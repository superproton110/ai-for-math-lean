
import Mathlib
import Aesop
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open scoped BigOperators
open Finset

abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable def DistSet (P : Finset Point) : Finset ℝ :=
  (P.offDiag.image (fun pq => dist pq.1 pq.2))
noncomputable def distSym2 (z : Sym2 Point) : ℝ :=
  Sym2.lift ⟨fun a b => dist a b, by
    intro a b
    simp [dist_comm]⟩ z
noncomputable def f (P : Finset Point) (u : ℝ) : ℕ :=
  ((P.sym2.filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)).card)
noncomputable def S (P : Finset Point) : ℝ :=
  ∑ u ∈ DistSet P, ((f P u : ℝ)^2)
def NoThreeCollinear (P : Finset Point) : Prop :=
  ∀ ⦃x y z : Point⦄, x ∈ P → y ∈ P → z ∈ P →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set Point)
def ConvexPosition (P : Finset Point) : Prop :=
  (P : Set Point) ⊆ (convexHull ℝ (P : Set Point)).extremePoints ℝ

namespace depth_0_lemma_1

theorem round1_h_ineq1 (P : Finset Point):
  ∀ (g : Point → ℝ), (∑ x ∈ P, g x)^2 ≤ (P.card : ℝ) * (∑ x ∈ P, (g x)^2)  := by
  intro g
  have h_main : (∑ x ∈ P, g x * (1 : ℝ)) ^ 2 ≤ (∑ x ∈ P, (g x) ^ 2) * (∑ x ∈ P, (1 : ℝ) ^ 2) := by
    exact Finset.sum_mul_sq_le_sq_mul_sq P g (fun (_ : Point) => (1 : ℝ))
  have h1 : (∑ x ∈ P, g x * (1 : ℝ)) = (∑ x ∈ P, g x) := by
    simp
  have h2 : (∑ x ∈ P, (1 : ℝ) ^ 2) = (P.card : ℝ) := by
    simp [Finset.sum_const]
    <;> ring
  rw [h1, h2] at h_main
  have h_final : (∑ x ∈ P, g x)^2 ≤ (P.card : ℝ) * (∑ x ∈ P, (g x)^2) := by
    have h_comm : (∑ x ∈ P, (g x)^2) * (P.card : ℝ) = (P.card : ℝ) * (∑ x ∈ P, (g x)^2) := by
      exact mul_comm _ _
    rw [h_comm] at h_main
    exact h_main
  exact h_final
end depth_0_lemma_1

namespace depth_0_lemma_2

lemma round1_h2 (P : Finset Point) (u : ℝ) (p : Point) (hp : p ∈ P) :
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  (S_ord.filter (fun pq : Point × Point => pq.1 = p)) =
  (P.filter (fun q => p ≠ q ∧ dist p q = u)).image (fun q : Point => (p, q)) := by
  dsimp only
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  apply Finset.ext
  intro x
  have h_main : x ∈ S_ord.filter (fun pq : Point × Point => pq.1 = p) ↔ x ∈ (P.filter (fun q => p ≠ q ∧ dist p q = u)).image (fun q : Point => (p, q)) := by
    constructor
    ·
      intro h
      have h1 : x ∈ S_ord := (Finset.mem_filter.mp h).1
      have h2 : x.1 = p := (Finset.mem_filter.mp h).2
      have h3 : x.1 ∈ P ∧ x.2 ∈ P := by
        have h4 : x ∈ P ×ˢ P := (Finset.mem_filter.mp h1).1
        simpa [Finset.mem_product] using h4
      have h4 : x.1 ≠ x.2 := ((Finset.mem_filter.mp h1).2).1
      have h5 : dist x.1 x.2 = u := ((Finset.mem_filter.mp h1).2).2
      have h6 : x.2 ∈ P := h3.2
      have h7 : p ≠ x.2 := by
        rw [h2] at h4 <;> tauto
      have h8 : dist p x.2 = u := by
        rw [h2] at h5 <;> tauto
      have h9 : x.2 ∈ P.filter (fun q => p ≠ q ∧ dist p q = u) := by
        simp only [Finset.mem_filter] <;> exact ⟨h6, ⟨h7, h8⟩⟩
      have h10 : x = (p, x.2) := by
        ext <;> simp [h2] <;> tauto
      rw [h10]
      apply Finset.mem_image.mpr
      refine ⟨x.2, h9, by simp⟩
    ·
      intro h
      have h1 : ∃ (q : Point), (q ∈ P.filter (fun q => p ≠ q ∧ dist p q = u)) ∧ ((p, q) = x) := by
        simpa [Finset.mem_image] using h
      rcases h1 with ⟨q, hq, h_eq⟩
      have hq1 : q ∈ P := (Finset.mem_filter.mp hq).1
      have hq2 : p ≠ q := (Finset.mem_filter.mp hq).2.1
      have hq3 : dist p q = u := (Finset.mem_filter.mp hq).2.2
      have h5 : (p, q) ∈ S_ord := by
        simp only [S_ord, Finset.mem_filter, Finset.mem_product]
        <;> exact ⟨⟨hp, hq1⟩, hq2, hq3⟩
      have h6 : (p, q).1 = p := by simp
      have h7 : (p, q) ∈ S_ord.filter (fun pq : Point × Point => pq.1 = p) := by
        apply Finset.mem_filter.mpr
        exact ⟨h5, h6⟩
      rw [←h_eq]
      exact h7
  exact h_main

lemma round1_h3 (P : Finset Point) (u : ℝ) :
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  (S_ord.card) = ∑ p ∈ P, (S_ord.filter (fun pq : Point × Point => pq.1 = p)).card := by
  dsimp only
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  let f : (Point × Point) → Point := fun pq => pq.1
  have h1 : S_ord.image f ⊆ P := by
    intro x hx
    simp only [f, S_ord, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hx
    rcases hx with ⟨a, ha, rfl⟩
    <;> tauto
  have h2 : S_ord.card = ∑ p ∈ S_ord.image f, (S_ord.filter (fun pq : Point × Point => pq.1 = p)).card := by
    exact?
  have h4 : ∀ p ∈ P, p ∉ S_ord.image f → (S_ord.filter (fun pq : Point × Point => pq.1 = p)) = ∅ := by
    intro p _ hnp
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx h_eq
    have h5 : x ∈ S_ord := hx
    have h6 : f x = p := by
      simpa [f] using h_eq
    have h7 : p ∈ S_ord.image f := by
      exact Finset.mem_image.mpr ⟨x, hx, h6⟩
    contradiction
  have h3 : ∑ p ∈ S_ord.image f, (S_ord.filter (fun pq : Point × Point => pq.1 = p)).card = ∑ p ∈ P, (S_ord.filter (fun pq : Point × Point => pq.1 = p)).card := by
    apply Finset.sum_subset h1
    intro p hp hnp
    have h6 : (S_ord.filter (fun pq : Point × Point => pq.1 = p)) = ∅ := h4 p hp hnp
    rw [h6]
    <;> simp
  rw [h2, h3]

lemma round1_h1 (P : Finset Point) (u : ℝ) :
  (∑ p ∈ P, ((P.filter (fun q => p ≠ q ∧ dist p q = u)).card : ℕ)) =
  (((P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)).card) := by
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  have h2 : ∀ p ∈ P, (S_ord.filter (fun pq : Point × Point => pq.1 = p)).card = (P.filter (fun q => p ≠ q ∧ dist p q = u)).card := by
    intro p hp
    have h21 := round1_h2 P u p hp
    rw [h21]
    have h_inj : Function.Injective (fun (q : Point) => (p, q)) := by
      intro q1 q2 h
      simpa using h
    have h_card : ((P.filter (fun q => p ≠ q ∧ dist p q = u)).image (fun q : Point => (p, q))).card = (P.filter (fun q => p ≠ q ∧ dist p q = u)).card := by
      rw [Finset.card_image_of_injective _ h_inj]
    exact h_card
  have h3 : S_ord.card = ∑ p ∈ P, (S_ord.filter (fun pq : Point × Point => pq.1 = p)).card :=
    round1_h3 P u
  have h4 : ∑ p ∈ P, (S_ord.filter (fun pq : Point × Point => pq.1 = p)).card = ∑ p ∈ P, ((P.filter (fun q => p ≠ q ∧ dist p q = u)).card : ℕ) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact_mod_cast h2 p hp
  rw [h4] at h3
  exact h3.symm

lemma round1_h2_aux (P : Finset Point) (u : ℝ) (z : Sym2 Point)
  (hz : z ∈ (P.sym2).filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)) :
  ∃ (pq : Point × Point), pq ∈ P.offDiag ∧ (Sym2.mk pq) = z := by
  have h1z : z ∈ P.sym2 := (Finset.mem_filter.mp hz).1
  have h2z1 : ¬Sym2.IsDiag z ∧ distSym2 z = u := (Finset.mem_filter.mp hz).2
  have h_P_sym2 : P.sym2 = (P ×ˢ P).image Sym2.mk := by exact?
  let F : Finset (Sym2 Point) := (P.sym2).filter (fun x => ¬Sym2.IsDiag x)
  have h1 : z ∈ F := by
    simp only [F, Finset.mem_filter] at *
    <;> tauto
  have h2 : F = {a ∈ (P ×ˢ P).image Sym2.mk | ¬a.IsDiag} := by
    dsimp only [F]
    have h_P_sym2' : P.sym2 = (P ×ˢ P).image Sym2.mk := h_P_sym2
    simpa [h_P_sym2'] using rfl
  have h3 : {a ∈ (P ×ˢ P).image Sym2.mk | ¬a.IsDiag} = (P.offDiag.image Sym2.mk) :=
    Sym2.filter_image_mk_not_isDiag P
  have h4 : F = (P.offDiag.image Sym2.mk) := by
    rw [h2, h3]
  rw [h4] at h1
  simpa [Finset.mem_image] using h1

lemma round1_h4 (P : Finset Point) (u : ℝ) :
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  let Z := (P.sym2).filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)
  S_ord.card = 2 * Z.card := by
  dsimp only
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  let Z := (P.sym2).filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)
  let h : (Point × Point) → Sym2 Point := fun pq => Sym2.mk pq
  let Im_h_S := S_ord.image h
  have h1 : ∀ (pq : Point × Point), pq ∈ S_ord → h pq ∈ Z := by
    intro pq hpq
    have h11 : pq ∈ P ×ˢ P := (Finset.mem_filter.mp hpq).1
    have h12 : pq.1 ≠ pq.2 := ((Finset.mem_filter.mp hpq).2).1
    have h13 : dist pq.1 pq.2 = u := ((Finset.mem_filter.mp hpq).2).2
    have h14 : pq.1 ∈ P := (Finset.mem_product.mp h11).1
    have h15 : pq.2 ∈ P := (Finset.mem_product.mp h11).2
    have h16 : ¬Sym2.IsDiag (h pq) := by
      simpa [h, Sym2.IsDiag, Sym2.mk] using h12
    have h17 : distSym2 (h pq) = u := by
      simpa [h, distSym2, Sym2.lift_mk] using h13
    have h18 : h pq ∈ P.sym2 := by
      have h_P_sym2 : P.sym2 = (P ×ˢ P).image Sym2.mk := by exact?
      rw [h_P_sym2]
      <;> apply Finset.mem_image.mpr
      <;> exact ⟨pq, h11, rfl⟩
    exact Finset.mem_filter.mpr ⟨h18, ⟨h16, h17⟩⟩
  have h_sub1 : Im_h_S ⊆ Z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    exact h1 x hx
  have h2 : ∀ (z : Sym2 Point), z ∈ Z → ∃ (pq : Point × Point), pq ∈ P.offDiag ∧ (Sym2.mk pq) = z :=
    round1_h2_aux P u
  have h_sub2 : Z ⊆ Im_h_S := by
    intro z hz
    have h3 : ∃ (pq : Point × Point), pq ∈ P.offDiag ∧ (Sym2.mk pq) = z := h2 z hz
    rcases h3 with ⟨pq, hpq_offdiag, hpq_eq⟩
    have hp : pq.1 ∈ P := (Finset.mem_offDiag.mp hpq_offdiag).1
    have hq : pq.2 ∈ P := (Finset.mem_offDiag.mp hpq_offdiag).2.1
    have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp hpq_offdiag).2.2
    have h_in_prod : pq ∈ P ×ˢ P := by
      exact Finset.mem_product.mpr ⟨hp, hq⟩
    have h8 : dist pq.1 pq.2 = u := by
      have h9 : distSym2 z = u := (Finset.mem_filter.mp hz).2.2
      have h10 : Sym2.mk pq = z := hpq_eq
      have h11 : distSym2 (Sym2.mk pq) = u := by
        rw [h10] <;> exact h9
      simpa [distSym2, Sym2.lift_mk] using h11
    have h11 : pq ∈ S_ord := by
      exact Finset.mem_filter.mpr ⟨h_in_prod, ⟨hne, h8⟩⟩
    have h12 : h pq = z := by
      have h13 : h pq = Sym2.mk pq := by rfl
      rw [h13, hpq_eq]
    have h14 : z ∈ Im_h_S := by
      apply Finset.mem_image.mpr
      exact ⟨pq, h11, h12⟩
    exact h14
  have h_eq : Im_h_S = Z := by
    apply Finset.Subset.antisymm h_sub1 h_sub2
  have h_main : ∀ (z : Sym2 Point), z ∈ Z → (S_ord.filter (fun pq : Point × Point => h pq = z)).card = 2 := by
    intro z hz
    have h2z : ¬Sym2.IsDiag z ∧ distSym2 z = u := (Finset.mem_filter.mp hz).2
    have h4 : ∃ (pq : Point × Point), pq ∈ P.offDiag ∧ (Sym2.mk pq) = z := h2 z hz
    rcases h4 with ⟨pq, hpq_offdiag, hpq_eq⟩
    let p := pq.1
    let q := pq.2
    have hp : pq.1 ∈ P := (Finset.mem_offDiag.mp hpq_offdiag).1
    have hq : pq.2 ∈ P := (Finset.mem_offDiag.mp hpq_offdiag).2.1
    have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp hpq_offdiag).2.2
    have h14 : (p, q) ∈ S_ord := by
      have h_in_prod : (p, q) ∈ P ×ˢ P := by
        exact Finset.mem_product.mpr ⟨hp, hq⟩
      have hdist : dist pq.1 pq.2 = u := by
        have h9 : distSym2 z = u := h2z.2
        have h10 : Sym2.mk pq = z := hpq_eq
        have h11 : distSym2 (Sym2.mk pq) = u := by
          rw [h10] <;> exact h9
        simpa [distSym2, Sym2.lift_mk] using h11
      exact Finset.mem_filter.mpr ⟨h_in_prod, ⟨hne, hdist⟩⟩
    have h17 : (q, p) ∈ S_ord := by
      have h_in_prod2 : (q, p) ∈ P ×ˢ P := by
        exact Finset.mem_product.mpr ⟨hq, hp⟩
      have hdist2 : dist pq.1 pq.2 = u := by
        have h9 : distSym2 z = u := h2z.2
        have h10 : Sym2.mk pq = z := hpq_eq
        have h11 : distSym2 (Sym2.mk pq) = u := by
          rw [h10] <;> exact h9
        simpa [distSym2, Sym2.lift_mk] using h11
      exact Finset.mem_filter.mpr ⟨h_in_prod2, ⟨Ne.symm hne, by simpa [dist_comm] using hdist2⟩⟩
    have h18 : h (p, q) = Sym2.mk (p, q) := by rfl
    have h19 : h (q, p) = Sym2.mk (q, p) := by rfl
    have h20 : Sym2.mk (q, p) = Sym2.mk (p, q) := by
      simp [Sym2.mk]
      <;> aesop
    have h21 : h (q, p) = h (p, q) := by
      rw [h19, h20, h18]
    have h22 : (p, q) ≠ (q, p) := by
      intro h23 <;> simp [Prod.ext_iff] at h23 <;> tauto
    have h24 : S_ord.filter (fun pq : Point × Point => h pq = z) = {(p, q), (q, p)} := by
      ext ⟨x1, x2⟩
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      <;> aesop
      <;> (try { tauto }) <;>
      (try {
        simp_all [h, Sym2.mk, Sym2.eq_iff]
        <;> tauto
      })
    rw [h24]
    <;> simp [h22] <;> decide
  have h_sum : S_ord.card = ∑ z ∈ Im_h_S, (S_ord.filter (fun pq : Point × Point => h pq = z)).card := by
    have h : S_ord.card = ∑ y ∈ S_ord.image h, (S_ord.filter (fun x : Point × Point => h x = y)).card := by exact?
    exact h
  rw [h_sum, h_eq]
  have h_final : ∑ z ∈ Z, (S_ord.filter (fun pq : Point × Point => h pq = z)).card = ∑ z ∈ Z, 2 := by
    apply Finset.sum_congr rfl
    intro z hz
    exact h_main z hz
  rw [h_final]
  have h_sum2 : ∑ z ∈ Z, (2 : ℕ) = Z.card * 2 := by
    simp [Finset.sum_const]
    <;> ring
  rw [h_sum2]
  <;> ring

theorem round1_h_ineq2 (P : Finset Point)
  (hconv : ConvexPosition P) (hnc : NoThreeCollinear P):
  ∀ u ∈ DistSet P, (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)) = 2 * (f P u : ℝ)  := by
  intro u hu
  dsimp only [f, DistSet]
  let S_ord := (P ×ˢ P).filter (fun pq : Point × Point => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = u)
  let Z := (P.sym2).filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)
  have h1 : (∑ p ∈ P, ((P.filter (fun q => p ≠ q ∧ dist p q = u)).card : ℕ)) = S_ord.card :=
    round1_h1 P u
  have h4 : S_ord.card = 2 * Z.card := round1_h4 P u
  have h1' : (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℕ)) = (∑ p ∈ P, ((P.filter (fun q => p ≠ q ∧ dist p q = u)).card : ℕ)) := by
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    <;> apply Finset.filter_congr
    <;> intros x _
    <;> tauto
  have h5 : (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)) = (S_ord.card : ℝ) := by
    have h51 : (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℕ)) = S_ord.card := by
      rw [h1'] <;> exact h1
    exact_mod_cast h51
  have h6 : (S_ord.card : ℝ) = 2 * (Z.card : ℝ) := by exact_mod_cast h4
  have h7 : (Z.card : ℝ) = ((f P u : ℝ)) := by
    rfl
  have h8 : (S_ord.card : ℝ) = 2 * (f P u : ℝ) := by
    calc
      (S_ord.card : ℝ) = 2 * (Z.card : ℝ) := h6
      _ = 2 * ((f P u : ℝ)) := by rw [h7]
  calc
    (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ))
      = (S_ord.card : ℝ) := h5
    _ = 2 * (f P u : ℝ) := h8
end depth_0_lemma_2

namespace depth_0_lemma_3

namespace depth_1_lemma_1
abbrev Point := EuclideanSpace ℝ (Fin 2)
noncomputable def DistSet (P : Finset Point) : Finset ℝ :=
  (P.offDiag.image (fun pq => dist pq.1 pq.2))
noncomputable def distSym2 (z : Sym2 Point) : ℝ :=
  Sym2.lift ⟨fun a b => dist a b, by
    intro a b
    simp [dist_comm]⟩ z
noncomputable def f (P : Finset Point) (u : ℝ) : ℕ :=
  ((P.sym2.filter (fun z => ¬ Sym2.IsDiag z ∧ distSym2 z = u)).card)
noncomputable def S (P : Finset Point) : ℝ :=
  ∑ u ∈ DistSet P, ((f P u : ℝ)^2)
def NoThreeCollinear (P : Finset Point) : Prop :=
  ∀ ⦃x y z : Point⦄, x ∈ P → y ∈ P → z ∈ P →
    x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set Point)
def ConvexPosition (P : Finset Point) : Prop :=
  (P : Set Point) ⊆ (convexHull ℝ (P : Set Point)).extremePoints ℝ



lemma round1_h_exist_t (u₀ u₁ v₀ v₁ : ℝ) (h_ne : (u₀, u₁) ≠ (0, 0))
  (h_goal : v₀ * u₁ - v₁ * u₀ = 0) :
  ∃ (t : ℝ), v₀ = t * u₀ ∧ v₁ = t * u₁ := by
  by_cases h1 : u₀ ≠ 0
  ·
    use v₀ / u₀
    have h2 : v₀ = (v₀ / u₀) * u₀ := by
      field_simp [h1] <;> ring
    have h3 : v₁ = (v₀ / u₀) * u₁ := by
      have h4 : v₀ * u₁ - v₁ * u₀ = 0 := h_goal
      have h5 : v₀ * u₁ = v₁ * u₀ := by linarith
      field_simp [h1] at h5 ⊢ <;> linarith
    exact ⟨h2, h3⟩
  ·
    have h_u0 : u₀ = 0 := by simpa using h1
    have h_ne2 : u₁ ≠ 0 := by
      by_contra h
      have h' : u₁ = 0 := by simpa using h
      have h_contra : (u₀, u₁) = (0, 0) := by simp [h_u0, h'] <;> aesop
      exact h_ne h_contra
    use v₁ / u₁
    have h2 : v₀ * u₁ = 0 := by
      have h_goal' : v₀ * u₁ - v₁ * u₀ = 0 := h_goal
      rw [h_u0] at h_goal' <;> linarith
    have h3 : v₀ = 0 := by
      apply (mul_eq_zero.mp h2).resolve_right h_ne2
    constructor
    ·
      simp [h3, h_u0]
      <;> ring
    ·
      simp [h_ne2] <;> field_simp <;> linarith

lemma round1_h_dist_sq (p q : Point) :
  dist p q ^ 2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 := by
  have h₁ : dist p q ^ 2 = ∑ i : Fin 2, dist (p i) (q i) ^ 2 := by
    exact EuclideanSpace.dist_sq_eq p q
  rw [h₁]
  have h₂ : (∑ i : Fin 2, dist (p i) (q i) ^ 2) = dist (p 0) (q 0) ^ 2 + dist (p 1) (q 1) ^ 2 := by
    simp [Fin.sum_univ_two]
    <;> ring
  rw [h₂]
  have h₃ : ∀ (x y : ℝ), dist x y ^ 2 = (x - y)^2 := by
    intro x y
    simp [Real.dist_eq]
    <;> ring
  have h4_0 := h₃ (p 0) (q 0)
  have h4_1 := h₃ (p 1) (q 1)
  rw [h4_0, h4_1]
  <;> ring

lemma round1_h_main_geom (q r p₁ p₂ p₃ : Point) (hqr : q ≠ r)
  (h1 : dist p₁ q = dist p₁ r)
  (h2 : dist p₂ q = dist p₂ r)
  (h3 : dist p₃ q = dist p₃ r)
  (h_p1_ne_p2 : p₁ ≠ p₂) (h_p1_ne_p3 : p₁ ≠ p₃) (h_p2_ne_p3 : p₂ ≠ p₃):
  Collinear ℝ ({p₁, p₂, p₃} : Set Point) := by
  let a : ℝ := r 0 - q 0
  let b : ℝ := r 1 - q 1
  let c : ℝ := (q 0)^2 + (q 1)^2 - (r 0)^2 - (r 1)^2
  have h_nz : (a, b) ≠ (0, 0) := by
    intro h
    have hq0 : r 0 - q 0 = 0 := by simpa using congr_arg Prod.fst h
    have hq1 : r 1 - q 1 = 0 := by simpa using congr_arg Prod.snd h
    have hq0' : r 0 = q 0 := by linarith
    have hq1' : r 1 = q 1 := by linarith
    have h_eq : r = q := by
      ext i
      fin_cases i <;> simp [hq0', hq1'] <;> tauto
    have h_contra : q = r := by exact h_eq.symm
    exact hqr h_contra
  have h_eq1 : ∀ (p : Point), dist p q ^ 2 = dist p r ^ 2 → 2 * (p 0) * a + 2 * (p 1) * b = -c := by
    intro p h
    have h₂ : dist p q ^ 2 = dist p r ^ 2 := h
    have h₃ : (p 0 - q 0)^2 + (p 1 - q 1)^2 = (p 0 - r 0)^2 + (p 1 - r 1)^2 := by
      have h₄ : dist p q ^ 2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 := round1_h_dist_sq p q
      have h₅ : dist p r ^ 2 = (p 0 - r 0)^2 + (p 1 - r 1)^2 := round1_h_dist_sq p r
      rw [h₄, h₅] at h₂
      exact h₂
    linarith
  have h1' : 2 * (p₁ 0) * a + 2 * (p₁ 1) * b = -c := h_eq1 p₁ (by rw [h1])
  have h2' : 2 * (p₂ 0) * a + 2 * (p₂ 1) * b = -c := h_eq1 p₂ (by rw [h2])
  have h3' : 2 * (p₃ 0) * a + 2 * (p₃ 1) * b = -c := h_eq1 p₃ (by rw [h3])
  have h4 : (p₂ 0 - p₁ 0) * a + (p₂ 1 - p₁ 1) * b = 0 := by linarith
  have h5 : (p₃ 0 - p₁ 0) * a + (p₃ 1 - p₁ 1) * b = 0 := by linarith
  let u₀ := p₂ 0 - p₁ 0
  let u₁ := p₂ 1 - p₁ 1
  let v₀ := p₃ 0 - p₁ 0
  let v₁ := p₃ 1 - p₁ 1
  have h_u_ne_zero : (u₀, u₁) ≠ (0, 0) := by
    intro h
    have h₁ : u₀ = 0 := by simpa [Prod.mk.injEq] using congr_arg Prod.fst h
    have h₂ : u₁ = 0 := by simpa [Prod.mk.injEq] using congr_arg Prod.snd h
    have hp20 : p₂ 0 = p₁ 0 := by
      dsimp only [u₀] at h₁ <;> linarith
    have hp21 : p₂ 1 = p₁ 1 := by
      dsimp only [u₁] at h₂ <;> linarith
    have h_eq : p₂ = p₁ := by
      ext i
      fin_cases i <;> simp [hp20, hp21] <;> tauto
    exact h_p1_ne_p2 (h_eq.symm)
  have h_goal : v₀ * u₁ - v₁ * u₀ = 0 := by
    have h_eqA : a * (v₀ * u₁ - v₁ * u₀) = 0 := by
      have h : (u₀ * a + u₁ * b) * v₁ - (v₀ * a + v₁ * b) * u₁ = 0 := by
        rw [h4, h5] <;> ring
      linarith
    have h_eqB : b * (v₀ * u₁ - v₁ * u₀) = 0 := by
      have h : (u₀ * a + u₁ * b) * v₀ - (v₀ * a + v₁ * b) * u₀ = 0 := by
        rw [h4, h5] <;> ring
      linarith
    have hX : (v₀ * u₁ - v₁ * u₀) = 0 := by
      by_cases ha : a ≠ 0
      · exact (mul_eq_zero.mp h_eqA).resolve_left ha
      · have hb : b ≠ 0 := by
          by_contra h
          have h' : a = 0 ∧ b = 0 := ⟨by simpa using ha, by simpa using h⟩
          have h'' : (a, b) = (0, 0) := by simp [h'] <;> aesop
          exact h_nz h''
        exact (mul_eq_zero.mp h_eqB).resolve_left hb
    exact hX
  have h_exist_t : ∃ (t : ℝ), v₀ = t * u₀ ∧ v₁ = t * u₁ := round1_h_exist_t u₀ u₁ v₀ v₁ h_u_ne_zero h_goal
  rcases h_exist_t with ⟨t, ht⟩
  have h9 : p₃ - p₁ = t • (p₂ - p₁) := by
    ext i
    fin_cases i <;> simp [ht, u₀, u₁, v₀, v₁] <;> tauto
  have h10 : p₃ ∈ line[ℝ, p₁, p₂] := by
    have h11 : p₃ = t • (p₂ - p₁) + p₁ := by
      have h12 : p₃ - p₁ = t • (p₂ - p₁) := h9
      have h13 : p₃ = p₁ + (t • (p₂ - p₁)) := by
        calc
          p₃ = p₁ + (p₃ - p₁) := by abel
          _ = p₁ + (t • (p₂ - p₁)) := by rw [h12]
      simpa [add_comm] using h13
    rw [h11]
    exact smul_vsub_vadd_mem_affineSpan_pair t p₁ p₂
  have h_p1_in_span : p₁ ∈ affineSpan ℝ ({p₁, p₂} : Set Point) := by
    have h : p₁ ∈ ({p₁, p₂} : Set Point) := by simp
    have h' : ({p₁, p₂} : Set Point) ⊆ affineSpan ℝ ({p₁, p₂} : Set Point) := subset_affineSpan ℝ ({p₁, p₂} : Set Point)
    exact h' h
  have h_p2_in_span : p₂ ∈ affineSpan ℝ ({p₁, p₂} : Set Point) := by
    have h : p₂ ∈ ({p₁, p₂} : Set Point) := by simp
    have h' : ({p₁, p₂} : Set Point) ⊆ affineSpan ℝ ({p₁, p₂} : Set Point) := subset_affineSpan ℝ ({p₁, p₂} : Set Point)
    exact h' h
  have h11 : line[ℝ, p₁, p₂] = affineSpan ℝ ({p₁, p₂} : Set Point) := by
    exact?
  have h12 : p₃ ∈ affineSpan ℝ ({p₁, p₂} : Set Point) := by
    rw [←h11]
    exact h10
  have h_main : Collinear ℝ ({p₁, p₂, p₃} : Set Point) := by
    apply collinear_triple_of_mem_affineSpan_pair h_p1_in_span h_p2_in_span h12
  exact h_main

lemma round1_exists_three_distinct {α : Type _} [DecidableEq α] (s : Finset α) (h : s.card ≥ 3) :
  ∃ (x y z : α), x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have h₁ : s.card ≥ 3 := h
  have h₂ : ∃ (x : α), x ∈ s := Finset.card_pos.mp (by linarith)
  rcases h₂ with ⟨x, hx⟩
  have h₃ : (s.erase x).card ≥ 2 := by
    have h₄ : (s.erase x).card = s.card - 1 := by
      rw [Finset.card_erase_of_mem hx]
      <;> simp
    rw [h₄]
    omega
  have h₅ : ∃ (y : α), y ∈ s.erase x := Finset.card_pos.mp (by linarith)
  rcases h₅ with ⟨y, hy⟩
  have hy₁ : y ∈ s := (Finset.mem_erase.mp hy).2
  have hy₂ : y ≠ x := (Finset.mem_erase.mp hy).1
  have h₆ : ((s.erase x).erase y).card ≥ 1 := by
    have h₇ : ((s.erase x).erase y).card = (s.erase x).card - 1 := by
      rw [Finset.card_erase_of_mem hy] <;> simp
    rw [h₇]
    <;> omega
  have h₇ : ∃ (z : α), z ∈ (s.erase x).erase y := Finset.card_pos.mp h₆
  rcases h₇ with ⟨z, hz⟩
  have hz₁ : z ∈ s := by
    have hz₂ : z ∈ (s.erase x).erase y := hz
    have hz₃ : z ∈ s.erase x := Finset.mem_of_mem_erase hz₂
    have hz₄ : z ∈ s := Finset.mem_of_mem_erase hz₃
    exact hz₄
  have hz₅ : z ≠ x := by
    have hz₆ : z ∈ (s.erase x).erase y := hz
    have hz₇ : z ∈ s.erase x := Finset.mem_of_mem_erase hz₆
    have hz₈ : z ≠ x := (Finset.mem_erase.mp hz₇).1
    exact hz₈
  have hz₆ : z ≠ y := by
    have hz₇ : z ∈ (s.erase x).erase y := hz
    have hz₈ : z ≠ y := (Finset.mem_erase.mp hz₇).1
    exact hz₈
  refine' ⟨x, y, z, hx, hy₁, hz₁, hy₂.symm, hz₅.symm, hz₆.symm⟩

theorem round1_h1 (P : Finset Point)
  (hnc : NoThreeCollinear P):
  ∀ (q r : Point), q ∈ P → r ∈ P → q ≠ r → (P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card ≤ 2  := by
  intro q r hq hr hqr
  let S := P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)
  by_contra h
  have h₁ : S.card > 2 := by
    simpa using h
  have h₂ : S.card ≥ 3 := by linarith
  have h₃ : ∃ (p₁ p₂ p₃ : Point), p₁ ∈ S ∧ p₂ ∈ S ∧ p₃ ∈ S ∧ p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ :=
    round1_exists_three_distinct S h₂
  rcases h₃ with ⟨p₁, p₂, p₃, hp₁, hp₂, hp₃, hne12, hne13, hne23⟩
  have h_p₁_in_P : p₁ ∈ P := Finset.mem_filter.mp hp₁ |>.1
  have h_p₂_in_P : p₂ ∈ P := Finset.mem_filter.mp hp₂ |>.1
  have h_p₃_in_P : p₃ ∈ P := Finset.mem_filter.mp hp₃ |>.1
  have h₁' : p₁ ≠ q ∧ p₁ ≠ r ∧ dist p₁ q = dist p₁ r := (Finset.mem_filter.mp hp₁).2
  have h₂' : p₂ ≠ q ∧ p₂ ≠ r ∧ dist p₂ q = dist p₂ r := (Finset.mem_filter.mp hp₂).2
  have h₃' : p₃ ≠ q ∧ p₃ ≠ r ∧ dist p₃ q = dist p₃ r := (Finset.mem_filter.mp hp₃).2
  have h_main : Collinear ℝ ({p₁, p₂, p₃} : Set Point) :=
    round1_h_main_geom q r p₁ p₂ p₃ hqr h₁'.2.2 h₂'.2.2 h₃'.2.2 hne12 hne13 hne23
  have h_contra : ¬ Collinear ℝ ({p₁, p₂, p₃} : Set Point) := hnc h_p₁_in_P h_p₂_in_P h_p₃_in_P hne12 hne23 hne13
  exact h_contra h_main
end depth_1_lemma_1

namespace depth_1_lemma_2

lemma round1_h_general (β γ : Type*) [DecidableEq β] [DecidableEq γ] (X : Finset β) (f : β → γ) :
  (∑ y ∈ X.image f, ((X.filter (fun x => f x = y)).card : ℕ)^2) = ((X ×ˢ X).filter (fun z : β × β => f z.1 = f z.2)).card := by
  let S := (X ×ˢ X).filter (fun z : β × β => f z.1 = f z.2)
  let S_y (y : γ) := (X.filter (fun x => f x = y)) ×ˢ (X.filter (fun x => f x = y))
  have h1 : ∀ (y1 y2 : γ), y1 ∈ X.image f → y2 ∈ X.image f → y1 ≠ y2 → Disjoint (S_y y1) (S_y y2) := by
    intro y1 y2 hy1 hy2 hne
    apply Finset.disjoint_left.mpr
    intro z hz1 hz2
    rcases z with ⟨a, b⟩
    have h41 : (a, b) ∈ S_y y1 := hz1
    have h42 : (a, b) ∈ S_y y2 := hz2
    have h_a1 : a ∈ X.filter (fun x => f x = y1) := by
      simp only [S_y, Finset.mem_product] at h41 <;> tauto
    have h_a2 : a ∈ X.filter (fun x => f x = y2) := by
      simp only [S_y, Finset.mem_product] at h42 <;> tauto
    have h_eq1 : f a = y1 := (Finset.mem_filter.mp h_a1).2
    have h_eq2 : f a = y2 := (Finset.mem_filter.mp h_a2).2
    have h_contra : y1 = y2 := by
      calc
        y1 = f a := h_eq1.symm
        _ = y2 := h_eq2
    contradiction
  have h1' : Set.PairwiseDisjoint (X.image f : Set γ) (fun y => S_y y) := by
    intro y1 hy1 y2 hy2 hne
    exact h1 y1 y2 hy1 hy2 hne
  have h2 : S = Finset.biUnion (X.image f) S_y := by
    ext z
    simp only [S, S_y, Finset.mem_filter, Finset.mem_image, Finset.mem_biUnion, Finset.mem_product] at *
    <;> aesop
  have h3 : S.card = (Finset.biUnion (X.image f) S_y).card := by rw [h2]
  have h4 : (Finset.biUnion (X.image f) S_y).card = ∑ y ∈ X.image f, (S_y y).card := by
    rw [Finset.card_biUnion h1']
  have h_main : ∑ y ∈ X.image f, ((X.filter (fun x => f x = y)).card : ℕ)^2 = ∑ y ∈ X.image f, (S_y y).card := by
    apply Finset.sum_congr rfl
    intro y hy
    have h5 : (S_y y).card = ((X.filter (fun x => f x = y)).card : ℕ)^2 := by
      simp [S_y, Finset.card_product]
      <;> ring
    exact h5.symm
  rw [h3, h4, h_main]

lemma round1_h_main2 (P : Finset Point) (p : Point) (hp : p ∈ P) :
  let T := (P ×ˢ P).filter (fun (z : Point × Point) => z.1 ≠ p ∧ z.2 ≠ p ∧ dist p z.1 = dist p z.2)
  (T.card : ℝ) = (∑ q ∈ P, ∑ r ∈ P, if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0) := by
  let T := (P ×ˢ P).filter (fun (z : Point × Point) => z.1 ≠ p ∧ z.2 ≠ p ∧ dist p z.1 = dist p z.2)
  let P' (z : Point × Point) : Prop := (z.1 ≠ p ∧ z.2 ≠ p ∧ dist p z.1 = dist p z.2)
  have h_sum : (∑ z ∈ (P ×ˢ P), (if P' z then (1 : ℝ) else 0)) = T.card := by
    have hT : T = (P ×ˢ P).filter P' := by
      rfl
    rw [hT]
    have h : ∑ z ∈ ( (P ×ˢ P).filter P' ), (1 : ℝ) = ((P ×ˢ P).filter P').card := by
      norm_cast
      <;> simp
    simpa [Finset.sum_ite] using h.symm
  have h_final : (∑ z ∈ (P ×ˢ P), (if P' z then (1 : ℝ) else 0)) = (∑ q ∈ P, ∑ r ∈ P, if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0) := by
    rw [Finset.sum_product]
    <;> simp [Finset.sum_ite]
    <;> aesop
  have h_main : (T.card : ℝ) = ∑ z ∈ (P ×ˢ P), (if P' z then (1 : ℝ) else 0) := by
    exact_mod_cast h_sum.symm
  exact_mod_cast h_main.trans h_final

lemma round1_h_step1 (P : Finset Point):
  ∀ (p : Point), p ∈ P →
    (∑ u ∈ (P.filter (fun x => x ≠ p)).image (fun q : Point => dist p q),
      ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)
    = (∑ q ∈ P, ∑ r ∈ P, if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0) := by
  intro p hp
  let A := P.filter (fun x : Point => x ≠ p)
  let f : Point → ℝ := fun (q : Point) => dist p q
  let S := (A ×ˢ A).filter (fun (z : Point × Point) => f z.1 = f z.2)
  let T := (P ×ˢ P).filter (fun (z : Point × Point) => z.1 ≠ p ∧ z.2 ≠ p ∧ dist p z.1 = dist p z.2)
  have h_eq : ∀ (x : Point × Point), x ∈ S ↔ x ∈ T := by
    intro x
    simp [A, f, S, T, Finset.mem_filter, Finset.mem_product]
    <;> aesop
  have h_S_eq_T : S = T := by
    ext x
    exact h_eq x
  have h_main1 : (∑ y ∈ A.image f, ((A.filter (fun x => f x = y)).card : ℕ)^2) = S.card := by
    exact_mod_cast round1_h_general (Point) (ℝ) A f
  have h_main2 : (T.card : ℝ) = (∑ q ∈ P, ∑ r ∈ P, if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0) :=
    round1_h_main2 P p hp
  have h4 : (S.card : ℝ) = (T.card : ℝ) := by
    congr
    <;> exact h_S_eq_T
  have h5 : ((∑ y ∈ A.image f, ((A.filter (fun x => f x = y)).card : ℕ)^2) : ℝ) = (S.card : ℝ) := by
    exact_mod_cast h_main1
  have h6 : ((∑ y ∈ A.image f, ((A.filter (fun x => f x = y)).card : ℕ)^2) : ℝ) = (T.card : ℝ) := by
    calc
      ((∑ y ∈ A.image f, ((A.filter (fun x => f x = y)).card : ℕ)^2) : ℝ) = (S.card : ℝ) := h5
      _ = (T.card : ℝ) := h4
  have h7 : ((∑ y ∈ A.image f, ((A.filter (fun x => f x = y)).card : ℝ)^2)) = (T.card : ℝ) := by
    norm_cast at h6 ⊢ <;> simpa using h6
  have h9 : A.image f = (P.filter (fun x => x ≠ p)).image (fun q : Point => dist p q) := by
    rfl
  have h11 : ∀ (y : ℝ), (P.filter (fun q : Point => q ≠ p ∧ dist p q = y)).card = (A.filter (fun x : Point => f x = y)).card := by
    intro y
    have h12 : (P.filter (fun q : Point => q ≠ p ∧ dist p q = y)) = (A.filter (fun x : Point => f x = y)) := by
      ext x
      simp only [A, f, Finset.mem_filter, Finset.mem_image]
      <;> constructor <;> intro h
      ·
        rcases h with ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      ·
        rcases h with ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [h12]
  have h10 : ((∑ u ∈ (P.filter (fun x => x ≠ p)).image (fun q : Point => dist p q), ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)) =
    ((∑ y ∈ A.image f, ((A.filter (fun x => f x = y)).card : ℝ)^2)) := by
    have h13 : (P.filter (fun x => x ≠ p)).image (fun q : Point => dist p q) = A.image f := by
      exact h9
    rw [h13]
    apply Finset.sum_congr rfl
    intro y _
    have h14 : ((P.filter (fun q : Point => q ≠ p ∧ dist p q = y)).card : ℝ) = ((A.filter (fun x : Point => f x = y)).card : ℝ) := by
      exact_mod_cast h11 y
    rw [h14]
    <;> ring
  rw [h10]
  rw [h7]
  exact h_main2

lemma round1_h_step1' (P : Finset Point) (p : Point) (hp : p ∈ P) :
  (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)
  = (∑ u ∈ (P.filter (fun x : Point => x ≠ p)).image (fun q : Point => dist p q), ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2) := by
  let S₁ := (P.filter (fun x : Point => x ≠ p)).image (fun q : Point => dist p q)
  have h₁ : ∀ u : ℝ, u ∉ S₁ → ((P.filter (fun q : Point => q ≠ p ∧ dist p q = u)).card : ℝ)^2 = 0 := by
    intro u hu
    have h₂ : (P.filter (fun q : Point => q ≠ p ∧ dist p q = u)) = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro x hx
      have hx' : x ∈ P.filter (fun q : Point => q ≠ p ∧ dist p q = u) := hx
      have h_memP : x ∈ P := (Finset.mem_filter.mp hx').1
      have h_cond : x ≠ p ∧ dist p x = u := (Finset.mem_filter.mp hx').2
      have h_x_ne_p : x ≠ p := h_cond.1
      have h_dist : dist p x = u := h_cond.2
      have h₃ : u ∈ S₁ := by
        apply Finset.mem_image.mpr
        refine ⟨x, ?_, by simpa [h_dist] using rfl⟩
        simp only [S₁, Finset.mem_filter] <;> exact ⟨h_memP, h_x_ne_p⟩
      exact hu h₃
    rw [h₂]
    <;> simp
  have h_subset : S₁ ⊆ DistSet P := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, h_eq⟩
    have hy₁ : y ∈ P.filter (fun x : Point => x ≠ p) := hy
    have hy₂ : y ∈ P := (Finset.mem_filter.mp hy₁).1
    have hy₃ : y ≠ p := (Finset.mem_filter.mp hy₁).2
    have h₄ : (p, y) ∈ P.offDiag := by
      simp [Finset.mem_offDiag, hy₂, hy₃] <;> tauto
    have h₅ : x ∈ DistSet P := by
      unfold DistSet
      apply Finset.mem_image.mpr
      refine ⟨(p, y), h₄, by
        simpa [h_eq] using rfl⟩
    exact h₅
  have h₃ : (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2) =
    (∑ u ∈ S₁, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2) := by
    rw [← Finset.sum_subset h_subset]
    <;> intro u _ h₄
    <;> exact h₁ u h₄
  exact h₃

lemma round1_h_step1_final (P : Finset Point) (p : Point) (hp : p ∈ P) :
  (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)
  = (∑ q ∈ P, ∑ r ∈ P, if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0) := by
  have h₁ := round1_h_step1' P p hp
  have h₂ := round1_h_step1 P p hp
  rw [h₁]
  exact h₂

lemma round2_h_sum_p (P : Finset Point) (q r : Point) (hq : q ∈ P) (hr : r ∈ P) :
  (∑ p ∈ P, (if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0))
  = if q = r then ((P.card : ℝ) - 1) else ((P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) := by
  by_cases h : q = r
  ·
    subst h
    have h2 : ∀ (p : Point), (q ≠ p ∧ q ≠ p ∧ dist p q = dist p q) ↔ (p ≠ q) := by
      intro p
      constructor
      · rintro ⟨h1, _, _⟩
        exact Ne.symm h1
      · intro h
        have h' : q ≠ p := Ne.symm h
        exact ⟨h', h', by rfl⟩
    have h1 : (∑ p ∈ P, (if (q ≠ p ∧ q ≠ p ∧ dist p q = dist p q) then (1 : ℝ) else 0))
      = ∑ p ∈ P, (if p ≠ q then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      have h2' : (q ≠ p ∧ q ≠ p ∧ dist p q = dist p q) ↔ (p ≠ q) := h2 p
      split_ifs <;> tauto
    have h3 : (∑ p ∈ P, (if p ≠ q then (1 : ℝ) else 0)) = ((P.filter (fun p : Point => p ≠ q)).card : ℝ) := by
      rw [Finset.sum_ite]
      <;> simp
    have h4 : (P.filter (fun p : Point => p ≠ q ∧ p ≠ q ∧ dist p q = dist p q)) = P.filter (fun p : Point => p ≠ q) := by
      ext x
      simp [Finset.mem_filter]
      <;> tauto
    have h5 : P.card > 0 := by
      exact Finset.card_pos.mpr (⟨q, hq⟩)
    have hc : ((P.filter (fun p : Point => p ≠ q)).card : ℝ) = ((P.card : ℝ) - 1) := by
      have h41 : (P.filter (fun p : Point => p ≠ q)) = P.erase q := by
        ext x
        simp [Finset.mem_filter]
        <;> tauto
      rw [h41]
      rw [Finset.card_erase_of_mem hq]
      <;> simp [h5]
      <;> norm_cast
    have h_main : (∑ p ∈ P, (if (q ≠ p ∧ q ≠ p ∧ dist p q = dist p q) then (1 : ℝ) else 0)) = ((P.card : ℝ) - 1) := by
      rw [h1, h3, hc]
    rw [h_main]
    <;> simp
  ·
    have h' : q ≠ r := h
    have h2 : ∀ (p : Point), (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) ↔ (p ≠ q ∧ p ≠ r ∧ dist p q = dist p r) := by
      intro p
      <;> simp [ne_comm] <;> tauto
    have h1 : (∑ p ∈ P, (if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0))
      = ((P.filter (fun p : Point => q ≠ p ∧ r ≠ p ∧ dist p q = dist p r)).card : ℝ) := by
      rw [Finset.sum_ite]
      <;> simp
    have h_eq : P.filter (fun p : Point => q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) = P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter]
      <;> aesop <;> tauto
    rw [h1, h_eq]
    <;> rw [if_neg h']

lemma h_sum_filter (P : Finset Point) (q : Point) (c : Point → Point → ℝ) :
  ∑ r ∈ P, (if q ≠ r then c q r else 0) = ∑ r ∈ P.filter (fun x => x ≠ q), c q r := by
  let t := P.filter (fun x => x ≠ q)
  have h1 : ∀ (r : Point), r ∈ P → (if q ≠ r then c q r else (0 : ℝ)) = (if r ∈ t then c q r else (0 : ℝ)) := by
    intro r hr
    simp only [t, Finset.mem_filter] at *
    <;> by_cases hqr : q ≠ r <;> simp [hqr, hr] <;> tauto
  have h2 : ∑ r ∈ P, (if q ≠ r then c q r else (0 : ℝ)) = ∑ r ∈ P, (if r ∈ t then c q r else (0 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact h1 r hr
  rw [h2]
  let g : Point → ℝ := fun r => if r ∈ t then c q r else 0
  have hsub : t ⊆ P := Finset.filter_subset _ _
  have h3 : ∀ (r : Point), r ∈ (P \ t) → g r = 0 := by
    intro r hr
    have h4 : r ∈ P \ t := hr
    have h5 : r ∉ t := (Finset.mem_sdiff).mp h4 |>.2
    simp [g, h5]
    <;> tauto
  have h4 : ∑ r ∈ P, g r = ∑ r ∈ t, g r := by
    have h5 : P = t ∪ (P \ t) := by
      ext x
      simp [hsub]
      <;> tauto
    rw [h5]
    rw [Finset.sum_union (Finset.disjoint_sdiff)]
    have h6 : ∑ r ∈ (P \ t), g r = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      exact h3 r hr
    rw [h6, add_zero]
    <;> rfl
  have h5 : ∑ r ∈ t, g r = ∑ r ∈ t, c q r := by
    apply Finset.sum_congr rfl
    intro r hr
    have h6 : r ∈ t := hr
    simp [g, h6]
    <;> tauto
  rw [h4, h5]
  <;> rfl

lemma round2_h_sumqr (P : Finset Point) :
  (∑ q ∈ P, ∑ r ∈ P,
    (if q = r then ((P.card : ℝ) - 1)
     else ((P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ)))
   = (P.card : ℝ) * ((P.card : ℝ) - 1)
   + (∑ q ∈ P, ∑ r ∈ P, if q ≠ r then ((P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) := by
  let c (q r : Point) : ℝ := ((P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ)
  let C (q r : Point) : ℝ := if q = r then ((P.card : ℝ) - 1) else c q r
  have h_inner : ∀ (q : Point), q ∈ P → ∑ r ∈ P, (if q ≠ r then c q r else 0) = ∑ r ∈ P.filter (fun x => x ≠ q), c q r :=
    fun q hq => h_sum_filter P q c
  have h₁ : ∀ (q : Point), q ∈ P → ∑ r ∈ P, C q r = ((P.card : ℝ) - 1) + ∑ r ∈ P.filter (fun x => x ≠ q), c q r := by
    intro q hq
    have h₆ : ∑ r ∈ P, C q r = ∑ r ∈ P, (if q = r then ((P.card : ℝ) - 1) else c q r) := by rfl
    rw [h₆]
    let f : Point → ℝ := fun r => if q = r then ((P.card : ℝ) - 1) else c q r
    have hP : P = insert q (P.erase q) := by
      rw [Finset.insert_erase hq]
    have h₇₁ : ∑ r ∈ (insert q (P.erase q)), f r = f q + ∑ r ∈ P.erase q, f r := by
      rw [Finset.sum_insert (show q ∉ P.erase q by simp)]
      <;> ring
    have h₇₁' : ∑ r ∈ P, f r = f q + ∑ r ∈ P.erase q, f r := by
      have h_eq : P = insert q (P.erase q) := hP
      have h : ∑ r ∈ P, f r = ∑ r ∈ (insert q (P.erase q)), f r := by
        congr
      rw [h] at *
      exact h₇₁
    have h₇₂ : ∀ r ∈ P.erase q, f r = c q r := by
      intro r hr
      have h₇₃ : r ≠ q := by
        simpa [Finset.mem_erase] using (Finset.mem_erase.mp hr).1
      have h₇₄ : q ≠ r := h₇₃.symm
      simp [f, h₇₄]
      <;> rw [if_neg h₇₄]
    have h₇₄ : ∑ r ∈ P.erase q, f r = ∑ r ∈ P.erase q, c q r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact h₇₂ r hr
    have h₇₅ : f q = ((P.card : ℝ) - 1) := by
      simp [f]
      <;> norm_num
    have h₈ : P.erase q = P.filter (fun x => x ≠ q) := by
      ext x
      simp [Finset.mem_filter]
      <;> tauto
    have h_main_goal : ∑ r ∈ P, f r = ((P.card : ℝ) - 1) + ∑ r ∈ P.filter (fun x => x ≠ q), c q r := by
      calc
        ∑ r ∈ P, f r = f q + ∑ r ∈ P.erase q, f r := h₇₁'
        _ = f q + ∑ r ∈ P.erase q, c q r := by rw [h₇₄]
        _ = f q + ∑ r ∈ P.filter (fun x => x ≠ q), c q r := by rw [h₈]
        _ = ((P.card : ℝ) - 1) + ∑ r ∈ P.filter (fun x => x ≠ q), c q r := by rw [h₇₅]
    exact h_main_goal
  have h_main : ∑ q ∈ P, ∑ r ∈ P, C q r = (P.card : ℝ) * ((P.card : ℝ) - 1) + ∑ q ∈ P, ∑ r ∈ P, if q ≠ r then c q r else 0 := by
    have h₂ : ∑ q ∈ P, ∑ r ∈ P, C q r = ∑ q ∈ P, ( ((P.card : ℝ) - 1) + ∑ r ∈ P.filter (fun x => x ≠ q), c q r ) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact h₁ q hq
    rw [h₂]
    have h₃ : ∑ q ∈ P, ( ((P.card : ℝ) - 1) + ∑ r ∈ P.filter (fun x => x ≠ q), c q r )
        = (∑ q ∈ P, ((P.card : ℝ) - 1)) + ∑ q ∈ P, (∑ r ∈ P.filter (fun x => x ≠ q), c q r) := by
      rw [Finset.sum_add_distrib]
    rw [h₃]
    have h₄ : (∑ q ∈ P, ((P.card : ℝ) - 1)) = (P.card : ℝ) * ((P.card : ℝ) - 1) := by
      rw [Finset.sum_const]
      <;> ring
    rw [h₄]
    have h₅ : ∑ q ∈ P, (∑ r ∈ P.filter (fun x => x ≠ q), c q r) = ∑ q ∈ P, ∑ r ∈ P, if q ≠ r then c q r else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      have h₆ : ∑ r ∈ P.filter (fun x => x ≠ q), c q r = ∑ r ∈ P, (if q ≠ r then c q r else 0) := by
        exact (h_inner q hq).symm
      exact h₆
    rw [h₅]
    <;> ring
  simpa [c, C] using h_main

theorem round1_h2 (P : Finset Point)
  (hnc : NoThreeCollinear P):
  (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)) =
  (P.card : ℝ) * ((P.card : ℝ) - 1) + (∑ q ∈ P, ∑ r ∈ P, if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0)  := by
  have h_step1_final : ∀ (p : Point), p ∈ P →
    (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)
    = (∑ q ∈ P, ∑ r ∈ P, if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0) :=
    fun p hp => round1_h_step1_final P p hp
  have h_sum1 : (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)) =
    ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, (if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h_step1_final p hp
  rw [h_sum1]
  let F (p q r : Point) : ℝ := if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0
  have h_sum_comm : (∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, F p q r) = ∑ q ∈ P, ∑ r ∈ P, ∑ p ∈ P, F p q r := by
    have h1 : (∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, F p q r) = ∑ p ∈ P, ∑ q ∈ P, (∑ r ∈ P, F p q r) := by rfl
    rw [h1]
    have h2 : ∑ p ∈ P, ∑ q ∈ P, (∑ r ∈ P, F p q r) = ∑ q ∈ P, ∑ p ∈ P, (∑ r ∈ P, F p q r) := by
      rw [Finset.sum_comm]
    rw [h2]
    have h3 : ∑ q ∈ P, ∑ p ∈ P, (∑ r ∈ P, F p q r) = ∑ q ∈ P, ∑ r ∈ P, ∑ p ∈ P, F p q r := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_comm]
    rw [h3]
  rw [h_sum_comm]
  have h_sum2 : ∀ (q : Point), q ∈ P → ∀ (r : Point), r ∈ P →
    (∑ p ∈ P, (if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0))
    = if q = r then ((P.card : ℝ) - 1) else ((P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) :=
    fun q hq r hr => round2_h_sum_p P q r hq hr
  have h_sum3 : (∑ q ∈ P, ∑ r ∈ P, ∑ p ∈ P, (if (q ≠ p ∧ r ≠ p ∧ dist p q = dist p r) then (1 : ℝ) else 0))
    = ∑ q ∈ P, ∑ r ∈ P, (if q = r then ((P.card : ℝ) - 1) else ((P.filter (fun p : Point => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ)) := by
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    exact h_sum2 q hq r hr
  rw [h_sum3]
  exact round2_h_sumqr P
end depth_1_lemma_2

namespace depth_1_lemma_3

lemma round1_h_main1 (P : Finset Point)
  (h1 : ∀ (q r : Point), q ∈ P → r ∈ P → q ≠ r → (P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card ≤ 2):
  ∀ (q : Point), q ∈ P → ∀ (r : Point), r ∈ P → (if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) ≤ 2 := by
  intro q hq r hr
  by_cases hqr : q ≠ r
  ·
    have h₂ : (P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card ≤ 2 := h1 q r hq hr hqr
    simp [hqr, h₂]
    <;> exact_mod_cast h₂
  ·
    simp [hqr]
    <;> norm_num

lemma round1_h_sum_aux (P : Finset Point) (q : Point) (hq : q ∈ P) :
  ∑ r ∈ P, (if q ≠ r then (2 : ℝ) else 0) = 2 * ((P.card : ℝ) - 1) := by
  have h_ne : ∀ (r : Point), r ∈ P → (if q ≠ r then (2 : ℝ) else 0) = if r ∈ P.erase q then (2 : ℝ) else 0 := by
    intro r hr
    by_cases h : q ≠ r
    · have h' : r ≠ q := by tauto
      have hmem : r ∈ P.erase q := by
        exact Finset.mem_erase.mpr ⟨h', hr⟩
      simp [h, hmem]
    · have h' : r = q := by tauto
      simp [h, h']
  have hsum1 : ∑ r ∈ P, (if q ≠ r then (2 : ℝ) else 0) = ∑ r ∈ P, (if r ∈ P.erase q then (2 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact h_ne r hr
  rw [hsum1]
  have h_disj : Disjoint (P.erase q) ({q} : Finset Point) := by
    simp [Finset.disjoint_left]
    <;> tauto
  have h_union : (P.erase q) ∪ ({q} : Finset Point) = P := by
    simp [hq, Finset.ext_iff]
    <;> tauto
  have h_main : ∑ r ∈ P, (if r ∈ P.erase q then (2 : ℝ) else 0) =
      ∑ r ∈ ((P.erase q) ∪ ({q} : Finset Point)), (if r ∈ P.erase q then (2 : ℝ) else 0) := by
    rw [h_union]
  rw [h_main]
  have h_sum : ∑ r ∈ ((P.erase q) ∪ ({q} : Finset Point)), (if r ∈ P.erase q then (2 : ℝ) else 0) =
      (∑ r ∈ (P.erase q), (if r ∈ P.erase q then (2 : ℝ) else 0)) + ∑ r ∈ ({q} : Finset Point), (if r ∈ P.erase q then (2 : ℝ) else 0) := by
    rw [Finset.sum_union h_disj]
  rw [h_sum]
  have h1 : ∑ r ∈ ({q} : Finset Point), (if r ∈ P.erase q then (2 : ℝ) else 0) = 0 := by
    simp [Finset.sum_singleton]
    <;> norm_num
    <;> tauto
  rw [h1, add_zero]
  have h2 : ∑ r ∈ (P.erase q), (if r ∈ P.erase q then (2 : ℝ) else 0) = ∑ r ∈ (P.erase q), (2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have h_x : x ∈ P.erase q := hx
    have h_x1 : x ≠ q ∧ x ∈ P := by
      simpa [Finset.mem_erase] using h_x
    simpa using h_x1
  rw [h2]
  have h_card : (P.erase q).card = P.card - 1 := Finset.card_erase_of_mem hq
  have h_pos : 1 ≤ P.card := by
    exact Finset.card_pos.mpr ⟨q, hq⟩
  have h₃ : ((P.erase q).card : ℝ) = (P.card : ℝ) - 1 := by
    rw [h_card]
    <;> simp [h_pos]
    <;> norm_cast
  have h4 : ∑ r ∈ (P.erase q), (2 : ℝ) = 2 * ((P.erase q).card : ℝ) := by
    rw [Finset.sum_const]
    <;> ring
  rw [h4, h₃]
  <;> ring

lemma round1_h_main2 (P : Finset Point):
  ∑ q ∈ P, ∑ r ∈ P, (if q ≠ r then (2 : ℝ) else 0) = 2 * (P.card : ℝ) * ((P.card : ℝ) - 1) := by
  have h₁ : ∀ (q : Point), q ∈ P → ∑ r ∈ P, (if q ≠ r then (2 : ℝ) else 0) = 2 * ((P.card : ℝ) - 1) := by
    intro q hq
    exact round1_h_sum_aux P q hq
  calc
    ∑ q ∈ P, ∑ r ∈ P, (if q ≠ r then (2 : ℝ) else 0)
      = ∑ q ∈ P, (2 * ((P.card : ℝ) - 1)) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact h₁ q hq
    _ = 2 * (P.card : ℝ) * ((P.card : ℝ) - 1) := by
        rw [Finset.sum_const]
        <;> ring

theorem round1_h3 (P : Finset Point)
  (h1 : ∀ (q r : Point), q ∈ P → r ∈ P → q ≠ r → (P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card ≤ 2):
  (∑ q ∈ P, ∑ r ∈ P, if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) ≤ 2 * (P.card : ℝ) * ((P.card : ℝ) - 1)  := by
  have h_main1 : ∀ (q : Point), q ∈ P → ∀ (r : Point), r ∈ P → (if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) ≤ 2 :=
    round1_h_main1 P h1
  have h_sum1 : ∀ (q : Point), q ∈ P → ∀ (r : Point), r ∈ P → (if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) ≤ (if q ≠ r then (2 : ℝ) else 0) := by
    intro q hq r hr
    by_cases h : q ≠ r
    ·
      have h₂ : ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) ≤ (2 : ℝ) := by
        have h₃ : (P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card ≤ 2 := h1 q r hq hr h
        exact_mod_cast h₃
      have h₃ : (if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) = ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) := by
        split_ifs <;> tauto
      have h₄ : (if q ≠ r then (2 : ℝ) else 0) = (2 : ℝ) := by
        split_ifs <;> tauto
      rw [h₃, h₄]
      <;> exact h₂
    ·
      have h₂ : ¬ (q ≠ r) := h
      have h₃ : (if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) = 0 := by
        split_ifs <;> tauto
      have h₄ : (if q ≠ r then (2 : ℝ) else 0) = (0 : ℝ) := by
        split_ifs <;> tauto
      rw [h₃, h₄]
      <;> norm_num
  have h_sum2 : (∑ q ∈ P, ∑ r ∈ P, (if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0)) ≤ (∑ q ∈ P, ∑ r ∈ P, (if q ≠ r then (2 : ℝ) else 0)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact h_sum1 i ‹_› j ‹_›
  have h_main2 : (∑ q ∈ P, ∑ r ∈ P, (if q ≠ r then (2 : ℝ) else 0)) = 2 * (P.card : ℝ) * ((P.card : ℝ) - 1) :=
    round1_h_main2 P
  rw [h_main2] at h_sum2
  exact h_sum2
end depth_1_lemma_3


theorem round1_h_ineq3 (P : Finset Point)
  (hconv : ConvexPosition P) (hnc : NoThreeCollinear P):
  (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)) ≤ 3 * (P.card : ℝ) * ((P.card : ℝ) - 1)  := by
  have h1 : ∀ (q r : Point), q ∈ P → r ∈ P → q ≠ r → (P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card ≤ 2 := by
    exact depth_1_lemma_1.round1_h1 P hnc
  have h2 : (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)) =
    (P.card : ℝ) * ((P.card : ℝ) - 1) + (∑ q ∈ P, ∑ r ∈ P, if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) := by
    exact depth_1_lemma_2.round1_h2 P hnc
  have h3 : (∑ q ∈ P, ∑ r ∈ P, if q ≠ r then ((P.filter (fun p => p ≠ q ∧ p ≠ r ∧ dist p q = dist p r)).card : ℝ) else 0) ≤ 2 * (P.card : ℝ) * ((P.card : ℝ) - 1) := by
    exact depth_1_lemma_3.round1_h3 P h1
  have h4 : (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)^2)) ≤ 3 * (P.card : ℝ) * ((P.card : ℝ) - 1) := by
    rw [h2]
    linarith
  exact h4

end depth_0_lemma_3


theorem erdos94 (P : Finset Point)
    (hconv : ConvexPosition P) (hnc : NoThreeCollinear P) :
     ∃ C : ℝ, 0 ≤ C ∧ S P ≤ C * (P.card : ℝ)^3 := by
  have h_ineq1 := depth_0_lemma_1.round1_h_ineq1 P
  have h_ineq2 := depth_0_lemma_2.round1_h_ineq2 P hconv hnc
  have h_ineq3 := depth_0_lemma_3.round1_h_ineq3 P hconv hnc
  have h_step1 : ∀ u ∈ DistSet P, (f P u : ℝ) ^ 2 ≤ ((P.card : ℝ) / 4) * (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2) := by
    intro u hu
    have h21 : (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ)) = 2 * (f P u : ℝ) := h_ineq2 u hu
    have h22 : (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ))^2 ≤ (P.card : ℝ) * (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2) := by
      have h221 := h_ineq1 (fun (q : Point) => ((P.filter (fun q' => q' ≠ q ∧ dist q q' = u)).card : ℝ))
      simpa using h221
    have h222 : (2 * (f P u : ℝ))^2 ≤ (P.card : ℝ) * (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2) := by
      rw [h21] at h22
      exact h22
    have h223 : (2 * (f P u : ℝ))^2 = 4 * (f P u : ℝ)^2 := by ring
    rw [h223] at h222
    nlinarith
  have h_step2 : (∑ u ∈ DistSet P, (f P u : ℝ) ^ 2) ≤ ((P.card : ℝ) / 4) * (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) := by
    have h23 : ∀ u ∈ DistSet P, (f P u : ℝ) ^ 2 ≤ ((P.card : ℝ) / 4) * (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2) := by
      intro u hu
      exact h_step1 u hu
    have h24 : (∑ u ∈ DistSet P, (f P u : ℝ) ^ 2) ≤ (∑ u ∈ DistSet P, ((P.card : ℝ) / 4) * (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact h23 x hx
    have h25 : (∑ u ∈ DistSet P, ((P.card : ℝ) / 4) * (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) = ((P.card : ℝ) / 4) * (∑ u ∈ DistSet P, (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) := by
      rw [Finset.mul_sum]
    have h26 : (∑ u ∈ DistSet P, (∑ p ∈ P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) = (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) := by
      rw [Finset.sum_comm]
    rw [h25, h26] at h24
    exact h24
  have h_step3 : (∑ u ∈ DistSet P, (f P u : ℝ) ^ 2) ≤ (3 / 4) * (P.card : ℝ) ^ 2 * ((P.card : ℝ) - 1) := by
    have h31 : (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) ≤ 3 * (P.card : ℝ) * ((P.card : ℝ) - 1) := h_ineq3
    have h32 : (∑ u ∈ DistSet P, (f P u : ℝ) ^ 2) ≤ ((P.card : ℝ) / 4) * (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) := h_step2
    have h33 : ((P.card : ℝ) / 4) * (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) ≤ ((P.card : ℝ) / 4) * (3 * (P.card : ℝ) * ((P.card : ℝ) - 1)) := by
      have h331 : (∑ p ∈ P, (∑ u ∈ DistSet P, ((P.filter (fun q => q ≠ p ∧ dist p q = u)).card : ℝ) ^ 2)) ≤ 3 * (P.card : ℝ) * ((P.card : ℝ) - 1) := h31
      have h332 : (P.card : ℝ) / 4 ≥ 0 := by positivity
      nlinarith
    have h34 : ((P.card : ℝ) / 4) * (3 * (P.card : ℝ) * ((P.card : ℝ) - 1)) = (3 / 4) * (P.card : ℝ) ^ 2 * ((P.card : ℝ) - 1) := by
      ring
    linarith
  have h_step4 : (3 / 4) * (P.card : ℝ) ^ 2 * ((P.card : ℝ) - 1) ≤ (3 / 4) * (P.card : ℝ) ^ 3 := by
    have h41 : (P.card : ℝ) ≥ 0 := by positivity
    nlinarith [sq_nonneg ((P.card : ℝ) - 1), sq_nonneg ((P.card : ℝ))]
  have h_final : S P ≤ (3 / 4) * (P.card : ℝ) ^ 3 := by
    have h51 : S P = (∑ u ∈ DistSet P, (f P u : ℝ) ^ 2) := rfl
    linarith [h_step3, h_step4]
  exact ⟨(3 / 4 : ℝ), by norm_num, h_final⟩

#print axioms erdos94
