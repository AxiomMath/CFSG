module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Principles

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.psu_range_le_of_perfect (h : A6Hyp σ D) {Q : Type} [Group Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) : φ.range ≤ D := by
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    have h1 : φ.range = Subgroup.map φ ⊤ := MonoidHom.range_eq_map φ
    have h2 : commutator Q = ⁅(⊤ : Subgroup Q), ⊤⁆ := rfl
    rw [h2] at hQ
    rw [h1, ← Subgroup.map_commutator, hQ]
  exact h.2.2 _ hperf

theorem A6Hyp.psu_card_range_dvd (h : A6Hyp σ D) {Q : Type} [Group Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) : Nat.card φ.range ∣ 360 := by
  have h3 := Subgroup.card_dvd_of_le (h.psu_range_le_of_perfect φ hQ)
  rwa [h.card_D] at h3

theorem A6Hyp.psu_central_quotient_dvd (h : A6Hyp σ D) {Q : Type} [Group Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) (hker : φ.ker ≤ Subgroup.center Q) :
    Nat.card (Q ⧸ Subgroup.center Q) ∣ 360 := by
  have h1 := h.psu_card_range_dvd φ hQ
  have h2 : (Subgroup.center Q).index ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker] at h2
  rw [← Subgroup.index_eq_card]
  exact h2.trans h1

theorem A6Hyp.psu_range_eq_of_central_quotient (h : A6Hyp σ D) {Q : Type} [Group Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hQ : commutator Q = ⊤) (hker : φ.ker ≤ Subgroup.center Q)
    (hcard : Nat.card (Q ⧸ Subgroup.center Q) = 360) : φ.range = D := by
  have h1 := h.psu_card_range_dvd φ hQ
  have h2 : (Subgroup.center Q).index ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker, Subgroup.index_eq_card, hcard] at h2
  have h3 : Nat.card φ.range = 360 := Nat.dvd_antisymm h1 h2
  exact Subgroup.eq_of_le_of_card_ge (h.psu_range_le_of_perfect φ hQ) (by rw [h.card_D, h3])

theorem A6Hyp.psu_commuting_pair_false (h : A6Hyp σ D) {Q₁ Q₂ : Type} [Group Q₁] [Group Q₂]
    (φ₁ : Q₁ →* ↥(fixedSubgroup σ)) (φ₂ : Q₂ →* ↥(fixedSubgroup σ))
    (h₁ : commutator Q₁ = ⊤) (h₂ : commutator Q₂ = ⊤)
    (hk₁ : φ₁.ker ≤ Subgroup.center Q₁) (hk₂ : φ₂.ker ≤ Subgroup.center Q₂)
    (hc₁ : Nat.card (Q₁ ⧸ Subgroup.center Q₁) = 360)
    (hc₂ : Nat.card (Q₂ ⧸ Subgroup.center Q₂) = 360)
    (hcomm : ∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x) : False := by
  have e₁ := h.psu_range_eq_of_central_quotient φ₁ h₁ hk₁ hc₁
  have e₂ := h.psu_range_eq_of_central_quotient φ₂ h₂ hk₂ hc₂
  obtain ⟨eA⟩ := h.2.1
  obtain ⟨a, b, hab⟩ := a6sq_nonab
  have hd₁ : (eA.symm a : ↥(fixedSubgroup σ)) ∈ φ₁.range := by rw [e₁]; exact (eA.symm a).2
  have hd₂ : (eA.symm b : ↥(fixedSubgroup σ)) ∈ φ₂.range := by rw [e₂]; exact (eA.symm b).2
  obtain ⟨x, hx⟩ := hd₁
  obtain ⟨y, hy⟩ := hd₂
  have hxy : (eA.symm a : ↥(fixedSubgroup σ)) * (eA.symm b : ↥(fixedSubgroup σ)) =
      (eA.symm b : ↥(fixedSubgroup σ)) * (eA.symm a : ↥(fixedSubgroup σ)) := by
    rw [← hx, ← hy]
    exact hcomm x y
  apply hab
  apply eA.symm.injective
  apply Subtype.ext
  simp only [MulEquiv.map_mul, Subgroup.coe_mul]
  exact hxy

end Principles

@[expose] def PSUHas27Sub (G : Type) [Group G] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (j : Q →* G), Function.Injective j ∧ commutator Q = ⊤ ∧
    27 ∣ Nat.card (Q ⧸ Subgroup.center Q)

@[expose] def PSUHasPair360 (G : Type) [Group G] : Prop :=
  ∃ (Q₁ Q₂ : Type) (_ : Group Q₁) (_ : Group Q₂) (j₁ : Q₁ →* G) (j₂ : Q₂ →* G),
    Function.Injective j₁ ∧ Function.Injective j₂ ∧ commutator Q₁ = ⊤ ∧ commutator Q₂ = ⊤ ∧
    Nat.card (Q₁ ⧸ Subgroup.center Q₁) = 360 ∧ Nat.card (Q₂ ⧸ Subgroup.center Q₂) = 360 ∧
    ∀ x y, j₁ x * j₂ y = j₂ y * j₁ x

theorem PSUHas27Sub.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : PSUHas27Sub G) :
    PSUHas27Sub H := by
  obtain ⟨Q, _, j, hj, hQ, h27⟩ := h
  exact ⟨Q, inferInstance, e.toMonoidHom.comp j, e.injective.comp hj, hQ, h27⟩

theorem PSUHasPair360.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : PSUHasPair360 G) :
    PSUHasPair360 H := by
  obtain ⟨Q₁, Q₂, _, _, j₁, j₂, hj₁, hj₂, hQ₁, hQ₂, hc₁, hc₂, hcomm⟩ := h
  refine ⟨Q₁, Q₂, inferInstance, inferInstance, e.toMonoidHom.comp j₁, e.toMonoidHom.comp j₂,
    e.injective.comp hj₁, e.injective.comp hj₂, hQ₁, hQ₂, hc₁, hc₂, fun x y => ?_⟩
  change e (j₁ x) * e (j₂ y) = e (j₂ y) * e (j₁ x)
  rw [← map_mul, ← map_mul, hcomm]

theorem psu_dvd_27_of_lieModel (hO : LieOrderFormulasInput) {Y : Type} [Group Y] {τ : StatedLieTag}
    {n f : ℕ} (hadm : StatedLieAdmissible τ n 3 f) (hm : LieModel Y τ n 3 f)
    (h3 : 3 ≤ lieSylowExponent τ n * f) : 27 ∣ Nat.card Y := by
  obtain ⟨-, -, hfac⟩ := hO Y τ n 3 f hadm hm
  have : 3 ^ (lieSylowExponent τ n * f) ∣ Nat.card Y := by
    rw [← hfac]
    exact Nat.ordProj_dvd (Nat.card Y) 3
  exact (pow_dvd_pow 3 h3).trans this

theorem PSUHas27Sub.of_lieModel (hO : LieOrderFormulasInput) {G : Type} [Group G] (M : Subgroup G)
    (hM : Group.IsPerfect M) {τ : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible τ n 3 f)
    (hm : LieModel (M ⧸ Subgroup.center M) τ n 3 f) (h3 : 3 ≤ lieSylowExponent τ n * f) :
    PSUHas27Sub G :=
  ⟨M, inferInstance, M.subtype, M.subtype_injective, Group.isPerfect_def.mp hM,
    psu_dvd_27_of_lieModel hO hadm hm h3⟩

theorem psu_card_of_lieModel_psl_two_nine (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    (hadm : StatedLieAdmissible .PSL 2 3 2) (hm : LieModel Y .PSL 2 3 2) : Nat.card Y = 360 := by
  obtain ⟨-, hmul, -⟩ := hO Y .PSL 2 3 2 hadm hm
  have h1 : lieOrderNumerator .PSL 2 (3 ^ 2) = 720 := by decide
  have h2 : lieOrderDivisor .PSL 2 (3 ^ 2) = 2 := by decide
  rw [h1, h2] at hmul
  omega

theorem psu_not_dvd_three_three (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hadm : StatedLieAdmissible .PSU 3 3 1) (hm : LieModel X .PSU 3 3 1) :
    ¬ 360 ∣ Nat.card X := by
  obtain ⟨-, hmul, -⟩ := hO X .PSU 3 3 1 hadm hm
  have h1 : lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 := by decide
  have h2 : lieOrderDivisor .PSU 3 (3 ^ 1) = 1 := by decide
  rw [h1, h2] at hmul
  omega

end CFSG.ComponentClassification.CatFC
