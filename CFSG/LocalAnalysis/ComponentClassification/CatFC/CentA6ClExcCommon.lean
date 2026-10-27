module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Witness

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lieModel_dvd_360 (hO : LieOrderFormulasInput) {X : Type} [Group X] {τ : StatedLieTag}
    {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel X τ n p f) (hX : Nat.card X ∣ 360) : τ = .PSL ∧ n = 2 := by
  obtain ⟨-, -, hfac⟩ := hO X τ n p f hadm hm
  have hp := hadm.1
  have hf := hadm.2.1
  rcases lieSylowExponent_ge_three hadm hp2 with h | h3
  · exact h
  · exfalso
    have hdvd : p ^ (lieSylowExponent τ n * f) ∣ 360 := by
      rw [← hfac]
      exact (Nat.ordProj_dvd (Nat.card X) p).trans hX
    have h3f : 3 ≤ lieSylowExponent τ n * f := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
    have h27 : p ^ 3 ∣ 360 := (pow_dvd_pow p h3f).trans hdvd
    have hp7 : p ≤ 7 := by
      by_contra hlt
      push Not at hlt
      have h1 : 8 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
      have h2 := Nat.le_of_dvd (by norm_num) h27
      omega
    interval_cases p <;> revert hp hp2 h27 <;> decide

section Witness

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {D : Subgroup ↥(fixedSubgroup σ)}

theorem A6Hyp.card_dvd_of_perfect_inj (h : A6Hyp σ D) {Q : Type} [Group Q]
    (φ : Q →* ↥(fixedSubgroup σ)) (hφ : Function.Injective φ) (hQ : commutator Q = ⊤) :
    Nat.card Q ∣ 360 := by
  have hperf : ⁅φ.range, φ.range⁆ = φ.range := by
    have h1 : φ.range = Subgroup.map φ ⊤ := MonoidHom.range_eq_map φ
    have h2 : commutator Q = ⁅(⊤ : Subgroup Q), ⊤⁆ := rfl
    rw [h2] at hQ
    rw [h1, ← Subgroup.map_commutator, hQ]
  have hle : φ.range ≤ D := h.2.2 _ hperf
  have h3 := Subgroup.card_dvd_of_le hle
  rwa [h.card_D, ← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h3

theorem A6Hyp.false_of_quasisimple_lie (hO : LieOrderFormulasInput) (h : A6Hyp σ D) {Q : Type}
    [Group Q] (φ : Q →* ↥(fixedSubgroup σ)) (hφ : Function.Injective φ)
    (hQ : CFSG.IsQuasisimple Q) {τ : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (Q ⧸ center Q) τ n p f) (hne : ¬ (τ = .PSL ∧ n = 2)) : False := by
  have h1 := h.card_dvd_of_perfect_inj φ hφ (Group.isPerfect_def.mp hQ.1)
  have h2 : Nat.card (Q ⧸ center Q) ∣ Nat.card Q := Subgroup.card_quotient_dvd_card _
  exact hne (lieModel_dvd_360 hO hadm hp2 hm (h2.trans h1))

end Witness

@[expose] def HasBigLieSub (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ (Q : Type) (_ : Group Q) (φ : Q →* Y), Function.Injective φ ∧ CFSG.IsQuasisimple Q ∧
    ∃ (τ : StatedLieTag) (n f : ℕ), StatedLieAdmissible τ n p f ∧ ¬ (τ = .PSL ∧ n = 2) ∧
      Blueprint.LieModel (Q ⧸ center Q) τ n p f

theorem HasBigLieSub.of_mulEquiv {p : ℕ} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : HasBigLieSub p Y) : HasBigLieSub p Y' := by
  obtain ⟨Q, _, φ, hφ, hQ, hrest⟩ := h
  exact ⟨Q, inferInstance, e.toMonoidHom.comp φ, e.injective.comp hφ, hQ, hrest⟩

theorem HasBigLieSub.of_subgroup {p : ℕ} {Y : Type} [Group Y] (H : Subgroup Y)
    (hq : CFSG.IsQuasisimple ↥H) {τ : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible τ n p f) (hne : ¬ (τ = .PSL ∧ n = 2))
    (hm : Blueprint.LieModel (↥H ⧸ center ↥H) τ n p f) : HasBigLieSub p Y :=
  ⟨↥H, inferInstance, H.subtype, H.subtype_injective, hq, τ, n, f, hadm, hne, hm⟩

theorem A6Hyp.false_of_hasBigLieSub {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {D : Subgroup ↥(fixedSubgroup σ)} (hO : LieOrderFormulasInput) (h : A6Hyp σ D) {p : ℕ}
    (hp2 : p ≠ 2) (hB : HasBigLieSub p ↥(fixedSubgroup σ)) : False := by
  obtain ⟨Q, _, φ, hφ, hQ, τ, n, f, hadm, hne, hm⟩ := hB
  exact h.false_of_quasisimple_lie hO φ hφ hQ hadm hp2 hm hne

end CFSG.ComponentClassification.CatFC
