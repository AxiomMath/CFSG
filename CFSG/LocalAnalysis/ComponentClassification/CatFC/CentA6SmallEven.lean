module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SmallBasic
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqEvenClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqEvenExc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)

theorem exists_involution_not_mem_of_sp42 {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {C : Type} [Group C] (Φ : C ≃* CFSG.Open.StatedSp 2 k) {D : Subgroup C}
    (hD : Nat.card ↥D = 360) : ∃ x : C, orderOf x = 2 ∧ x ∉ D := by
  by_contra hno
  push_neg at hno
  let ω : CFSG.ComponentClassification.PresentationLocal.sympFour ≃* Equiv.Perm (Fin 6) :=
    MulEquiv.ofBijective CFSG.ComponentClassification.PresentationLocal.omegaPerm
      ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
        CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩
  let ε : C ≃* Equiv.Perm (Fin 6) :=
    (Φ.trans (CFSG.SignalizerFunctorTheorem.NonLocal.spTwoTwoEquiv hk)).trans ω
  have hsw : ∀ s : Equiv.Perm (Fin 6), s.IsSwap → s ∈ D.map ε.toMonoidHom := by
    intro s hs
    refine ⟨ε.symm s, hno _ ?_, by simp⟩
    rw [MulEquiv.orderOf_eq]
    exact hs.orderOf
  have hle : Subgroup.closure {σ : Equiv.Perm (Fin 6) | σ.IsSwap} ≤ D.map ε.toMonoidHom :=
    (Subgroup.closure_le _).2 fun s hs => hsw s hs
  rw [Equiv.Perm.closure_isSwap] at hle
  have htop : D.map ε.toMonoidHom = ⊤ := top_le_iff.1 hle
  have hcard : Nat.card ↥(D.map ε.toMonoidHom) = Nat.card ↥D :=
    Subgroup.card_map_of_injective ε.injective
  rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    at hcard
  have h720 : (6 : ℕ).factorial = 720 := by decide
  omega


theorem a6small_even_false (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S]
    (heven : EvenLieType S) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) (D : Subgroup ↥(fixedSubgroup σ))
    (hDn : D.Normal) (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6)))
    (hC : Nat.card (fixedSubgroup σ) ≤ 720)
    (hinv : ∀ x : ↥(fixedSubgroup σ), orderOf x = 2 → x ∈ D) : False := by
  have hC1440 : Nat.card (fixedSubgroup σ) ≤ 1440 := by omega
  have hCa : Nat.card (autCentralizer σ) ≤ 5760 := by
    rw [autCentralizer_eq_fixedSubgroup]; omega
  have hC' := a6small_derived_iso D hDn hD hC1440
  have hD360 : Nat.card ↥D = 360 := by
    obtain ⟨e⟩ := hD
    rw [Nat.card_congr e.toEquiv, a6sq_card]
  have hfin : ∀ (k : Type) [Field k] [Finite k], Nat.card k = 2 →
      Nonempty (↥(fixedSubgroup σ) ≃* CFSG.Open.StatedSp 2 k) → False := by
    intro k _ _ hk ⟨Φ⟩
    obtain ⟨x, hx2, hxD⟩ := exists_involution_not_mem_of_sp42 hk Φ hD360
    exact hxD (hinv x hx2)
  obtain ⟨t, n, f, hadm, hm⟩ := heven
  cases t
  · exact a6sq_even_PSL_core hO hadm hm hσ hout hCa hC' fun _ _ k _ _ hk hΦ => hfin k hk hΦ
  · exact a6sq_even_PSU_core hO hadm hm hσ hout hCa hC' fun _ _ k _ _ hk hΦ => hfin k hk hΦ
  · exact a6sq_even_PSp_core hO hadm hm hσ hout hCa hC' fun _ _ k _ _ hk hΦ => hfin k hk hΦ
  · exact (hadm.2.2.2 rfl).elim
  · exact a6sq_even_Omega_core hO (Or.inl rfl) hadm hm hσ hout hCa hC'
  · exact a6sq_even_Omega_core hO (Or.inr rfl) hadm hm hσ hout hCa hC'
  · exact a6sq_even_G2 hO hadm hm hσ hout hCa hC'
  · exact a6sq_even_F4 hO hadm hm hσ hout hCa hC'
  · exact a6sq_even_E6 hO hadm hm hσ hout hCa hC'
  · exact a6sq_even_E7_E8 hO (Or.inl rfl) hadm hm hσ hout hCa hC'
  · exact a6sq_even_E7_E8 hO (Or.inr rfl) hadm hm hσ hout hCa hC'
  · exact a6sq_even_twistedE6 hO hadm hm hσ hout hCa hC'
  · exact a6sq_even_trialityD4 hO hadm hm hσ hout hCa hC'
  · exact a6sq_even_twistedB2 hadm hm hσ hout
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · exact a6sq_even_twistedF4 hadm hm hσ hout
  · exact a6sq_even_Tits hadm hm hσ hout

end CFSG.ComponentClassification.CatFC
