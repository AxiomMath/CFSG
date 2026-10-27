module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34
public import CFSG.Sporadic.SmallOddCore.HeLocal
public import CFSG.Sporadic.HeldB.OuterFixedCore
public import CFSG.Sporadic.HeldB.OuterCent
public import CFSG.Sporadic.HeldB.AutModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section He


theorem he_inner_fixedSubgroup_cases {S : Type} [Group S] (e : S ≃* NativeSporadic.He) (s : S)
    (hs : orderOf s = 2) :
    Nonempty (fixedSubgroup (MulAut.conj s) ≃* heInnerGrp0) ∨
      Nonempty (fixedSubgroup (MulAut.conj s) ≃* heInnerGrp1) := by
  set θ : S ≃* heP := e.trans heEquivP
  have ht2 : orderOf ((θ s : heP) : Equiv.Perm (Fin 8330)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_mulEquiv_apply, hs]
  let f : fixedSubgroup (MulAut.conj s) ≃*
      centralizerIn heP ((θ s : heP) : Equiv.Perm (Fin 8330)) :=
    ((fixedSubgroupCongr θ (MulAut.conj s)).trans
      (MulEquiv.subgroupCongr (by rw [congr_conj, fixedSubgroup_conj]))).trans
      (heCentralizerEquiv (θ s))
  rcases involution_conj_cases (θ s).2 ht2 with ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
  · left
    exact ⟨f.trans (((MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans
      (infCentralizerConjEquiv hc (heGenPerm 0))).trans
      (MulEquiv.subgroupCongr heInnerGrp0_eq.symm))⟩
  · right
    exact ⟨f.trans (((MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans
      (infCentralizerConjEquiv hc heT1P)).trans (MulEquiv.subgroupCongr heInnerGrp1_eq.symm))⟩

theorem he_inner_not_twoSmall {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.He)
    {s : S} (hs : orderOf s = 2) {D : Subgroup (fixedSubgroup (MulAut.conj s))}
    (hD : IsComponent D) : ¬ FixedCentralizerTwoSmall (MulAut.conj s) D := by
  rcases he_inner_fixedSubgroup_cases e s hs with h0 | h1
  · obtain ⟨φ⟩ := h0
    exact not_fixedCentralizerTwoSmall_of_mulEquiv_ker hD φ heRho0 card_heRho0_ker
  · obtain ⟨φ⟩ := h1
    exact (heC1_no_component _ (LocalCores.isComponent_map_mulEquiv φ hD)).elim

theorem he_outer_card_fixedSubgroup {S : Type} [Group S] (e : S ≃* NativeSporadic.He)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nat.card (fixedSubgroup σ) = 15120 := by
  set θ : S ≃* heP := e.trans heEquivP
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
    (MulAut.congr θ σ) (by rw [orderOf_congr, hσ]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  rw [Nat.card_congr (((fixedSubgroupCongr θ σ).trans
    (MulEquiv.subgroupCongr (by rw [hx]))).trans
    (fixedSubgroupEquivOfConj x hg heAutU hxg)).toEquiv,
    ← ctbh_outer_centralizer_small_action_arithmetic.1]
  exact ctbh_outer_centralizer_small_action_arithmetic.2.1

theorem he_false_of_l34 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.He) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 20160)
    (hσD : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D) ∨
      FixedCentralizerTwoFree σ D) : False := by
  have := hS
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    have hs : orderOf s = 2 := by
      rw [← orderOf_injective _
        (ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna) s]
      exact hσ
    rcases hσD with ⟨-, hsmall⟩ | hfree
    · exact he_inner_not_twoSmall e hs hD hsmall
    · exact LinearPilot.not_mem_range_conj_of_twoFree hna hσ hfree ⟨s, rfl⟩
  · have h := card_quotient_center_dvd_card_fixedSubgroup D
    rw [hcard, he_outer_card_fixedSubgroup e hσ hin] at h
    norm_num at h

end He

end CFSG.SeitzReduction.SporadicRefine
