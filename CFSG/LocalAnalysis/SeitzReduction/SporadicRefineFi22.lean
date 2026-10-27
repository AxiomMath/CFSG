module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt

public section

namespace CFSG.SeitzReduction.SporadicRefine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG Subgroup CFSG.Blueprint CFSG.LocalCores
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

theorem fi22P_outer_card_fixSub_of_component
    (β : MulAut fi22P) (hβ2 : β * β = 1)
    (hβn : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner fi22P)
    {B : Subgroup (fixSub β)} (hB : IsComponent B)
    (hcard : Nat.card (B ⧸ Subgroup.center B) = 1451520) :
    Nat.card (fixSub β) = 2903040 := by
  obtain ⟨r, rfl⟩ := fi22RAut.surjective β
  have hr2 : r * r = 1 := fi22RAut.injective (by rw [map_mul, hβ2, map_one])
  have hrP : (r : Equiv.Perm (Fin 3510)) ∉ fi22P := by
    intro h
    apply hβn
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, ← fi22RAut_inn]
    exact ⟨r, Subgroup.mem_subgroupOf.2 h, rfl⟩
  obtain ⟨hB2, hc2⟩ := component_quotient_mulEquiv (fixSubRAutEquiv r) hB
  rw [hc2] at hcard
  rw [Nat.card_congr (fixSubRAutEquiv r).toEquiv]
  set τ := (r : Equiv.Perm (Fin 3510))
  have hτ1 : τ ≠ 1 := fun h => hrP (h ▸ fi22P.one_mem)
  have hτ2 : τ * τ = 1 := congrArg Subtype.val hr2
  have hτo : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  obtain ⟨k, hk, c, hc, hck⟩ := fi22R_involution_conj r.2 hτo
  have hcn := fi22R_le_normalizer hc
  have hk3 : 3 ≤ k := by
    by_contra h
    apply hrP
    have hkP : fi22ExtRep k ∈ fi22P := CTUC_Fi22_all_extension_involutions_covered.1 k (by omega)
    rw [← hck] at hkP
    exact (Subgroup.mem_normalizer_iff.1 hcn τ).2 hkP
  have e1 := (fi22CP_conj_equiv hcn τ).trans (MulEquiv.subgroupCongr (by rw [hck]))
  obtain ⟨hB1, hc1⟩ := component_quotient_mulEquiv e1 hB2
  rw [hc1] at hcard
  rw [Nat.card_congr e1.toEquiv]
  obtain ⟨-, -, h3, h4, h5, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · exfalso
    obtain ⟨hB3, -⟩ := component_quotient_mulEquiv (MulEquiv.subgroupCongr h3) hB1
    exact fo22H2_no_component _ hB3
  · exfalso
    obtain ⟨hB3, hc3⟩ := component_quotient_mulEquiv (MulEquiv.subgroupCongr h4) hB1
    rw [hc3, fo22H3_component hB3] at hcard
    norm_num at hcard
  · rw [Nat.card_congr (MulEquiv.subgroupCongr h5).toEquiv, card_fi22H (c := 4) (by norm_num)]
    rfl

theorem fixedSubgroup_eq_fixSub {S : Type*} [Group S] (σ : MulAut S) :
    fixedSubgroup σ = fixSub σ := by
  ext x
  exact Iff.rfl

theorem fi22_outer_card_fixedSubgroup
    {S : Type} [Group S] (e : S ≃* NativeSporadic.Fi22) {σ : MulAut S} (hσ2 : σ * σ = 1)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hcard : Nat.card (D ⧸ center D) = 1451520) :
    Nat.card (fixedSubgroup σ) = 2903040 := by
  set θ : S ≃* fi22P := e.trans fi22PermEquiv
  let φ := MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub σ)
  obtain ⟨hD1, hc1⟩ := component_quotient_mulEquiv φ hD
  obtain ⟨hD2, hc2⟩ := component_quotient_mulEquiv (fixSubCongr θ σ) hD1
  rw [hc1, hc2] at hcard
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr (fixSubCongr θ σ).toEquiv]
  exact fi22P_outer_card_fixSub_of_component _ (congr_mul_self θ σ hσ2)
    (fun h => hout ((congr_mem_inner_iff θ σ).1 h)) hD2 hcard

theorem fi22_outer_not_twoFree_of_lieModel
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Fi22) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) (hDm : LieModel D .PSp 3 2 1) :
    ¬ F4Pilot.FixedCentralizerTwoFree σ D := by
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hs : IsSimpleGroup D := F4Pilot.isSimpleGroup_of_lieModel_PSp hDm
  have hZ : center D = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hD.1 hs
  have hDcard : Nat.card D = 1451520 := by
    rw [F4Pilot.card_of_lieModel_PSp_three_two hDm]
    norm_num
  have hquot : Nat.card (D ⧸ center D) = 1451520 := by
    rw [← hDcard]
    exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv
  have hH := fi22_outer_card_fixedSubgroup e hσ2 hout hD hquot
  have hidx : D.index = 2 := by
    have h := D.card_mul_index
    rw [hDcard, hH] at h
    omega
  exact not_fixedCentralizerTwoFree_of_index_two hidx hZ
    (allInner_of_lieModel_PSp_two (r := 3) le_rfl hDm)

end CFSG.SeitzReduction.SporadicRefine
