module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralD5
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Gen

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups
open CFSG.ComponentClassification.Burgoyne.X10

theorem noPSL2Odd_e6_toral_D5_component
    (hO : LieOrderFormulasInput)
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .E6 K (bitsTuple e6BitsD5))} (hM : IsComponent M) :
    NoPSL2Odd M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .POmegaPlus 5 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _
      (bitsTuple_mem (K := K) e6BitsD5)
  obtain ⟨hqs, hlie⟩ := e6_levi_D5_recognition hp hp2 hK
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsD5)) =
      subsystemGroup .E6 K e6LeviD5 := by
    rw [rootCharKernel_e6BitsD5 hK2, ← subsystemGroup_eq_rootSpan]
  let e₁ := MulEquiv.subgroupCongr hS
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* subsystemGroup .E6 K e6LeviD5 := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁)
  exact noPSL2Odd_of_lieModel hO hp2 (by unfold ExcCompTag; decide) (by decide) hadm
    (lieModel_of_mulEquiv (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie)

theorem noPSL2Odd_e6_toral_A5_component
    (hO : LieOrderFormulasInput)
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .E6 K (bitsTuple e6BitsA5))} (hM : IsComponent M) :
    NoPSL2Odd M := by
  classical
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .PSL 6 p f := ⟨hp, hf, by norm_num, by simp, by simp⟩
  have : Finite (ModGL .E6 K) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .E6 K e6LeviA5 with hH_def
  set Q := rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6) with hQ_def
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5)) = H ⊔ Q := by
    rw [rootCharKernel_e6BitsA5 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : H ⊔ Q ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := hS ▸ hSX
  have hHX : H ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := le_sup_left.trans hSX'
  have hQX : Q ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) := le_sup_right.trans hSX'
  have hD : (rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
        (toralCentralizer .E6 K (bitsTuple e6BitsA5)) =
      H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)) ⊔
        Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)) := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hHX hQX
  obtain ⟨hqH, hlieH⟩ := e6_levi_A5_recognition hp hp2 hK
  obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .E6 K hK2 isRoot_hiE6
  have hQmap : (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
      rootGroup (rootOperatorFamily .E6) K (-hiE6)).map (adjointGroup .E6 K).subtype = Q := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_hiE6,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_hiE6)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup
      (e6A5Node k)) (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
        rootGroup (rootOperatorFamily .E6) K (-hiE6)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E6 (isRoot_single _ _) isRoot_hiE6
        (e6A5Node_ne_hiE6 k).1 (e6A5Node_ne_hiE6 k).2 (iform_e6A5Node_hiE6 k)
        (not_isRoot_e6A5Node_hiE6 k).1 (not_isRoot_e6A5Node_hiE6 k).2
  have hcomm : Commutes H Q := by
    rw [hH_def, show e6LeviA5 = Set.range e6A5Node from rfl,
      ← map_subtype_iSup_rankOne e6A5Node, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hq₁ : IsQuasisimple (H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHX).symm hqH
  have hαβ : ∀ x ∈ H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)),
      ∀ y ∈ Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)), x * y = y * x :=
    fun x hx y hy => Subtype.ext (hcomm x hx y hy)
  have hn₁ : ((H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))).subgroupOf
      ((rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
        (toralCentralizer .E6 K (bitsTuple e6BitsA5)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  have hH : M = H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5)) →
      NoPSL2Odd M := fun h => by
    let e : M ≃* H := (MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hHX)
    exact noPSL2Odd_of_lieModel hO hp2 (by unfold ExcCompTag; decide) (by decide) hadm
      (lieModel_of_mulEquiv (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlieH)
  by_cases h5 : 5 ≤ Nat.card K
  · have hc2 : Nat.card K ≠ 2 := by omega
    have hc3 : Nat.card K ≠ 3 := by omega
    have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm (hfin.2 h5).1
    have hn₂ : ((Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))).subgroupOf
        ((rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
          (toralCentralizer .E6 K (bitsTuple e6BitsA5)))).Normal := by
      rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
      refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (hαβ y hy x hx).symm)
    rcases eq_or_eq_of_isComponent_le_sup hD hq₁ hq₂ hn₁ hn₂ hM hMS with h | h
    · exact hH h
    · let e : M ≃* SL2 K :=
        ((MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hQX)).trans eQ.symm
      exact noPSL2Odd_of_mulEquiv_SL2 hK2 e
  · have h3' : Nat.card K = 3 := by
      have hodd : Odd (Nat.card K) := by
        rw [hK]
        exact (hp.eq_two_or_odd'.resolve_left hp2).pow
      obtain ⟨k, hk⟩ := hodd
      omega
    have hs₂ : Group.IsSolvable (Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
      haveI := (hfin.1 h3').1
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hQX).injective
    exact hH (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM hMS)

theorem excInnerNoPSL2_E6
    (hO : LieOrderFormulasInput) : ExcInnerNoPSL2 .E6 := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo L hL
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have hKodd : Odd (Nat.card K) := by
    rw [hKp]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inr (Or.inl rfl))) hKodd hαg hα
  refine NoPSL2Odd.of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (noPSL2Odd_toralCentralizer_component_of_orbitCheck hK2 e6SignOrbit_check
      (fun ρ hρ hne N hN => ?_) hb (hb1 hα1) (LocalCores.isComponent_map_mulEquiv Θ hL))
  have hlen : e6SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact noPSL2Odd_e6_toral_D5_component hO hp hp2 hKp hN
  · exact noPSL2Odd_e6_toral_A5_component hO hp hp2 hKp hN

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
