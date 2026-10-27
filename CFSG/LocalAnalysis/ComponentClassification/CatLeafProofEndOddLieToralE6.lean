module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieToralRows
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralD5

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

theorem e6_toral_D5_quat
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    QuatComponentForm (toralCentralizer .E6 K (bitsTuple e6BitsD5)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _
      (bitsTuple_mem (K := K) e6BitsD5)
  obtain ⟨hqs, -⟩ := e6_levi_D5_recognition hp hp2 hK
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsD5)) =
      subsystemGroup .E6 K e6LeviD5 := by
    rw [rootCharKernel_e6BitsD5 hK2, ← subsystemGroup_eq_rootSpan]
  let e₁ := MulEquiv.subgroupCongr hS
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁).symm hqs
  intro M hM
  obtain rfl := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  exact exists_quaternion_of_rootPair_le hK2 (isRoot_single _ (e6Node 1)) hSX
    ((rootPair_le_subsystemGroup (J := e6LeviD5) ⟨4, rfl⟩).trans hS.symm.le)

theorem e6_toral_A5_quat
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    QuatComponentForm (toralCentralizer .E6 K (bitsTuple e6BitsA5)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : Finite (ModGL .E6 K) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .E6 K e6LeviA5 with hH_def
  set Q := rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6) with hQ_def
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5)) = H ⊔ Q := by
    rw [rootCharKernel_e6BitsA5 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  obtain ⟨hqH, -⟩ := e6_levi_A5_recognition hp hp2 hK
  obtain ⟨-, ⟨eQ⟩, -, -⟩ := odd_arbitrary_root_pair_SL2_p_components .E6 K hK2 isRoot_hiE6
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
  have hHX : H ≤ toralCentralizer .E6 K (bitsTuple e6BitsA5) :=
    (le_sup_left.trans hS.symm.le).trans hSX
  intro M hM
  rcases eq_or_SL_of_two_factors hS hSX hsolv hcomm hqH eQ
      (rootPair_quasisimple_or_solvable hp hp2 hK hK2 isRoot_hiE6) hM with h | he
  · subst h
    exact exists_quaternion_of_rootPair_le hK2 (isRoot_single _ _) hHX
      (rootPair_le_subsystemGroup (i := e6Node 0) ⟨0, rfl⟩)
  · obtain ⟨e⟩ := he
    exact exists_quaternion_of_mulEquiv_SL hK2 e

theorem oddExcInnerDiagQuatForm_E6
    : OddExcInnerDiagQuatForm .E6 := by
  refine oddExcInnerDiagQuatForm_of_toral (Or.inr (Or.inr (Or.inl rfl)))
    fun K _ _ p f hp hp2 hKp b hb hb1 => ?_
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_quat_of_orbitCheck hK2 e6SignOrbit_check (fun ρ hρ hne => ?_) hb hb1
  have hlen : e6SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e6_toral_D5_quat hp hp2 hKp
  · exact e6_toral_A5_quat hp hp2 hKp

end CFSG.ComponentClassification.CatLeafProof
