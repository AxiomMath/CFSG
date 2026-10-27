module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
public import CFSG.LieType.Chevalley.OddE6AllInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralD5

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

theorem e6_toral_D5_slForm
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    SLComponentForm K (toralCentralizer .E6 K (bitsTuple e6BitsD5)) := by
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
  refine slComponentForm_of_eq_or_SL (B := (rootSpan .E6 K (rootCharKernel
    (bitsTuple (K := K) e6BitsD5))).subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsD5)))
    ?_ fun L hL => Or.inl (eq_of_isComponent_of_normal_quasisimple hq hsolv hL)
  rw [Nat.card_congr (e₂.trans e₁).toEquiv]
  exact card_SL_dvd_subsystemGroup hK2 (i := e6Node 1) ⟨4, rfl⟩

theorem e6_toral_A5_slForm
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    SLComponentForm K (toralCentralizer .E6 K (bitsTuple e6BitsA5)) := by
  classical
  obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
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
  obtain ⟨hqH, -⟩ := e6_levi_A5_recognition hp hp2 hK
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
  refine slComponentForm_of_eq_or_SL
    (B := H.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) ?_ fun M hM => ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv]
    exact card_SL_dvd_subsystemGroup hK2 (i := e6Node 0) ⟨0, rfl⟩
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  by_cases h5 : 5 ≤ Nat.card K
  · have hq₂ : IsQuasisimple (Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQX).symm (hfin.2 h5).1
    have hn₂ : ((Q.subgroupOf (toralCentralizer .E6 K (bitsTuple e6BitsA5))).subgroupOf
        ((rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5))).subgroupOf
          (toralCentralizer .E6 K (bitsTuple e6BitsA5)))).Normal := by
      rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
      refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        (hαβ y hy x hx).symm)
    rcases eq_or_eq_of_isComponent_le_sup hD hq₁ hq₂ hn₁ hn₂ hM hMS with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(MulEquiv.subgroupCongr h).trans
        ((Subgroup.subgroupOfEquivOfLe hQX).trans eQ.symm)⟩
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
    exact Or.inl (eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM hMS)

theorem oddExcInnerDiagSLForm_E6
    : OddExcInnerDiagSLForm .E6 := by
  refine oddExcInnerDiagSLForm_of_toral (Or.inr (Or.inr (Or.inl rfl)))
    (fun K _ _ hK α hα L hL =>
      odd_E6_all_involution_fixed_p_components K hK α hα 2 Nat.prime_two L hL)
    (fun K _ _ p f hp hp2 hKp b hb hb1 => ?_)
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_slForm_of_orbitCheck hK2 e6SignOrbit_check (fun ρ hρ hne => ?_) hb hb1
  have hlen : e6SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e6_toral_D5_slForm hp hp2 hKp
  · exact e6_toral_A5_slForm hp hp2 hKp

end CFSG.ComponentClassification.CatLeafProof
