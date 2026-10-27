module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneRee
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossRankTwo
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofReeConj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion

open CFSG.Open Subgroup TauCeti CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.LieType.Chevalley (fixSubfield)

open CFSG.RankThree.PartOne.Sec66T (fixSub)


section Ree


theorem fusesIntoFixedE9_reeGammaFieldAut {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : K ≃+* K} (hβ : orderOf β = 3) :
    FusesIntoFixedE9 (F4.reeGammaFieldAut K a β) := by
  obtain ⟨b, -, hbcard, hchar, ⟨eC⟩⟩ :=
    CFSG.RankThree.PartOne.Sec66T.reeF4_fixed_data_odd hK Nat.prime_three (by norm_num) hβ
  have : Finite (F4.reeGamma (fixSubfield β) b) := Subtype.finite
  have : Finite (F4.reeGamma K a) := Subtype.finite
  obtain ⟨u, v, hu, hv3, hvu, huv⟩ := exists_plane_of_hasNoncommPair
    (CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.hasNoncommPair_reeGamma b
      (fixSubfield β) hbcard)
  set ι : F4.reeGamma (fixSubfield β) b →* F4.reeGamma K a :=
    (fixSub (F4.reeGammaFieldAut K a β)).subtype.comp eC.symm.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (fixSub (F4.reeGammaFieldAut K a β)).subtype_injective.comp eC.symm.injective
  have hfix : ∀ w, F4.reeGammaFieldAut K a β (ι w) = ι w := fun w => (eC.symm w).2
  have hu' : orderOf (ι u) = 3 := by rw [orderOf_injective ι hιinj, hu]
  have hv3' : ι v ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
  have hvu' : ι v ∉ zpowers (ι u) := by
    rintro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    exact hvu (Subgroup.mem_zpowers_iff.2 ⟨k, hιinj (by rw [map_zpow, hk])⟩)
  have huv' : ι u * ι v = ι v * ι u := by rw [← map_mul, ← map_mul, huv]
  refine fusesIntoFixedE9_of_reps (isElemAbelian_sup_zpowers
    (pow_three_eq_one_of_orderOf hu') hv3' huv') (card_sup_zpowers_eq_nine hu' hv3' hvu' huv')
    (fixed_of_mem_sup_zpowers (hfix u) (hfix v)) fun x hx => ?_
  obtain ⟨g, hg⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts3Ree.reeGamma_orderThree_conj a K hK x (ι u) hx hu'
  exact ⟨g, by rw [hg]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)⟩

theorem innerFusionE9At_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) :
    InnerFusionE9At ⟨.reeF4 m, hv⟩ := by
  obtain ⟨X, _, _, _, hm1, hX, -, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  refine innerFusionE9At_of_model e fun α hα3 hαo => ?_
  have hα1 : α ≠ 1 := fun h => hαo ⟨1, by rw [map_one, h]⟩
  have hout : CFSG.RankThree.PartOne.CTP.IsOuterOfOrder 3 α :=
    ⟨orderOf_eq_three hα3 hα1, fun g hg => hαo ⟨g, hg.symm⟩⟩
  obtain ⟨g, β, hβ, hαβ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeF4_stdDescent_odd hm1 hX
      Nat.prime_three α hout
  refine FusesIntoFixedE9.of_conj (MulAut.conj g)⁻¹ ?_
  have hconj : (MulAut.conj g)⁻¹ * α * (MulAut.conj g)⁻¹⁻¹ = F4.reeGammaFieldAut X m β := by
    rw [hαβ]
    group
  rw [hconj]
  exact fusesIntoFixedE9_reeGammaFieldAut hX hβ

end Ree

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion
