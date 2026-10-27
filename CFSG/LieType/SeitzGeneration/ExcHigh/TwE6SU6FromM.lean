module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh


variable {K : Type} [Field K] {σ : K →+* K}

theorem orbitH_mem_orbitRankOneGroup (σ : K →+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (w : (orbitField TwistTag.E6 K σ a)ˣ) :
    ((orbitH TwistTag.E6 K σ a w : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈
      orbitRankOneGroup TwistTag.E6 K σ a := by
  rw [orbitRankOneGroup, ← orbitRankOneHom_range]
  exact ⟨HSL w, orbitRankOneHom_HSL a w⟩

theorem torusAB_mem_of_orbit {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (h0 : orbitRankOneGroup TwistTag.E6 K σ orb0 ≤ Y)
    (h1 : orbitRankOneGroup TwistTag.E6 K σ orb1 ≤ Y) {u v : Kˣ} (hu : u ∈ normOne σ)
    (hv : v ∈ normOne σ) : torusAB σ u v ∈ Y := by
  have hu2 : (σ ^ (TwistTag.E6.orbit orb0).card) (u : K) = u := by
    rw [orb0_card]; exact sigma_sq_of_normOne σ hu
  have hv2 : (σ ^ (TwistTag.E6.orbit orb1).card) (v : K) = v := by
    rw [orb1_card]; exact sigma_sq_of_normOne σ hv
  have e0 := orbitH_two σ orb0 orb0_card (orbUnit σ orb0 u hu2)
  have e1 := orbitH_two σ orb1 orb1_card (orbUnit σ orb1 v hv2)
  rw [orb0_perm, orb0_min] at e0
  rw [orb1_perm, orb1_min] at e1
  have hu0 : Units.map (orbitField TwistTag.E6 K σ orb0).subtype.toMonoidHom
      (orbUnit σ orb0 u hu2) = u := Units.ext rfl
  have hu1 : Units.map (σ.comp (orbitField TwistTag.E6 K σ orb0).subtype).toMonoidHom
      (orbUnit σ orb0 u hu2) = sU σ u := Units.ext rfl
  have hv0 : Units.map (orbitField TwistTag.E6 K σ orb1).subtype.toMonoidHom
      (orbUnit σ orb1 v hv2) = v := Units.ext rfl
  have hv1 : Units.map (σ.comp (orbitField TwistTag.E6 K σ orb1).subtype).toMonoidHom
      (orbUnit σ orb1 v hv2) = sU σ v := Units.ext rfl
  rw [hu0, hu1] at e0
  rw [hv0, hv1] at e1
  rw [torusAB_eq, ← e0, ← e1]
  exact mul_mem (h0 (orbitH_mem_orbitRankOneGroup σ orb0 (orbUnit σ orb0 u hu2)))
    (h1 (orbitH_mem_orbitRankOneGroup σ orb1 (orbUnit σ orb1 v hv2)))

theorem frameSeq_orb : ∀ i : Fin 4, i.val ≤ 2 → ∀ a ∈ frameSeq i, a = orb0 ∨ a = orb1 := by
  decide

theorem frameConj_mem_of_orbit {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (h0 : orbitRankOneGroup TwistTag.E6 K σ orb0 ≤ Y)
    (h1 : orbitRankOneGroup TwistTag.E6 K σ orb1 ≤ Y) (i : Fin 4) (hi : i.val ≤ 2) :
    frameConj σ i ∈ Y := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
  rcases frameSeq_orb i hi a ha with rfl | rfl
  · exact h0 (orbitN_one_mem_orbitRankOneGroup _)
  · exact h1 (orbitN_one_mem_orbitRankOneGroup _)

theorem frameHom_mem_of_orbit {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (h0 : orbitRankOneGroup TwistTag.E6 K σ orb0 ≤ Y)
    (h1 : orbitRankOneGroup TwistTag.E6 K σ orb1 ≤ Y)
    (h2 : orbitRankOneGroup TwistTag.E6 K σ orbLeaf ≤ Y) (i : Fin 4) (hi : i.val ≤ 2)
    (A : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    ((frameHom σ i A : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) ∈ Y := by
  have hc : frameConj σ i ∈ Y := frameConj_mem_of_orbit h0 h1 i hi
  have hA : rankOneFix σ orbLeaf orbLeaf_card A ∈ Y := by
    refine h2 ?_
    rw [orbitRankOneGroup, ← orbitRankOneHom_range]
    exact ⟨fixIncl σ orbLeaf orbLeaf_card A, rfl⟩
  rw [coe_frameHom]
  show frameConj σ i * rankOneFix σ orbLeaf orbLeaf_card A * (frameConj σ i)⁻¹ ∈ Y
  exact mul_mem (mul_mem hc hA) (inv_mem hc)

end CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
