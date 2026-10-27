module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem gnImg_thompsonJ_le_of_sq_eq_one {X : Type} [Group X] {T : Subgroup X}
    {S : Subgroup (X ⧸ gnC T)} (h : ∀ s ∈ gnImg T T, s * s = 1 → s ∈ S) :
    gnImg T (CFSG.Quasithin.thompsonJ T) ≤ S := by
  rw [gnImg, CFSG.Quasithin.thompsonJ, Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  refine Subgroup.map_le_iff_le_comap.mpr fun a ha => ?_
  have ha2 : a * a = 1 := by simpa [pow_two] using hA.2.1.2 a ha
  refine h _ (Subgroup.mem_map_of_mem _ (hA.1 ha)) ?_
  rw [← map_mul, ha2, map_one]

@[expose] def jNormCent {X : Type} [Group X] (T : Subgroup X) : Subgroup X :=
  Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X) ⊓
    Subgroup.centralizer (CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) : Set X)

theorem gnImg_normalizer_thompsonJ_le_normalizer_jNormCent {X : Type} [Group X]
    (T : Subgroup X) :
    gnImg T (Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X)) ≤
      Subgroup.normalizer (gnImg T (jNormCent T) : Set (X ⧸ gnC T)) := by
  have hNK : Subgroup.normalizer (CFSG.Quasithin.thompsonJ T : Set X) ≤
      Subgroup.normalizer (jNormCent T : Set X) := by
    intro n hn
    rw [jNormCent]
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hn, ?_⟩
    exact CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup
      (CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T))
      (CFSG.Quasithin.normalizer_le_normalizer_of_map_mulEquiv
        CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv (CFSG.Quasithin.thompsonJ T) hn)
  exact (Subgroup.map_mono hNK).trans (Subgroup.le_normalizer_map _)

theorem baum_le_jNormCent {X : Type} [Group X] (T : Subgroup X) :
    CFSG.Quasithin.baum T ≤ jNormCent T := by
  rw [CFSG.Quasithin.baum, jNormCent]
  exact inf_le_inf_right _
    (Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ T))

theorem jNormCent_le_centralizer {X : Type} [Group X] [Finite X] {T T₁ : Subgroup X}
    (h1 : T₁ ≤ CFSG.Quasithin.omegaOneCenterOf T) :
    jNormCent T ≤ Subgroup.centralizer (T₁ : Set X) := by
  intro x hx
  rw [jNormCent] at hx
  have hxE : x ∈ Subgroup.centralizer
      (CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ T) : Set X) := hx.2
  rw [Subgroup.mem_centralizer_iff] at hxE ⊢
  intro y hy
  exact hxE y ((h1.trans
    (CFSG.AGLEmbeddingD2.GN.omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ T)) hy)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
