module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCoreCharacteristic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CHHRank
public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G}

omit [Finite G] in
theorem memUniqueConj_of_mem_uniqueSet {M E : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hE : E ∈ uniqueSet M) :
    ∀ g : G, E ≤ M.map (MulAut.conj g).toMonoidHom → g ∈ M := by
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hE.2 g hg)
  rwa [normalizer_maxTwoLocal hM] at hgN

omit [Finite G] in
theorem mem_uniqueSet_of_memUniqueConj {M E : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hEM : E ≤ M) (h : ∀ g : G, E ≤ M.map (MulAut.conj g).toMonoidHom → g ∈ M) :
    E ∈ uniqueSet M := by
  refine ⟨hEM, fun g hg => ?_⟩
  have hgN : g ∈ Subgroup.normalizer (M : Set G) := by
    rw [normalizer_maxTwoLocal hM]
    exact h g hg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
