module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

theorem exists_conj_le_sylow {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    (R : Sylow p Y) {E : Subgroup Y} (hE : ∀ x ∈ E, x ^ p = 1) :
    ∃ g : Y, E.map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup Y) := by
  have hpg : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE x x.2)⟩
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q R
  refine ⟨g, ?_⟩
  have h1 : ((g • Q : Sylow p Y) : Subgroup Y) =
      (Q : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hg] at h1
  rw [h1]
  exact Subgroup.map_mono hQ

end CFSG.AGLEmbedding
