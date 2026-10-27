module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers Subgroup CFSG.HallHigman

namespace InnerQ.SimpleQuot

theorem false_of_isPSolvable_of_surjective {X S : Type} [Group X] [Finite X] [Group S]
    {p : ℕ} [Fact p.Prime] (hX : IsPSolvable p X) (φ : X →* S) (hφ : Function.Surjective φ)
    (hS : IsSimpleGroup S) (hSnab : ¬ IsMulCommutative S) (hpS : p ∣ Nat.card S) : False := by
  have hp : p.Prime := Fact.out
  set f : (⊤ : Subgroup X) →* S := φ.comp (⊤ : Subgroup X).subtype
  have hf : Function.Surjective f := fun s => by
    obtain ⟨x, rfl⟩ := hφ s
    exact ⟨⟨x, mem_top x⟩, rfl⟩
  have hsub : (⊤ : Subgroup X).IsSubnormal := (inferInstance : (⊤ : Subgroup X).Normal).isSubnormal
  set e := QuotientGroup.quotientKerEquivOfSurjective f hf
  haveI : IsSimpleGroup ((⊤ : Subgroup X) ⧸ f.ker) := e.isSimpleGroup
  have hidx : f.ker.index = Nat.card S := by
    rw [index, Nat.card_congr e.toEquiv]
  rcases hX ⊤ hsub f.ker this with h | h
  · rw [hidx] at h
    apply hSnab
    haveI : Fact (Nat.card S).Prime := ⟨h ▸ hp⟩
    haveI := isCyclic_of_prime_card (α := S) rfl
    exact ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
  · rw [hidx] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp h hpS

variable {G : Type} [Group G] [Finite G] {p : ℕ}

end InnerQ.SimpleQuot

end CFSG.LocalAnalysis.RankThreeTheoremC
