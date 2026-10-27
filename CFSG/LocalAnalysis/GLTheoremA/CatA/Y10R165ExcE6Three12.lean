module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngineSections
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open scoped Matrix MatrixGroups Pointwise

section Certificate


theorem exists_section_lift {H G K : Type} [Group H] [Finite H] [Group G]
    [Field K] [Finite K] [CharP K 2]
    {π : H →* G} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H)
    {L : Subgroup G} (hLperf : ⁅L, L⁆ = L) {x : H}
    (hLx : L ≤ Subgroup.centralizer ({π x} : Set G))
    (e : ↥L ≃* SL(3, K)) (h2 : ¬ 2 ∣ Nat.card π.ker) :
    ∃ (S : Subgroup H) (eS : ↥S ≃* ↥L),
      S ≤ Subgroup.centralizer ({x} : Set H) ∧ S.map π = L ∧ S ⊓ π.ker = ⊥ ∧
      (∀ s : ↥S, π s = eS s) ∧ Group.IsPerfect ↥S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine.exists_section_lift_of_splits
    hπ hker hLperf hLx e (Q := fun n => ¬ 2 ∣ n) ?_ h2 ?_
  · exact fun {m n} hmn hn h => hn (h.trans hmn)
  · intro E _ _ ρ hρ hcen hQ
    exact CFSG.SeitzReduction.LinearPilot.sl_exists_section_of_coprime
      (m := 2) (F := K) (p := 2) (E := E) hρ hcen hQ

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
