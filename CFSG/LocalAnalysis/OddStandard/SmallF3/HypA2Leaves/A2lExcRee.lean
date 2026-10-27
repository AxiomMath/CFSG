module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRows

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

@[expose] def a2lFixedQuasi : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    OddLieType S → CatLeaf.FixedTwoComponentsQuasisimple S

theorem a2l_chev3On_ree (hCL2 : HypA2.ClosureFieldExp) (hQ : a2lFixedQuasi) :
    a2lChev3On fun S _ => ∃ f : ℕ, LieModel S .twistedG2 0 3 f := by
  intro K _ _ hK h2 _ hnF ⟨f, hf⟩ σ hσ X hXσ hXc hXF
  exfalso
  obtain ⟨σ', P, hPF, hF⟩ := a2l_exc_reduce hK hnF hσ hXσ hXc hXF
  haveI : IsSimpleGroup (K ⧸ center K) := hK.2.1
  have hq := hQ (K ⧸ center K) hK.2.2
    ⟨.twistedG2, 0, 3, f, Nat.prime_three, by norm_num, hf.admissible, hf⟩
  have hc := a2l_fieldExp_of_fStar hCL2 hq hf hPF hF
  obtain ⟨-, -, -, -, ⟨m, hm⟩, h3⟩ := hf.admissible
  omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
