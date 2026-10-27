module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma129J : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      ∀ R0 : Subgroup G, S ≤ R0 → IsSylow2Of R0 (secN (secV t S L E)) →
        JElem R0 = secV t S L E

theorem asc82Lemma129_of_J (hJ : Asc82Lemma129J) : Asc82Lemma129 := by
  intro G _ _ t L S z K1 K2 E hctx R0 hSR0 hR0
  have h1 := hJ G t L S z K1 K2 E hctx R0 hSR0 hR0
  exact ⟨h1, sec12_isSylow2Of_top_of_jElem hR0 h1⟩

end CFSG.OddStandard.SmallF3.Omega
