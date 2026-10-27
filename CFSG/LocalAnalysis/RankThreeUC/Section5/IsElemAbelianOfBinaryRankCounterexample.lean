module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
public import CFSG.LocalAnalysis.RankThreeUC.Section5.IsElemAbelianOrIsExtraspecial
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialBinaryActionAlternatives
public import CFSG.LocalAnalysis.RankThreeUC.Section5.DerivedContainment.DerivedContainment
public import CFSG.LocalAnalysis.RankThreeUC.Section5.AlphaScriptQ.AlphaScriptQ

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_binary_rank_counterexample {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    CFSG.Open.IsElemAbelian p P := by
  rcases isElemAbelian_or_isExtraspecial hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction with h | hext
  · exact h
  · exfalso
    have hder := DerivedContainment.derived_le hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hext
    obtain ⟨_, h58⟩ := extraspecialBinaryActionAlternatives hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hext
    apply hc.not_concl
    rcases h58 with ⟨hpi, hr⟩ | ⟨_, _, hM⟩
    · exact Or.inr (Or.inl ⟨p, ⟨hpi, AlphaScriptQ.mem_alpha hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hder⟩, P,
        AlphaScriptQ.mem_scriptQ hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hder, hr⟩)
    · exact Or.inl hM

end Section5
end CFSG.LocalAnalysis.RankThreeUC
