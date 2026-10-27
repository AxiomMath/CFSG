module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
public import CFSG.LocalAnalysis.RankThreeUC.Section5.LargeElementaryDerivedContainment
public import CFSG.LocalAnalysis.RankThreeUC.Section5.AlphaScriptQ.AlphaScriptQ

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryPrimeExclusionFromRank

open CFSG.LocalAnalysis.RankThreeUC.Section5

theorem p_not_mem_piOf {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (hEA : CFSG.Open.IsElemAbelian p P) (hlarge : 3 < CFSG.Open.pRank p P) :
    p ∉ piOf B := by
  intro hpi
  have hder : P ≤ commutator G :=
    LargeElementaryDerivedContainment.derived_le hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hEA (by omega)
  have hQ := AlphaScriptQ.mem_scriptQ hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hder
  have hα := AlphaScriptQ.mem_alpha hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction hder
  exact hc.not_concl (Or.inr (Or.inl ⟨p, ⟨hpi, hα⟩, P, hQ, hlarge⟩))

end CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryPrimeExclusionFromRank
