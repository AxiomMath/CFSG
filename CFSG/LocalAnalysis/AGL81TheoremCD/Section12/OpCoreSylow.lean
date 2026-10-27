module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {Q H : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    pCoreOf p H ≤ Q := by
  obtain ⟨Q', hQ'⟩ := hQ
  rw [pCoreOf, ← hQ']
  exact Subgroup.map_mono
    (IsPGroup.le_sylow_of_normal (p := p) (N := CFSG.pCore p H)
      (CFSG.pCore_isPGroup (p := p) (G := ↥H)) Q')

theorem pCoreOf_le_of_isSylowOf_le {p : ℕ} [Fact p.Prime] {Q H M : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hQM : Q ≤ M) :
    pCoreOf p H ≤ M :=
  (pCoreOf_le_of_isSylowOf hQ).trans hQM

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
