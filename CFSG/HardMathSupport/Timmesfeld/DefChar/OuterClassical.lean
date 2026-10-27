module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterA1
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterC
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterTwistedA
public import CFSG.HardMathSupport.Timmesfeld.DefChar.OuterOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.Automorphisms.LinearHigherCoprime
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.HardMathSupport.Timmesfeld.Coordinator (DefCharOuterRank)

@[expose] def DefCharFamily.IsClassical : DefCharFamily → Prop
  | .A | .twistedA | .B | .C | .D | .twistedD => True
  | _ => False

theorem defCharOuterRankFamA : DefCharOuterRankFam .A := by
  intro S _ _ hS hnab idx hk hidx p hp hp2 hch D hD hcard
  obtain ⟨r, q, hrq⟩ := hk
  have hv := idx.2
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hrq] at hv
  have hr1 : 1 ≤ r := hv.1.1
  by_cases hr : r = 1
  · exact defCharOuterRankFamA_one S hS hnab idx ⟨q, hrq.trans (by rw [hr])⟩ hidx p hp hp2 hch D
      hD hcard
  · exact defCharOuterRankFamA_of_two_le S hS hnab idx ⟨r, q, hrq, by omega⟩ hidx p hp hp2 hch D
      hD hcard

theorem defCharOuterRankFam_classical (k : DefCharFamily) (hk : k.IsClassical) :
    DefCharOuterRankFam k := by
  cases k with
  | A => exact defCharOuterRankFamA
  | twistedA => exact defCharOuterRankFamTwistedA
  | B => exact defCharOuterRankFamB
  | C => exact defCharOuterRankFamC
  | D => exact defCharOuterRankFamD
  | twistedD => exact defCharOuterRankFamTwistedD
  | _ => exact absurd hk (by simp [DefCharFamily.IsClassical])

theorem defCharOuterRank_of_exceptional
    (h : ∀ k : DefCharFamily, ¬ k.IsClassical → DefCharOuterRankFam k) : DefCharOuterRank :=
  defCharOuterRank_of_families fun k => by
    classical
    by_cases hk : k.IsClassical
    · exact defCharOuterRankFam_classical k hk
    · exact h k hk

end CFSG.HardMathSupport.Timmesfeld.DefChar
