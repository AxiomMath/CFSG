module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargePrimeMain
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 (I294CrossLargePrime
  i294CrossLargePrime_holds)

theorem crossAbelianAt_of_largePrime (h : I294CrossLargePrime) (d : TauCeti.ValidLieTypeIndex) :
    CrossAbelianAt d := by
  intro p hp hp5 hdp L _ _ hs he hl h2 P
  by_contra hP
  have hna : ∃ a b : L, a * b ≠ b * a := by
    by_contra hc
    push_neg at hc
    exact hP ⟨⟨fun a b => Subtype.ext (hc a b)⟩⟩
  have := h p hp hp5 L hs hna d hdp he hl ⟨P, hP⟩
  omega

@[expose] def CrossRankAtPrime (d : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) →
      ∀ y : L, orderOf y = p → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L))

theorem crossAtPrime_of_rankAtPrime (h : I294CrossLargePrime) {d : TauCeti.ValidLieTypeIndex}
    {p : ℕ} (hr : CrossRankAtPrime d p) : CrossAtPrime d p := fun hp hp5 hdp =>
  ⟨crossAbelianAt_of_largePrime h d p hp hp5 hdp, hr hp hp5 hdp⟩

@[expose] def CrossRankE7SevenSplit : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid),
    (7 ∣ q.card - 1 ∨ 7 ∣ q.card + 1) → CrossRankAtPrime ⟨.E7 q, hv⟩ 7

@[expose] def CrossRankE8FiveFour : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid),
    orderOf ((q.card : ℕ) : ZMod 5) = 4 → CrossRankAtPrime ⟨.E8 q, hv⟩ 5

theorem crossE7SevenSplit_of_rank (h : I294CrossLargePrime) (hr : CrossRankE7SevenSplit) :
    CrossE7SevenSplit := fun q hv h7 => crossAtPrime_of_rankAtPrime h (hr q hv h7)

theorem crossE8FiveFour_of_rank (h : I294CrossLargePrime) (hr : CrossRankE8FiveFour) :
    CrossE8FiveFour := fun q hv h4 => crossAtPrime_of_rankAtPrime h (hr q hv h4)

end CFSG.LocalAnalysis.RankFourTheoremC
