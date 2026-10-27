module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel

public section

namespace CFSG.AGLEmbedding

theorem card_of_isSmallUnitary_three {K : Type} [Group K] (h : IsSmallUnitary 3 K) :
    Nat.card K = 6048 := by
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨he⟩⟩ := h
  have hd : IsUnitaryIndex 3 d := ⟨q, hqp, hdq⟩
  obtain ⟨-, -, -, F, _, _, J, -, -, -, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd ⟨he⟩)
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hord := kFactUnitaryOrder K 3 d hd ⟨he⟩
  obtain ⟨q', hq'p, hq'd, hfe, -⟩ := hd.exists_eq
  have hq'e : q'.exponent = 1 := by
    have : q' = q := by
      have h1 : TauCeti.LieTypeIndex.twistedA 2 q' = TauCeti.LieTypeIndex.twistedA 2 q :=
        hq'd.symm.trans hdq
      injection h1
    rw [this, hqe]
  rw [hfe, hq'e] at hord
  norm_num at hord
  omega

theorem card_of_isLinThreeFour {K : Type} [Group K] (h : IsLinThreeFour K) :
    Nat.card K = 20160 := by
  obtain ⟨ε⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour h
  rw [Nat.card_congr ε.toEquiv]
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk

theorem card_of_isSmallLinTwo_three {K : Type} [Group K] (h : IsSmallLinTwo 3 K) :
    Nat.card K = 360 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd, ⟨e₁⟩⟩ := h
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  rw [Nat.card_congr (e₁.trans e₂).toEquiv]
  have hk : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  rw [CFSG.SectionRank.OddCover.card_psl_two Nat.prime_three (by norm_num) hk]
  norm_num

theorem kFactSmallThreeOrders : KFactSmallThreeOrders := fun _ _ =>
  ⟨card_of_isSmallUnitary_three, card_of_isLinThreeFour, card_of_isSmallLinTwo_three⟩

end CFSG.AGLEmbedding
