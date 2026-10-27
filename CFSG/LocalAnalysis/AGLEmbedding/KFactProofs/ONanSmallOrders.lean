module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open CFSG.Sporadic.Schreier CFSG.Sporadic.J4

theorem card_of_isSmallLinTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    (hK : IsSmallLinTwo p K) : Nat.card K = p ^ 2 * (((p ^ 2) ^ 2 - 1) / 2) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  rw [Nat.card_congr (e.trans e₂).toEquiv]
  exact CFSG.SectionRank.OddCover.card_psl_two hp hp2 (GaloisField.card p 2 (by norm_num))

theorem card_mul_gcd_of_isSmallUnitary {p : ℕ} {K : Type} [Group K] [Finite K]
    (hK : IsSmallUnitary p K) :
    Nat.card K * Nat.gcd 3 (p + 1) = p ^ 3 * (p ^ 3 + 1) * (p ^ 2 - 1) := by
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := hK
  have hfe : d.1.fieldExponent = 1 := by
    rw [hd]
    simpa using hqe
  have h := kFactUnitaryOrder K p d ⟨q, hqp, hd⟩ ⟨e⟩
  rw [hfe, pow_one] at h
  exact h

theorem card_of_isAltTwoP {p : ℕ} (hp : p.Prime) {K : Type} [Group K] (hK : IsAltTwoP p K) :
    Nat.card K = (2 * p).factorial / 2 := by
  obtain ⟨e⟩ := hK
  have : Nontrivial (Fin (2 * p)) := Fin.nontrivial_iff_two_le.2 (by have := hp.two_le; omega)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem card_of_isMcL
    {K : Type} [Group K] (hs : IsSimpleGroup K) (hK : IsSporadicGroup .McL K) :
    Nat.card K = 898128000 := by
  obtain ⟨e⟩ := nonempty_equiv_mclP hs hK
  rw [Nat.card_congr e.toEquiv, card_mclP]

theorem card_of_isJ4
    {K : Type} [Group K] (hs : IsSimpleGroup K) (hK : IsSporadicGroup .J4 K) :
    Nat.card K = 86775571046077562880 := by
  obtain ⟨e⟩ := nonempty_equiv_j4 hs hK
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (seedEquiv j4Facts.mat).symm.toEquiv]
  exact card_J4

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
