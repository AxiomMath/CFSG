module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBadCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.J4

open CFSG.Sporadic.J4Schreier CFSG.AGLEmbedding.KFactProofs.SmallIdent
  CFSG.AGLEmbedding.KFactProofs.RankOneCore
open scoped commutatorElement

theorem not_normalizerQuotientComm_j4_model :
    ¬ NormalizerQuotientComm 11 CFSG.Sporadic.J4.J := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨x, y, z, h₁, h₂, c, ⟨P, hP⟩, hext, hcard, hexp, hz, hZ, hn1, hn2, h1x, h1y, -, h2x,
    h2y, -⟩ :=
    R3E_J4_eleven_normalizer_transitivity_and_fixed_dimensions
  subst hz
  set Q : Subgroup CFSG.Sporadic.J4.J := Subgroup.closure ({x, y} : Set CFSG.Sporadic.J4.J)
    with hQ
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hx : x ^ 11 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨x, hxQ⟩ : Q)
    rw [hexp] at this
    simpa using congrArg Subtype.val this
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Q = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcard] at h1
    norm_num at h1
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    have hbot : Subgroup.map Q.subtype (Subgroup.center Q) = ⊥ := by
      rw [hZ, h1]
      exact Subgroup.zpowers_one_eq_bot
    have hc := Subgroup.card_map_of_injective (f := Q.subtype) Q.subtype_injective
      (K := Subgroup.center Q)
    rw [hbot, Subgroup.card_bot, hext.2.2.2] at hc
    norm_num at hc
  have hnot := commutator_not_mem_heisenberg (p := 11) (by norm_num) Q hcard hQ hx hz1
    (hP ▸ hn1) (hP ▸ hn2) 7 3 3 3 2 9 8 6 10 5 3 8 h1x h1y h2x h2y (by decide)
  exact not_normalizerQuotientComm_of_witness P (by rw [hP]; exact hQne) (by rw [hP]; exact hn1)
    (by rw [hP]; exact hn2) (by rw [hP]; exact hnot)

theorem not_normalizerQuotientComm_isJ4
    {L : Type} [Group L] [Finite L]
    (hs : IsSimpleGroup L) (hK : CFSG.AGLEmbedding.IsSporadicGroup .J4 L) :
    ¬ NormalizerQuotientComm 11 L := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_equiv_j4 hs hK
  intro hc
  exact not_normalizerQuotientComm_j4_model (NormalizerQuotientComm.of_mulEquiv e hc)

end CFSG.AGLEmbedding.KFactProofs.SmallBad.J4
