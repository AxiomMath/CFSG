module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.OrbitsCube

open CFSG.Sporadic.J4Schreier CFSG.AGLEmbedding.KFactProofs.SmallIdent
open scoped commutatorElement

theorem normalizerWitness_j4_model :
    ∃ P : Sylow 11 CFSG.Sporadic.J4.J, NormalizerWitness (P : Subgroup CFSG.Sporadic.J4.J) := by
  obtain ⟨x, y, z, h₁, h₂, c, ⟨P, hP⟩, hext, hcard, hexp, hz, hZ, hn1, hn2, h1x, h1y, h1z, h2x,
    h2y, h2z, -⟩ := R3E_J4_eleven_normalizer_transitivity_and_fixed_dimensions
  refine ⟨P, ?_⟩
  rw [hP]
  subst hz
  have hp : Nat.Prime 11 := by norm_num
  set Q : Subgroup CFSG.Sporadic.J4.J := Subgroup.closure ({x, y} : Set CFSG.Sporadic.J4.J)
    with hQ
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hx : x ^ 11 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨x, hxQ⟩ : Q)
    rw [hexp] at this
    simpa using congrArg Subtype.val this
  have hy : y ^ 11 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨y, hyQ⟩ : Q)
    rw [hexp] at this
    simpa using congrArg Subtype.val this
  have hZcard : Nat.card (Subgroup.center Q) = 11 := hext.2.2.2
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    have hbot : Subgroup.map Q.subtype (Subgroup.center Q) = ⊥ := by
      rw [hZ, h1]
      exact Subgroup.zpowers_one_eq_bot
    have hc := Subgroup.card_map_of_injective (f := Q.subtype) Q.subtype_injective
      (K := Subgroup.center Q)
    rw [hbot, Subgroup.card_bot, hZcard] at hc
    norm_num at hc
  have hw := conjWitness_of_data hp hcard hx hy hz1 hn2 8 6 10 5 3 8 h2x h2y (by decide) (by decide)
  exact ⟨h₂, hn2, h₂, hn2, hw.1, hw.2⟩

theorem normalizerWitness_isJ4
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hK : CFSG.AGLEmbedding.IsSporadicGroup .J4 K) (T : Sylow 11 K) :
    NormalizerWitness (T : Subgroup K) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_equiv_j4 hs hK
  obtain ⟨S, hS⟩ := normalizerWitness_j4_model
  have h := @NormalizerWitness.of_sylow_equiv K CFSG.Sporadic.J4.J _ _ _ 11 _
  exact h e hS T

end CFSG.AGLEmbedding.KFactProofs.OrbitsCube
