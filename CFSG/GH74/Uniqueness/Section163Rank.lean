module

public import CFSG.GH74.Uniqueness.Section12BenderDict
public import CFSG.LocalAnalysis.RankTwoShapes.SingleInvolutionClass
public import CFSG.GH74.GLS.TwoThin.Rank

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.exists_elemAbelian_eight_le_centralizer
    (S : ZDSetup X Z M) {u : X}
    (hu : orderOf u = 2) (huZ : u ∉ Z) :
    ∃ E : Subgroup X, E ≤ centralizer ({u} : Set X) ∧ Nat.card E = 8 ∧ ∀ e ∈ E, e * e = 1 := by
  obtain ⟨hsimple, -, ⟨z₀, hz₀, hZeq⟩, -⟩ := S.theorem1_unconditional
  have : IsSimpleGroup X := hsimple
  have hnonab : ∃ a b : X, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact S.exists_not_commute h
  have h2 : 2 ≤ CFSG.Assembly.twoRank X := S.two_le_twoRank
  have h3 : 3 ≤ CFSG.Assembly.twoRank X := by
    by_contra hlt
    have heq : CFSG.Assembly.twoRank X = 2 := by omega
    have hconj : IsConj z₀ u :=
      CFSG.RankTwoShapes.involutions_isConj_of_twoRank_eq_two hnonab heq (S.invariant.1 z₀ hz₀) hu
    apply huZ
    rw [hZeq]
    exact hconj
  have hperf : commutator X = ⊤ :=
    CFSG.GH74.GLS.TwoThin.commutator_eq_top_of_simple hsimple hnonab
  have h3c : 3 ≤ CFSG.Open.pRank 2 (centralizer ({u} : Set X)) :=
    CFSG.Assembly.Dichotomy.tt_two_le_pRank_involution_centralizer hperf h3 u hu
  obtain ⟨E, hEC, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (centralizer ({u} : Set X))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 2 h3c
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 hdvd
  refine ⟨K.map E.subtype, (map_subtype_le K).trans hEC, ?_, ?_⟩
  · rw [card_map_of_injective E.subtype_injective, hK]
    norm_num
  · rintro _ ⟨k, -, rfl⟩
    have := hE.2 k k.2
    rw [sq] at this
    exact this

end CFSG.GH74.Uniqueness
