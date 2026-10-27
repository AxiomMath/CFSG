module

import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open KFactProofs.SmallIdent
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

variable {K : Type} [Group K] [Finite K] {p : ℕ}

omit [Finite K] in
theorem nonempty_mulEquiv_psl2GF_of_pair [Fact p.Prime]
    (hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)) : Nonempty (K ≃* PSL2GF p 2) := by
  rcases hLA with ⟨d, hd, ⟨e₁⟩⟩ | ⟨rfl, ⟨e₁⟩⟩
  · obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
    exact ⟨e₁.trans e₂⟩
  · have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 3 2) = 9 := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
      norm_num
    obtain ⟨e₂⟩ :=
      unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
    exact ⟨e₁.trans e₂.symm⟩

theorem sylow_facts_of_pair [Fact p.Prime] (hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K))
    (T : Sylow p K) : Nat.card (T : Subgroup K) = p ^ 2 ∧ ∀ t ∈ (T : Subgroup K), t ^ p = 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_pair hLA
  have hfs : Function.Surjective (e : K →* PSL2GF p 2) := e.surjective
  have hT'eq : ((T.mapSurjective hfs : Sylow p (PSL2GF p 2)) : Subgroup (PSL2GF p 2)) =
      (T : Subgroup K).map e.toMonoidHom := Sylow.coe_mapSurjective hfs T
  obtain ⟨hT'el, hT'card⟩ := psl2GF_sylow p 2 (by norm_num) (T.mapSurjective hfs)
  refine ⟨by rw [← hT'card, hT'eq, Subgroup.card_map_of_injective e.injective], fun t ht => ?_⟩
  have h1 : e t ∈ ((T.mapSurjective hfs : Sylow p (PSL2GF p 2)) : Subgroup (PSL2GF p 2)) := by
    rw [hT'eq]
    exact ⟨t, ht, rfl⟩
  exact e.injective (by rw [map_pow, hT'el.2 _ h1, map_one])

end CFSG.AGLEmbedding
