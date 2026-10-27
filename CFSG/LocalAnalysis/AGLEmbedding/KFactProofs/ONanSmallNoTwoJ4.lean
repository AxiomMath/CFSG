module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallNoTwoGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallJ4
public import CFSG.RankThree.PartOne.S11c.J4Plane

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Blueprint CFSG.RankThree.PartOne

theorem noTwo_of_isJ4
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hK : IsSporadicGroup .J4 K) (S : Sylow 11 K) (U : Subgroup K) (hU : IsPGroup 2 U)
    (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hcard, hexp⟩ := sylowCube_of_isJ4 hs hK S
  obtain ⟨e⟩ := nonempty_equiv_j4 hs hK
  obtain ⟨E, hES, hEel, hEcard⟩ := exists_plane_of_exponent (p := 11) (by norm_num)
    (S : Subgroup K) (by rw [hcard]; exact ⟨11, by norm_num⟩) hexp
  set φ : K →* CFSG.Sporadic.J4.J := (e : K →* CFSG.Sporadic.J4.J) with hφ
  have hφinj : Function.Injective φ := e.injective
  have hφsurj : Function.Surjective φ := e.surjective
  have hnorm : ∀ t ∈ E, ∀ u ∈ U, t * u * t⁻¹ ∈ U := fun t ht u hu =>
    (Subgroup.mem_normalizer_iff.1 (hSU (hES ht)) u).1 hu
  have hU' := J4_eq_bot_of_normalized_by_plane (E.map φ) (IsElementaryAbelian.map φ)
    (by rw [Subgroup.card_map_of_injective hφinj, hEcard]) (U.map φ) (hU.map _) (by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      obtain ⟨v, rfl⟩ := hφsurj h
      have e1 : φ t * φ v * (φ t)⁻¹ = φ (t * v * t⁻¹) := by simp
      rw [e1, Subgroup.mem_map_iff_mem hφinj, Subgroup.mem_map_iff_mem hφinj]
      refine ⟨fun hv => hnorm t ht v hv, fun hv => ?_⟩
      have := hnorm t⁻¹ (inv_mem ht) _ hv
      simpa [mul_assoc] using this)
  exact (Subgroup.map_eq_bot_iff_of_injective U hφinj).1 hU'

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
