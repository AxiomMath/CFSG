module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltPerm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltPerm

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem eq_bot_of_normalizes_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K)
    (S : Sylow p K) (U : Subgroup K) (hU : ¬ p ∣ Nat.card U)
    (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨e⟩ := hK
  set ι := altPermEmbed e with hι'
  have hι : Function.Injective ι := altPermEmbed_injective e
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e S
  set E : Subgroup (Perm (Fin (2 * p))) := (S : Subgroup K).map ι with hE
  obtain ⟨a₁, ha₁, a₂, ha₂, O₁, O₂, hO₁, hO₂, hd, hm₁, hm₂⟩ :=
    CFSG.AGLEmbeddingD2.exists_cycles_of_isElemAbelian hp hp2 (by omega) hEab hEcard
  have hnorm : ∀ g ∈ E, g ∈ Subgroup.normalizer ((U.map ι : Subgroup (Perm (Fin (2 * p)))) :
      Set (Perm (Fin (2 * p)))) := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨s * u * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSU hs) u).1 hu, by simp⟩
    · intro hh
      obtain ⟨u, hu, hu'⟩ := hh
      refine ⟨s⁻¹ * u * s, ?_, ?_⟩
      · simpa using (Subgroup.mem_normalizer_iff.1 (hSU (inv_mem hs)) u).1 hu
      · have : h = (ι s)⁻¹ * (ι s * h * (ι s)⁻¹) * ι s := by group
        rw [this, ← hu']
        simp
  have hU' : ¬ p ∣ Nat.card (U.map ι) := by
    rwa [Subgroup.card_map_of_injective hι]
  have hbot := eq_bot_of_normalized_by_cycles_coprime hp (Fintype.card_fin (2 * p)) hU'
    (hEab.2 a₁ ha₁) (hEab.2 a₂ ha₂) hO₁ hO₂ hd hm₁ hm₂ (hnorm a₁ ha₁) (hnorm a₂ ha₂)
  exact (Subgroup.map_eq_bot_iff_of_injective U hι).1 hbot

theorem noTwo_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K) (S : Sylow p K)
    (U : Subgroup K) (hU : IsPGroup 2 U)
    (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  refine eq_bot_of_normalizes_of_isAltTwoP hp hp2 hK S U ?_ hSU
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hk]
  intro hpd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (Nat.Prime.dvd_of_dvd_pow hp hpd))

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
