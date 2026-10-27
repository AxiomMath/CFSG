module

public import CFSG.LieType.Ree.LargeReeEightLifts
public import CFSG.LieType.Ree.LargeReeCentralTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverCommuting

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime]

@[expose] def exceptionalLeft
    (k : Fin 4 × Bool) : Set (ModGL F4.tag K) :=
  bif k.2 then {g | ∃ d : K, g = fourCoord k.1 0 d} else {g | ∃ c : K, g = fourCoord k.1 c 0}

@[expose] def exceptionalRight
    (k : Fin 4 × Bool) : Set (ModGL F4.tag K) :=
  bif k.2 then {g | ∃ c : K, g = fourCoord k.1 c 0} else {g | ∃ d : K, g = fourCoord k.1 0 d}

theorem exceptionalLeft_subset
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (k : Fin 4 × Bool) :
    exceptionalLeft (K := K) k ⊆ F4.reeFixedPosUnipotent K 1 := by
  obtain ⟨f, _ | _⟩ := k
  · rintro _ ⟨c, rfl⟩
    exact fourCoord_mem hK f c 0
  · rintro _ ⟨d, rfl⟩
    exact fourCoord_mem hK f 0 d

theorem exceptionalRight_subset
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) (k : Fin 4 × Bool) :
    exceptionalRight (K := K) k ⊆ F4.reeFixedPosUnipotent K 1 := by
  obtain ⟨f, _ | _⟩ := k
  · rintro _ ⟨d, rfl⟩
    exact fourCoord_mem hK f 0 d
  · rintro _ ⟨c, rfl⟩
    exact fourCoord_mem hK f c 0

theorem ker_eq_bot_of_reeGamma_eight
    (hK : Nat.card K = 2 ^ (2 * 1 + 1)) {E : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] (η : E →* F4.reeGamma K 1)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) :
    η.ker = ⊥ := by
  have hK' : Nat.card K = F4.prime ^ (2 * 1 + 1) := hK
  have := finite_modGL (τ := F4.tag) (K := K)
  have : Fact F4.prime.Prime := ⟨Nat.prime_two⟩
  refine ker_eq_bot_of_coprime_central_series_of_commute η hη hC h2
    (U := F4.reeFixedPosUnipotent K 1) reeFixedPosUnipotent_le_reeGamma
    isPGroup_reeFixedPosUnipotent_subgroupOf not_dvd_index_reeFixedPosUnipotent
    (odd_card_torus 1 hK) (torusPair 1) (torusPair_mem_reeGamma 1 hK')
    (fun t x hx => torusPair_conj_mem_reeFixedPosUnipotent 1 hK' t hx)
    11 (series 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ exceptionalLeft exceptionalRight
    (exceptionalLeft_subset hK) (exceptionalRight_subset hK) ?_ ?_
  ·
    rw [series, Nat.cast_zero, sub_zero, heightSeries_twelve, inf_bot_eq]
  ·
    rw [series, show (12 : ℤ) - (11 : ℕ) = 1 by norm_num]
    exact inf_eq_left.2 (reeFixedPosUnipotent_le_heightSeries_one 1)
  ·
    intro i _
    rw [series_succ, series_eq]
    exact inf_le_inf_left _ (heightSeries_antitone (by omega))
  ·
    intro i _ t x hx
    rw [series] at hx ⊢
    obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨torusPair_conj_mem_reeFixedPosUnipotent 1 hK' t hxU,
      torusPair_conj_mem_heightSeries 1 t hxV⟩
  ·
    intro i _ x hx g hg
    rw [series_succ] at hx
    rw [series_eq]
    exact commutator_mem_inf_succ hx hg
  ·
    intro i _ x hx
    rw [series_succ] at hx
    rw [series_eq]
    exact sq_mem_inf_succ hx
  ·
    intro i _ x hx hfix
    rw [series_succ] at hx
    rw [series_eq] at hfix ⊢
    obtain ⟨hxU, hxV⟩ := Subgroup.mem_inf.1 hx
    have : CharP K 2 := ‹CharP K F4.prime›
    exact Subgroup.mem_inf.2 ⟨hxU, mem_heightSeries_succ_of_forall_of 1 (odd_card_torus 1 hK)
      (fun β hβ hβp => torusWeight_ne_one_eight hK hβ hβp) hxV
      fun t => (Subgroup.mem_inf.1 (hfix t)).2⟩
  ·
    intro i _ j _ b
    rw [series_succ, series_succ, series_eq 1 i, series_eq 1 j]
    intro h₁ h₂ h₃ h₄ h₅ h₆
    exact form_eq_zero_of_inf_eight hK _ _ b h₁ h₂ h₃ h₄ h₅ fun f c d =>
      ⟨h₆ (f, false) _ ⟨c, rfl⟩ _ ⟨d, rfl⟩, h₆ (f, true) _ ⟨d, rfl⟩ _ ⟨c, rfl⟩⟩
  ·
    rintro ⟨f, _ | _⟩ a y ha hy
    · obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hy
      exact (lift_commute_four hη hC hK f y a ⟨d, hd⟩ ⟨c, hc⟩).symm
    · obtain ⟨d, hd⟩ := ha
      obtain ⟨c, hc⟩ := hy
      exact lift_commute_four hη hC hK f a y ⟨d, hd⟩ ⟨c, hc⟩

end CFSG.LieType.Ree.LargeReeCover

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley ReeTag LargeReeCover

theorem large_Ree_field_eight_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hJ : CFSG.Blueprint.LieModel J .twistedF4 0 2 3) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  swap
  · exact absurd ht (by decide)
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e₀⟩⟩ := id hR
  obtain rfl : a = 1 := by omega
  have hK2 : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [hK]
  have : CharP K F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK2
  obtain ⟨e⟩ := (large_Ree_model_Schreier J 2 3 hR).2.2.2.2.2 1 K hfa hK ⟨e₀⟩
  set η' : E →* F4.reeGamma K 1 := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_reeGamma_eight hK2 η' (e.surjective.comp hη) (hker' ▸ hC)
    (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LieType.Ree
