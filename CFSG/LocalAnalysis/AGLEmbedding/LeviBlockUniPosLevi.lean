module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosCover
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosGU
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniPosIndex
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockThreeFivesGroup

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

theorem LeviBlock.eq_two_of_mem_uniBlockOrders_u42 {f s ε : ℕ} (hε : ε ≤ 1)
    (h : 25920 ∈ uniBlockOrders f s ε) : s = 2 ∧ ε = 0 := by
  rcases h with ⟨k, hk⟩ | hk
  · exact absurd hk.symm (ordA_ne_u42 (n := k) (f := 2 * f) (by rw [← pow_mul, mul_comm]))
  · have := ((ordTwistedA_eq_u42_iff (f := f) rfl).mp hk.symm).1
    omega

theorem LeviBlock.not_three_pow_five_dvd_of_sylow {X : Type} [Group X] [Finite X]
    (hsyl : ∀ Q : Sylow 3 X, Nat.card (Q : Subgroup X) = 3 ^ 4) : ¬ 3 ^ 5 ∣ Nat.card X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h5
  obtain ⟨Q⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hQ := hsyl Q
  rw [Sylow.card_eq_multiplicity] at hQ
  have hfac : (Nat.card X).factorization 3 = 4 := Nat.pow_right_injective (by norm_num) hQ
  have := (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h5
  omega


theorem kFactCompParabLeviU42On_unitary_two :
    KFactCompParabLeviU42On (IsLieOf (IdxTwistedAAt 2)) := by
  intro Y _ _ L P hCP hC hZ3 O W hOP hPO hO3 hWP hPWO _ _ d' ψ hd' hψ _ hsyl
  left
  obtain ⟨d, hd, ⟨e⟩⟩ := hC
  obtain ⟨K, _, f, t, s, ε, h, ρ, I, g, hε, hI, hq, hρ, hZ, hJ⟩ :=
    exists_uniFlag_dim_of_compParab hCP d (LeviBlock.idxTwistedA_of_at hd) e
  have hf2 : 2 ^ f = 2 := LeviBlock.two_pow_eq_of_at hd fun r₀ q h₀ => (hq r₀ q h₀).1
  have : Finite K := h.finite
  have hmem : 25920 ∈ uniBlockOrders f s ε := by
    obtain ⟨hcard, hsimp⟩ := LeviBlock.catGroup_u42_facts hd'
    have : Finite (CatGroup d') := Finite.of_surjective ψ hψ
    have hnc : ∃ a b : CatGroup d', a * b ≠ b * a :=
      ThreeFives.exists_noncomm_of_simple hsimp (by rw [hcard]; norm_num)
    have := card_mem_of_section hCP.parab.1 ρ hρ (hasLeviBlocks_hypStab h hε hI g hJ) hOP hPO
      hO3 hWP hPWO hnc (by rw [hcard]; norm_num) ψ hψ
    rwa [hcard] at this
  obtain ⟨rfl, rfl⟩ := LeviBlock.eq_two_of_mem_uniBlockOrders_u42 hε hmem
  obtain rfl : f = 1 := Nat.pow_right_injective le_rfl (hf2.trans (by norm_num))
  obtain rfl : t = 1 := by
    by_contra hne
    have ht2 : 2 ≤ t := by
      have := (hI.le t hI.mem).1
      omega
    exact LeviBlock.not_three_pow_five_dvd_of_sylow hsyl
      ((LeviBlock.three_pow_five_dvd_card_hypUnitary_two_zero h).trans
        (LeviBlock.card_hypUnitary_dvd_card_of_flag h hε hI ρ hZ g hJ (Or.inl ht2)))
  have hJ1 : ∀ y, y ∈ (P.subgroupOf L).comap ρ ↔
      y • (g • hypFlag h (1 + 2) 0 1) = g • hypFlag h (1 + 2) 0 1 := by
    intro y
    rw [hJ]
    refine ⟨fun hy => hy 1 (Finset.mem_coe.mpr hI.mem), fun hy i hi => ?_⟩
    obtain rfl : i = 1 := by
      have := hI.le i hi
      omega
    exact hy
  have hZ1 : Subgroup.center ↥L = ⊥ := by
    have hdvd := ToralCensus.card_center_dvd_card_of_surjective hρ hZ
    rw [card_hypScalars h (by norm_num), show Nat.gcd (2 * (1 + 2) + 0) (2 ^ 1 + 1) = 3 by
      norm_num] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (by rw [h3]) hZ3
  obtain ⟨r₀, q, hdq, hqp, hqc⟩ := LeviBlock.exists_eq_twistedA_of_at hd
  obtain ⟨-, hr₀⟩ := hq r₀ q hdq
  have hqe : q.exponent = 1 := by
    rw [TauCeti.PrimePower.card_def, hqp] at hqc
    exact Nat.pow_right_injective le_rfl (hqc.trans (pow_one 2).symm)
  refine ⟨d, ⟨q, hqp, hqe, by rw [hdq, show r₀ = 5 by omega]⟩,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm.trans e⟩, ?_⟩
  rw [Subgroup.relIndex, ← Subgroup.index_comap_of_surjective _ hρ,
    LeviBlock.index_eq_card_hypIsotropicLines h (by norm_num) (by norm_num) g hJ1]
  exact LeviBlock.card_hypIsotropicLines_three_zero h

theorem kFactCompParabLeviU42On_twistedA : KFactCompParabLeviU42On (IsLieOf IdxTwistedA) :=
  kFactCompParabLeviU42On_twistedA_of kFactCompParabLeviU42On_unitary_two

end CFSG.AGLEmbedding
