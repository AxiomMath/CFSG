module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T8S2

section Odd

variable {H : Type} [Group H] [Finite H]

theorem omegaNbr_map_oddE {Λ : Set (Subgroup H)}
    (hsyl : ∀ {L R : Subgroup H}, L ∈ Λ → R ∈ RSet Λ → R ≤ L → IsSylow2In R L)
    {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {K J : Subgroup H}
    (hJ : J ∈ omegaNbr Λ K)
    (hne : J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N)) :
    J.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Λ N) (K.map (QuotientGroup.mk' N)) := by
  obtain ⟨hJΛ, -, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := hsyl hJΛ hT hTJ
  refine ⟨map_mem_quotFamily hJΛ, hne, T.map (QuotientGroup.mk' N),
    mem_RSet_of_isSylow2In (map_mem_quotFamily hJΛ) (isSylow2In_map_mk hN hTsyl),
    Subgroup.map_mono hTJ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact mk_mem_normalizer_map (N := N) (hTN ht)

theorem map_ne_of_noTwinsE {Λ : Set (Subgroup H)}
    {N : Subgroup H} [N.Normal] (hN : Odd (Nat.card N)) {K J : Subgroup H} {z t : H}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hJ : J ∈ omegaNbr Λ K)
    (hzt : z * t = t * z) (hnt : J ∈ twinSet Λ K → J = K) :
    J.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N) := by
  intro heq
  have hzb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN K) hz
  have htb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN J) ht
  rw [heq] at htb
  have hmk : QuotientGroup.mk' N z = QuotientGroup.mk' N t := hzb.eq htb
  have hw : z⁻¹ * t ∈ N := by
    have : QuotientGroup.mk' N (z⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hmk, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hsq : (z⁻¹ * t) ^ 2 = 1 := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.sq
    have hcomm : z⁻¹ * t = t * z⁻¹ := by rw [hzi]; exact hzt
    calc (z⁻¹ * t) ^ 2 = (z⁻¹ * t) * (z⁻¹ * t) := pow_two _
      _ = z⁻¹ * z⁻¹ * (t * t) := by
          rw [mul_assoc, ← mul_assoc t, ← hcomm, mul_assoc, mul_assoc]
      _ = 1 := by rw [hzi, hz.sq, ht.sq, mul_one]
  have hord : orderOf (z⁻¹ * t) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1 : z⁻¹ * t = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact orderOf_eq_one_iff.mp h
    · refine eq_one_of_isPGroup_of_mem_odd hN hw (IsPGroup.of_card (n := 1) ?_)
      rw [Nat.card_zpowers, h]
      norm_num
  have hzteq : z = t := inv_injective (mul_eq_one_iff_eq_inv.mp h1)
  have hJK : J ∈ twinSet Λ K := ⟨hJ.1, z, hz, hzteq ▸ ht⟩
  exact hJ.2.1 (hnt hJK)

end Odd

end T8S2

end CFSG.ClassicalInvolution.Asc77
