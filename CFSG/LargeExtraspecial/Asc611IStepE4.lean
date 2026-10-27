module

public import CFSG.LargeExtraspecial.Asc611IStepE3
import all CFSG.Fischer.F4
public import CFSG.LargeExtraspecial.Asc611IStepE2

public section

namespace CFSG.LargeExtraspecial.Asc611I

open Subgroup Matrix CFSG.Fischer CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ} {e : SUid frob m} {U : Subgroup (PG m)}

theorem herm_self_shift_eq_zero (S : Setup e U) (hEU : (QuotientGroup.mk e : PG m) ∈ U)
    {k : SUid frob m} (hk : (QuotientGroup.mk k : PG m) ∈ U) (hke : k * e = e * k)
    (hkN : ∀ x, invN e (k • x) = invN e x) (hker : ∀ v, invN e v = 0 → k • v = v)
    (hperp : ∀ x b, invN e b = 0 → herm frob (k • x + x) b = 0) {a : Fin m → K}
    (ha : herm frob a a = 0) (haN : herm frob a (invN e a) = 0) :
    herm frob a (k • a + a) = 0 := by
  have he := S.invol
  by_contra hβ
  set s := k • a + a with hs
  have hNs : invN e s = 0 := by rw [hs, invN_add, hkN, vec_add_self]
  have hss : herm frob s s = 0 := hperp a s hNs
  have hka : k • a = a + s := by
    rw [hs, add_comm (k • a) a, ← add_assoc, vec_add_self, zero_add]
  have hperpa : ∀ b, invN e b = 0 → herm frob s b = 0 := fun b hb => hperp a b hb
  clear_value s
  have hβ1 : herm frob a s = 1 := by
    have h1 : herm frob (k • a) (k • a) = herm frob a a := herm_smul_smul frob k a a
    rw [hka, herm_add_left, herm_add_right, herm_add_right, ha, hss,
      herm_conj frob frob_frob a s] at h1
    have h2 : herm frob a s + frob (herm frob a s) = 0 := by linear_combination h1
    exact ((add_frob_eq_zero_iff _).1 h2).resolve_left hβ
  have hγ : herm frob (k • a) a = 1 := by
    rw [hka, herm_add_left, ha, zero_add, herm_conj frob frob_frob a s, hβ1, map_one]
  have hu₀ := mk_comm_mem S.normal hk (cv_comm he ha haN)
  have hG2 : ∀ x, (k * cv e a * k⁻¹ * (cv e a)⁻¹) • x = x + herm frob s x • invN e a +
      herm frob (invN e a) x • s + (1 * herm frob (invN e a) x) • invN e a := by
    intro x
    rw [comm_cv_smul he hke ha haN (hkN a) x, hγ, ← hs]
  obtain ⟨ta, hta⟩ := exists_invN_eq_of_perp he hperpa
  have hHa : herm frob a (invN e ta) = 1 := by rw [hta]; exact hβ1
  have hHta : herm frob ta (invN e a) = 1 := by rw [herm_invN_swap he a ta, hHa, map_one]
  rcases herm_invN_self he ta with h0 | h0
  ·
    have hz0 : herm frob (a + ω • ta) (invN e (a + ω • ta)) = 1 := by
      rw [invN_add, invN_smul, herm_add_left, herm_add_right, herm_add_right, herm_smul_left,
        herm_smul_left, herm_smul_right, herm_smul_right, haN, hHa, hHta, h0]
      simp only [mul_one, mul_zero, add_zero, zero_add]
      exact omega_add_frob
    have hz1 : herm frob (a + (ω * ω) • ta) (invN e (a + (ω * ω) • ta)) = 1 := by
      rw [invN_add, invN_smul, herm_add_left, herm_add_right, herm_add_right, herm_smul_left,
        herm_smul_left, herm_smul_right, herm_smul_right, haN, hHa, hHta, h0, map_mul,
        frob_omega]
      linear_combination (ω * ω + ω) * two_eq_zero
    have hz01 : herm frob (a + ω • ta) (invN e (a + (ω * ω) • ta)) = 0 := by
      rw [invN_add, invN_smul, herm_add_left, herm_add_right, herm_add_right, herm_smul_left,
        herm_smul_left, herm_smul_right, herm_smul_right, haN, hHa, hHta, h0, frob_omega]
      linear_combination AS35N.omega_sq_add
    obtain ⟨q₀, q₁, hN0, hN1, F2⟩ := exists_frame_two he hz0 hz1 hz01
    have hN0' : invN e q₀ = invN e a + ω • s := by rw [hN0, invN_add, invN_smul, hta]
    have hN1' : invN e q₁ = invN e a + (ω * ω) • s := by rw [hN1, invN_add, invN_smul, hta]
    have hact := actsBy_m0_of hN0' hN1' hG2
    refine false_of_frame2 S F2 hu₀ m0F (fun r hr => m0F_snoc hr) hact ?_ ?_ ?_
    · intro hno
      exact false_of_chain0e S F2 hEU (actsBy_one_e he F2 hno) hu₀ hact chainF_r2_M0
        (by decide)
    · intro q F3 hno3 hact3
      exact false_of_chain2e S F3 hEU (actsBy_one_e he F3 hno3) hu₀ hact3
        (c₁ := ![0, 1, 1]) (c₂ := ![1, 0, 1]) (by decide) (by decide) chainF_r3_M0 (by decide)
    · exact ⟨![0, 1, 0, 1], ![1, 1, 1, 1], ![1, 0, 1, 0], ![1, 0, 1, 0], by decide, by decide,
        by decide, chainF_r4_M0, by decide⟩
  ·
    have hz0 : herm frob (a + ta) (invN e (a + ta)) = 1 := by
      rw [invN_add, herm_add_left, herm_add_right, herm_add_right, haN, hHa, hHta, h0]
      linear_combination (1 : K) * two_eq_zero
    have hz01 : herm frob (a + ta) (invN e ta) = 0 := by
      rw [herm_add_left, hHa, h0]
      exact add_self_K 1
    obtain ⟨q₀, q₁, hN0, hN1, F2⟩ := exists_frame_two he hz0 h0 hz01
    have hN0' : invN e q₀ = invN e a + s := by rw [hN0, invN_add, hta]
    have hN1' : invN e q₁ = s := by rw [hN1, hta]
    have hact := actsBy_hp_of hN0' hN1' hG2
    refine false_of_frame2 S F2 hu₀ hpF (fun r hr => hpF_snoc hr) hact ?_ ?_ ?_
    · intro hno
      refine false_of_rank_two_hp S hk hkN hker hperp (a := a) F2 hno ?_ fun y => ?_
      · rw [invN_add, hN0', hN1', add_assoc, vec_add_self, add_zero]
      · rw [herm_shift_symm hkN hperp a y, ← hs, ← hta, herm_invN_left he,
          herm_invN_congr_left he (show invN e ta = invN e q₁ by rw [hN1])]
    · intro q F3 hno3 hact3
      exact false_of_chain0e S F3 hEU (actsBy_one_e he F3 hno3) hu₀ hact3 chainF_r3_HP
        (by decide)
    · exact ⟨![0, 1, 0, 1], ![1, 1, 1, 1], ![1, wF, 1, wF], ![1, wF, 1, wF], by decide,
        by decide, by decide, chainF_r4_HP, by decide⟩

end CFSG.LargeExtraspecial.Asc611I
