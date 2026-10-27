module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
private theorem pQuotHom_injective {S : Subgroup Ω} (hcore : GLAPPrimeCore 3 ↥S = ⊥) :
    Function.Injective (pQuotHom 3 S) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)).ker = ⊥
  rw [QuotientGroup.ker_mk', hcore]

private theorem eq_one_of_mem_center {S : Subgroup Ω} {c : PQuot 3 S}
    (hc : c ∈ Subgroup.center (PQuot 3 S)) (hc2 : c * c = 1) : c = 1 := by
  obtain ⟨k, hk⟩ := I2611.isPGroup_center_pQuot' Nat.prime_three S ⟨c, hc⟩
  have hck : c ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  rwa [hm, pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at hck

omit [Finite Ω] in
private theorem mem_center_of_chevQuotHom_eq {S : Subgroup Ω} {a b : ↥S}
    (h : chevQuotHom 3 S a = chevQuotHom 3 S b) :
    (pQuotHom 3 S a)⁻¹ * pQuotHom 3 S b ∈ Subgroup.center (PQuot 3 S) := by
  have h' : (QuotientGroup.mk (pQuotHom 3 S a) : PSimple 3 S) =
      QuotientGroup.mk (pQuotHom 3 S b) := h
  exact QuotientGroup.eq.1 h'

private theorem mul_self_eq_one_of_commute {P : Type*} [Group P] {a c : P}
    (hac : a * c = c * a) (ha : a * a = 1) (h : a * c * (a * c) = 1) : c * c = 1 :=
  calc c * c = a * a * (c * c) := by rw [ha, one_mul]
    _ = a * (a * c) * c := by group
    _ = a * (c * a) * c := by rw [hac]
    _ = a * c * (a * c) := by group
    _ = 1 := h

theorem lift_fixed_involution {S B : Subgroup Ω} (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hBN : B ≤ Subgroup.normalizer (S : Set Ω)) {v : PSimple 3 S} (hv2 : v * v = 1)
    (hv1 : v ≠ 1)
    (hvB : ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (S : Set Ω), chevAut 3 S ⟨b, hb⟩ v = v) :
    ∃ z ∈ S, z * z = 1 ∧ z ≠ 1 ∧ ∀ b ∈ B, b * z = z * b := by
  have hinj := pQuotHom_injective hcore
  obtain ⟨s, hs⟩ := chevQuotHom_surjective 3 S v
  have hss : pQuotHom 3 S (s * s) ∈ Subgroup.center (PQuot 3 S) := by
    have h1 : chevQuotHom 3 S 1 = chevQuotHom 3 S (s * s) := by rw [map_one, map_mul, hs, hv2]
    simpa using mem_center_of_chevQuotHom_eq h1
  obtain ⟨k, hk⟩ := I2611.isPGroup_center_pQuot' Nat.prime_three S ⟨_, hss⟩
  have hk' : pQuotHom 3 S (s * s) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set z : ↥S := s ^ 3 ^ k with hz
  have hz2 : z * z = 1 := hinj (by
    rw [map_mul, map_one, ← map_mul, hz, ← (Commute.refl s).mul_pow, map_pow, hk'])
  have hzv : chevQuotHom 3 S z = v := by
    obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    rw [hz, map_pow, hs, hm, pow_succ, pow_mul, sq, hv2, one_pow, one_mul]
  refine ⟨z, z.2, by exact_mod_cast congrArg Subtype.val hz2, fun h1 => hv1 ?_, fun b hb => ?_⟩
  · rw [← hzv, show z = 1 from Subtype.ext h1, map_one]
  set w : ↥S := S.normalizerMonoidHom ⟨b, hBN hb⟩ z with hw
  have hzw : chevQuotHom 3 S z = chevQuotHom 3 S w := by
    rw [hw, ← chevAut_chevQuotHom, hzv, hvB b hb (hBN hb)]
  obtain ⟨c, hc⟩ : ∃ c, c = (pQuotHom 3 S z)⁻¹ * pQuotHom 3 S w := ⟨_, rfl⟩
  have hcZ : c ∈ Subgroup.center (PQuot 3 S) := hc ▸ mem_center_of_chevQuotHom_eq hzw
  have hw2 : w * w = 1 := by rw [hw, ← map_mul, hz2, map_one]
  have hpw : pQuotHom 3 S w = pQuotHom 3 S z * c := by rw [hc, mul_inv_cancel_left]
  have hc2 : c * c = 1 := mul_self_eq_one_of_commute (a := pQuotHom 3 S z)
    (Subgroup.mem_center_iff.1 hcZ _) (by rw [← map_mul, hz2, map_one])
    (by rw [← hpw, ← map_mul, hw2, map_one])
  have hwz : w = z := hinj (by rw [hpw, eq_one_of_mem_center hcZ hc2, mul_one])
  have h3 : b * (z : Ω) * b⁻¹ = z := congrArg Subtype.val hwz
  calc b * (z : Ω) = b * z * b⁻¹ * b := by group
    _ = z * b := by rw [h3]

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
