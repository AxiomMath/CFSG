module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

section Frat

variable {D E : Type} [Group D] [Group E] [Finite D]

theorem frattini_lift (P Q Y : Subgroup D) (hPY : P ≤ Y) (hPn : (P.subgroupOf Y).Normal)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q P) (ρ : D →* E)
    (hρ : P.map ρ = Q.map ρ) (e : D) (he : e ∈ Y) :
    ∃ n ∈ normalizer (Q : Set D), n ∈ Y ∧ ρ n = ρ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQY : Q ≤ Y := hQ.le.trans hPY
  have hQ' : CFSG.ABGLocalTools.IsSylowOf 2 (Q.subgroupOf Y) (P.subgroupOf Y) := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Y).mp ?_
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hQY, inf_of_le_left hPY]
    exact hQ
  obtain ⟨S, hS⟩ := hQ'
  have := hPn
  have hF := Sylow.normalizer_sup_eq_top S
  rw [hS] at hF
  have he' : (⟨e, he⟩ : ↥Y) ∈ (⊤ : Subgroup ↥Y) := trivial
  rw [← hF, ← SetLike.mem_coe, Subgroup.mul_normal] at he'
  obtain ⟨a, ha, b, hb, hab⟩ := he'
  have hbP : b.1 ∈ P := hb
  obtain ⟨q, hq, hqb⟩ : ∃ q ∈ Q, ρ q = ρ b.1 := by
    have : ρ b.1 ∈ P.map ρ := ⟨b.1, hbP, rfl⟩
    rw [hρ] at this
    obtain ⟨q, hq, hqb⟩ := this
    exact ⟨q, hq, hqb⟩
  have hnorm : a.1 ∈ normalizer (Q : Set D) := by
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · intro hd
      exact (Subgroup.mem_normalizer_iff.mp ha ⟨d, hQY hd⟩).mp hd
    · intro hd
      have hdY : d ∈ Y := by
        have h1 : a.1⁻¹ * (a.1 * d * a.1⁻¹) * a.1 ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem a.2) (hQY hd)) a.2
        simpa [mul_assoc] using h1
      exact (Subgroup.mem_normalizer_iff.mp ha ⟨d, hdY⟩).mpr hd
  refine ⟨a.1 * q, Subgroup.mul_mem _ hnorm (Subgroup.le_normalizer hq),
    Y.mul_mem a.2 (hQY hq), ?_⟩
  have hab' : a.1 * b.1 = e := congrArg Subtype.val hab
  rw [map_mul, hqb, ← map_mul, hab']

theorem exists_pow_three_part (ρ : D →* E) (n : D) (h3 : orderOf (ρ n) = 3) :
    ∃ x ∈ Subgroup.zpowers n, IsPGroup 3 ↥(Subgroup.zpowers x) ∧ ρ x = ρ n := by
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3 (by norm_num)
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm
  obtain ⟨k, hk3, hkm⟩ := Nat.chineseRemainder hcop 1 0
  obtain ⟨j, hj⟩ : m ∣ k := (Nat.modEq_zero_iff_dvd).mp hkm
  have hxo : orderOf (n ^ k) ∣ 3 ^ a := by
    apply orderOf_dvd_of_pow_eq_one
    have : k * 3 ^ a = orderOf n * j := by rw [hnm, hj]; ring
    rw [← pow_mul, this, pow_mul, pow_orderOf_eq_one, one_pow]
  refine ⟨n ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers n) k, ?_, ?_⟩
  · obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hxo
    exact IsPGroup.iff_card.mpr ⟨b, by rw [Nat.card_zpowers, hb]⟩
  · rw [map_pow, ← pow_mod_orderOf, h3, hk3]
    exact pow_one _

theorem exists_involution_lift_of_surjective (ρ : D →* E) (hρ : Function.Surjective ρ)
    (hk : Odd (Nat.card ρ.ker)) (v : E) (hv : v * v = 1) :
    ∃ v' : D, v' * v' = 1 ∧ ρ v' = v := by
  let e := QuotientGroup.quotientKerEquivOfSurjective ρ hρ
  obtain ⟨s', hs', hs'e⟩ := exists_involution_lift_quot ρ.ker hk (e.symm v)
    (by rw [← map_mul, hv, map_one])
  refine ⟨s', hs', ?_⟩
  have : e (QuotientGroup.mk' ρ.ker s') = ρ s' := rfl
  rw [← this, hs'e, MulEquiv.apply_symm_apply]

end Frat

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
