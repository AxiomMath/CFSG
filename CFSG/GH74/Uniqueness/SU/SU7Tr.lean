module

public import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.GH74.Uniqueness.SU.SU7Bar

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5

namespace Tr

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}

theorem two_transitive (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) :
    ∀ p₁ ∈ U, ∀ p₂ ∈ U, ∀ q₁ ∈ U, ∀ q₂ ∈ U, p₁ ≠ 1 → p₂ ≠ 1 → p₁ ≠ p₂ → q₁ ≠ 1 → q₂ ≠ 1 →
      q₁ ≠ q₂ → ∃ h ∈ normalizer (U : Set G), h * p₁ * h⁻¹ = q₁ ∧ h * p₂ * h⁻¹ = q₂ := by
  have hJ := Base.j2facts hH hconf hcl
  have hmemZ := Base.mem_Zc_iff hH hconf hcl
  have hxS := Base.x_mem_S hconf
  have hzU : z ∈ U := (hmemZ z).1 hJ.z_mem
  have hz1 := Base.z_ne_one hconf
  obtain ⟨a, haM, haT, hafix⟩ := Bar.exists_fpf hH hconf hcl
  have hUsub : ∀ n ∈ normalizer (U : Set G), ∀ p ∈ U, n * p * n⁻¹ ∈ U :=
    fun n hn p hp => (mem_normalizer_iff.1 hn p).1 hp
  have haU : a ∈ normalizer (U : Set G) := by
    have hconj : ∀ p ∈ U, a * p * a⁻¹ ∈ U := fun p hp =>
      (hmemZ _).1 (Base.mem_Zc_of_normalizer haT ((hmemZ p).2 hp))
    exact Gen.mem_normalizer_of_conj_le hconj
  have hxU : x ∈ normalizer (U : Set G) := hH.normal hxS
  have hU4 : Nat.card U = 4 := by rw [hH.four.2.2]; norm_num
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := (isElemAbelian_iff.1 hH.four.2.1).1
  have hU2 : ∀ a ∈ U, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact (isElemAbelian_iff.1 hH.four.2.1).2 a ha
  have hxz : x * z * x⁻¹ = z := by
    rw [hconf.z_center x hxS]; group
  have hxfix : ∀ p ∈ U, p ≠ 1 → p ≠ z → x * p * x⁻¹ ≠ p := by
    intro p hp hp1 hpz heq
    have h1 : x * p = p * x := by
      have := heq
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    exact hJ.x_not_mem ((hJ.half_central p ((hmemZ p).2 hp) hp1 hpz x hxS).1 h1)
  exact Gen.two_trans hU4 hUc hU2 hUsub haU hxU hzU hz1 hxz hafix hxfix

theorem exists_conj_z (hH : Hyp184 S U M) (hconf : Conf18H S M V x z)
    (hcl : Concl189 S U M x hconf.x_mem) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    ∃ h ∈ normalizer (U : Set G), h * z * h⁻¹ = u := by
  have hJ := Base.j2facts hH hconf hcl
  have hmemZ := Base.mem_Zc_iff hH hconf hcl
  have hzU : z ∈ U := (hmemZ z).1 hJ.z_mem
  have hz1 := Base.z_ne_one hconf
  have hU4 : Nat.card U = 4 := by rw [hH.four.2.2]; norm_num
  obtain ⟨t₁, ht₁, ht₁1, t₂, ht₂, ht₂1, ht₂₁⟩ := Gen.exists_two_ne_one_of_card_four hU4
  have hp₂ : ∃ p ∈ U, p ≠ 1 ∧ p ≠ z := by
    by_cases h : t₁ = z
    · exact ⟨t₂, ht₂, ht₂1, by rw [h] at ht₂₁; exact ht₂₁⟩
    · exact ⟨t₁, ht₁, ht₁1, h⟩
  have hq₂ : ∃ q ∈ U, q ≠ 1 ∧ q ≠ u := by
    by_cases h : t₁ = u
    · exact ⟨t₂, ht₂, ht₂1, by rw [h] at ht₂₁; exact ht₂₁⟩
    · exact ⟨t₁, ht₁, ht₁1, h⟩
  obtain ⟨p, hpU, hp1, hpz⟩ := hp₂
  obtain ⟨q, hqU, hq1, hqu⟩ := hq₂
  obtain ⟨h, hh, h1, -⟩ := two_transitive hH hconf hcl z hzU p hpU u hu q hqU hz1 hp1 hpz.symm hu1 hq1
    hqu.symm
  exact ⟨h, hh, h1⟩

end Tr

end CFSG.GH74.Uniqueness.SU.SU7
