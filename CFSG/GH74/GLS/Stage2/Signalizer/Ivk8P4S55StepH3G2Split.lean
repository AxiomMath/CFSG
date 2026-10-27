module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2LinAlg
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.Bender.Thm1


variable {K : Type} [Field K]

theorem exists_rgroup_of_inner_split [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]
    (h3 : 3 ∣ Nat.card K - 1) {x : ↥(adjointGroup Tag.G2 K)} (hx : x ^ 3 = 1) :
    ∃ E : Subgroup ↥(adjointGroup Tag.G2 K), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ z ∈ E, MulAut.conj x z ∈ E := by
  classical
  obtain ⟨ω, hω1, hω3⟩ : ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
    have h3' : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      exact h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3'
    refine ⟨(u : K), fun h => ?_, ?_⟩
    · have : u = 1 := Units.ext h
      rw [this, orderOf_one] at hu
      omega
    · have := pow_orderOf_eq_one u
      rw [hu] at this
      exact congrArg Units.val this |>.trans (by simp)
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h0 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hω1)
  obtain ⟨ι, hι, -⟩ := exists_a2Hom_injective (K := K)
  have hEp : IsPGroup 3 ↥(zpowers x) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (x ^ n) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨y, hy⟩ := exists_conj_le_range_of_three_dvd_sub_one h3 ι hι (zpowers x) hEp
  obtain ⟨a, ha⟩ := hy (mem_map_of_mem _ (mem_zpowers x))
  have ha3 : a ^ 3 = 1 := by
    apply hι
    rw [map_pow, map_one, ha]
    change (y * x * y⁻¹) ^ 3 = 1
    rw [conj_pow, hx, mul_one, mul_inv_cancel]
  obtain ⟨R, hRr, hR1, hRn⟩ := exists_pGroup_normalized_of_commuting_cube_one r ω hω (zpowers a)
    (by
      rintro _ ⟨n, rfl⟩
      change (a ^ n) ^ 3 = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow])
    (by
      rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
      exact (Commute.zpow_zpow_self a n m).eq)
  refine ⟨(R.map ι).map (MulAut.conj y⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · intro h
    apply hR1
    rw [Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj y⁻¹).injective,
      Subgroup.map_eq_bot_iff_of_injective _ hι] at h
    exact h
  · exact (hRr.map ι).map _
  · rintro _ ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩
    have haρ : a * ρ * a⁻¹ ∈ R := (mem_normalizer_iff.mp (hRn (mem_zpowers a)) ρ).mp hρ
    refine ⟨ι (a * ρ * a⁻¹), ⟨_, haρ, rfl⟩, ?_⟩
    have hyx : y * x * y⁻¹ = ι a := ha.symm
    have hx' : x = y⁻¹ * ι a * y := by rw [← hyx]; group
    change y⁻¹ * ι (a * ρ * a⁻¹) * y⁻¹⁻¹ = x * (y⁻¹ * ι ρ * y⁻¹⁻¹) * x⁻¹
    rw [hx', map_mul, map_mul, map_inv]
    group

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2
