module

public import CFSG.ClassicalInvolution.Asc77.AscT3CoreInvol
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Balance.FuzzyAdjAxis

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_fixed_involution {N₀ T : Subgroup G} {u : G} (hT : IsPGroup 2 T)
    (huN : u ∈ N₀) (hu : u * u = 1) (hTN : T ≤ Subgroup.normalizer (N₀ : Set G))
    (hcomm : ∀ x ∈ T, ⁅x, u⁆ ∈ oddCoreOf N₀) :
    ∃ q ∈ N₀, ∀ x ∈ T, x * (q * u * q⁻¹) * x⁻¹ = q * u * q⁻¹ := by
  set O := oddCoreOf N₀ with hO
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard N₀
  have hOle : O ≤ N₀ := oddCoreOf_le_self N₀
  have huN' : u ∈ Subgroup.normalizer (N₀ : Set G) := Subgroup.le_normalizer huN
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hAN : ∀ a ∈ T, ∀ n ∈ O, a * n * a⁻¹ ∈ O := fun a ha n hn =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (hTN ha) hn
  have hx : ∀ a ∈ T, u⁻¹ * (a * u * a⁻¹) ∈ O := by
    intro a ha
    have h1 := mem_normalizer_oddCoreOf_of_mem_normalizer
      ((Subgroup.normalizer _).inv_mem huN') (hcomm a ha)
    have e : u⁻¹ * (a * u * a⁻¹) = u⁻¹ * ⁅a, u⁆ * u⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1
  obtain ⟨n, hn, hfix⟩ := Balance.Bootstrap.exists_fixed_mem_coset_of_isPGroup hT hOodd hAN hx
  set h : G := u * n with hh
  have hhh : h * h ∈ O := by
    have e : h * h = (u * n * u⁻¹) * n := by rw [hh, hui]; group
    rw [e]
    exact O.mul_mem (mem_normalizer_oddCoreOf_of_mem_normalizer huN' hn) hn
  have hkodd : Odd (orderOf (h * h)) :=
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hhh)
  obtain ⟨j, hj⟩ := hkodd
  set t'' : G := h ^ orderOf (h * h) with ht''
  have ht''sq : t'' * t'' = 1 := by
    rw [ht'', ← (Commute.refl h).mul_pow]
    exact pow_orderOf_eq_one (h * h)
  have ht''eq : t'' = h * (h * h) ^ j := by
    rw [ht'', hj, pow_succ', pow_mul, sq]
  have hut : u * t'' ∈ O := by
    have huh : u * h = n := by rw [hh, ← mul_assoc, hu, one_mul]
    have : u * t'' = n * (h * h) ^ j := by
      rw [ht''eq, ← mul_assoc, huh]
    rw [this]
    exact O.mul_mem hn (O.pow_mem hhh j)
  have hodd2 : Odd (orderOf (u * t'')) :=
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hut)
  obtain ⟨k, hk⟩ := T3Core.exists_conj_of_mul_mem_odd hu ht''sq hodd2
  have hqO : (u * t'') ^ k ∈ O := O.pow_mem hut k
  refine ⟨(u * t'') ^ k, hOle hqO, fun x hxT => ?_⟩
  rw [hk]
  have h1 : x * h * x⁻¹ = h := hfix x hxT
  calc x * t'' * x⁻¹ = x * h ^ orderOf (h * h) * x⁻¹ := rfl
    _ = (x * h * x⁻¹) ^ orderOf (h * h) := conj_pow.symm
    _ = t'' := by rw [h1]

end Fixed

end CFSG.ClassicalInvolution.Asc77.T3CII
