module

public import CFSG.Open.StatedDefs
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open Polynomial Matrix CFSG.Open

theorem natDegree_eq_one_or_five_of_dvd {K : Type} [Field K] [Finite K]
    (hK : ¬ 5 ∣ Nat.card K) {a : K[X]} (ha : Irreducible a) {c : K} (hc : c ≠ 0)
    (hdvd : a ∣ X ^ 5 - C c) (hodd : Odd a.natDegree) : a.natDegree = 1 ∨ a.natDegree = 5 := by
  have := Fintype.ofFinite K
  obtain ⟨s, hs⟩ : ∃ s, Nat.card K = s := ⟨_, rfl⟩
  rw [hs] at hK
  have hs1 : 1 ≤ s := by
    rw [← hs]
    exact Nat.card_pos
  have h4 : 1 ≤ s ^ 4 := Nat.one_le_pow _ _ hs1
  have h20 : 1 ≤ s ^ 20 := Nat.one_le_pow _ _ hs1
  have h5 : 5 ∣ s ^ 16 + s ^ 12 + s ^ 8 + s ^ 4 + 1 := by
    have : s % 5 = 1 ∨ s % 5 = 2 ∨ s % 5 = 3 ∨ s % 5 = 4 := by omega
    rcases this with h | h | h | h <;> simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h]
  obtain ⟨N, hN⟩ : (s - 1) * 5 ∣ s ^ 20 - 1 := by
    rw [show s ^ 20 - 1 = (s ^ 4 - 1) * (s ^ 16 + s ^ 12 + s ^ 8 + s ^ 4 + 1) by
      zify [h4, h20]
      ring]
    exact mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one s 4) h5
  have hsM : s ^ 20 = 5 * ((s - 1) * N) + 1 := by
    have : (s - 1) * 5 * N = 5 * ((s - 1) * N) := by ring
    omega
  have hcM : c ^ ((s - 1) * N) = 1 := by
    rw [pow_mul, ← hs, Nat.card_eq_fintype_card, FiniteField.pow_card_sub_one_eq_one c hc,
      one_pow]
  have hX : X ^ 5 - C c ∣ X ^ Nat.card K ^ 20 - X := by
    have h1 := sub_dvd_pow_sub_pow (X ^ 5 : K[X]) (C c) ((s - 1) * N)
    rw [← C_pow, hcM, C_1, ← pow_mul] at h1
    rw [hs, hsM, pow_succ X (5 * ((s - 1) * N)), ← sub_one_mul]
    exact h1.mul_right X
  have hdeg := ha.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (hdvd.trans hX)
  have hle : a.natDegree ≤ 20 := Nat.le_of_dvd (by norm_num) hdeg
  obtain ⟨k, hk⟩ := hodd
  generalize a.natDegree = d at hdeg hk hle ⊢
  interval_cases d <;> omega

theorem twentyFive_dvd_two_pow_add_one {f : ℕ} (h : 5 ∣ 2 ^ (5 * f) + 1) :
    25 ∣ 2 ^ (5 * f) + 1 := by
  rw [pow_mul', Nat.dvd_iff_mod_eq_zero] at h ⊢
  generalize 2 ^ f = x at h ⊢
  have hm : ((x % 25) ^ 5 + 1) % 25 = (x ^ 5 + 1) % 25 := ((Nat.mod_modEq x 25).pow 5).add_right 1
  have key : ∀ r < 25, (r ^ 5 + 1) % 5 = 0 → (r ^ 5 + 1) % 25 = 0 := by decide
  rw [← hm]
  refine key _ (Nat.mod_lt _ (by norm_num)) ?_
  rw [← Nat.mod_mod_of_dvd _ (by norm_num : 5 ∣ 25), hm, Nat.mod_mod_of_dvd _ (by norm_num), h]

theorem center_statedSU_five_ne_bot {E : Type} [Field E] [Finite E] {g : ℕ}
    (hE : Nat.card E = (2 ^ g) ^ 2) (h5 : 5 ∣ 2 ^ g + 1) :
    Subgroup.center ↥(StatedSU 5 (2 ^ g) E) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : 5 ∣ Nat.card Eˣ := by
    have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 ^ g) ^ 2 := Nat.one_le_pow _ _ h1
    rw [Nat.card_units, hE]
    exact h5.trans ⟨2 ^ g - 1, by zify [h1, h2]; ring⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 5 hcard
  have hmem := (CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hE (by norm_num) ζ).2
    ⟨hζ ▸ pow_orderOf_eq_one ζ, orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ h5)⟩
  intro hbot
  have hc : (⟨_, hmem⟩ : ↥(StatedSU 5 (2 ^ g) E)) ∈ Subgroup.center ↥(StatedSU 5 (2 ^ g) E) :=
    Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (GeneralLinearGroup.scalar_commute ζ (y : GL (Fin 5) E)).symm
  rw [hbot, Subgroup.mem_bot] at hc
  have h1 : (ζ : E) = 1 := by
    simpa [GeneralLinearGroup.coe_scalar] using congrArg
      (fun A : ↥(StatedSU 5 (2 ^ g) E) => ((A : GL (Fin 5) E) : Matrix (Fin 5) (Fin 5) E) 0 0) hc
  rw [Units.val_eq_one.1 h1, orderOf_one] at hζ
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
