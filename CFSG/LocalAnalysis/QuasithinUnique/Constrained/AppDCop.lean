module

public import Mathlib.GroupTheory.Sylow
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

open scoped Pointwise

namespace CFSG.QuasithinUnique.AppD

theorem factorization_144 : (144 : ℕ).factorization 3 = 2 := by
  have h3 : Nat.Prime 3 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  rw [Nat.factorization_def _ h3]
  have e : (144 : ℕ) = 3 ^ 2 * 16 := by norm_num
  rw [e, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_of_trivial_on_quotient {X : Type*} [Group X] [Finite X] (N : Subgroup X)
    [N.Normal] (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN : Nat.card N = 16)
    (hX : Nat.card X = 144) (φ : X ≃* X) (h1 : ∀ n ∈ N, φ n = n)
    (h2 : ∀ x, φ x * x⁻¹ ∈ N) : ∃ n ∈ N, ∀ x, φ x = n * x * n⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hPc : Nat.card P = 9 := by
    rw [Sylow.card_eq_multiplicity, hX, factorization_144]
    norm_num
  have hPN : (P : Subgroup X) ⊓ N = ⊥ := by
    have h1 : Nat.card ↥((P : Subgroup X) ⊓ N) ∣ 9 := by
      rw [← hPc]; exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥((P : Subgroup X) ⊓ N) ∣ 16 := by
      rw [← hN]; exact Subgroup.card_dvd_of_le inf_le_right
    have : Nat.card ↥((P : Subgroup X) ⊓ N) = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (by norm_num : Nat.Coprime 9 16)) h2
    exact Subgroup.eq_bot_of_card_eq _ this
  have hPnorm : (P : Subgroup X) ≤ Subgroup.normalizer (N : Set X) := by
    intro p _
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => Subgroup.Normal.conj_mem inferInstance m hm p, fun hm => ?_⟩
    have := Subgroup.Normal.conj_mem inferInstance _ hm p⁻¹
    simpa [mul_assoc] using this
  have htop : (P : Subgroup X) ⊔ N = ⊤ := by
    have := C5.card_sup_mul_card_inf_of_le_normalizer hPnorm
    rw [hPN, Subgroup.card_bot, mul_one, hPc, hN] at this
    exact Subgroup.eq_top_of_card_eq _ (by rw [hX]; omega)
  have hprod : ∀ x : X, ∃ p ∈ (P : Subgroup X), ∃ m ∈ N, x = p * m := by
    intro x
    have hx : x ∈ ((P : Subgroup X) ⊔ N : Subgroup X) := by rw [htop]; exact Subgroup.mem_top x
    have hx' : x ∈ (((P : Subgroup X) ⊔ N : Subgroup X) : Set X) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (P : Subgroup X) N hPnorm] at hx'
    obtain ⟨p, hp, m, hm, rfl⟩ := hx'
    exact ⟨p, hp, m, hm, rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P (φ • P)
  have hsub : MulAut.conj g • (P : Subgroup X) = φ • (P : Subgroup X) := by
    have := congrArg (fun Q : Sylow 3 X => (Q : Subgroup X)) hg
    exact this
  have key : ∀ p ∈ (P : Subgroup X), ∃ y ∈ (P : Subgroup X), g * y * g⁻¹ = φ p := by
    intro p hp
    have : φ • p ∈ φ • (P : Subgroup X) := Subgroup.smul_mem_pointwise_smul p φ _ hp
    rw [← hsub] at this
    obtain ⟨y, hy, hy'⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 this
    exact ⟨y, hy, by simpa using hy'⟩
  obtain ⟨p₀, hp₀, m₀, hm₀, hgeq⟩ := hprod g
  set n : X := p₀ * m₀ * p₀⁻¹ with hn
  have hnN : n ∈ N := Subgroup.Normal.conj_mem inferInstance m₀ hm₀ p₀
  have hg2 : g = n * p₀ := by rw [hgeq, hn]; group
  refine ⟨n, hnN, fun x => ?_⟩
  have hψP : ∀ p ∈ (P : Subgroup X), n⁻¹ * φ p * n = p := by
    intro p hp
    obtain ⟨y, hy, hy'⟩ := key p hp
    have e : n⁻¹ * φ p * n = p₀ * y * p₀⁻¹ := by
      rw [← hy', hg2]; group
    have hmemP : n⁻¹ * φ p * n ∈ (P : Subgroup X) := by
      rw [e]; exact mul_mem (mul_mem hp₀ hy) (inv_mem hp₀)
    have hmemN : (n⁻¹ * φ p * n) * p⁻¹ ∈ N := by
      have e2 : (n⁻¹ * φ p * n) * p⁻¹ = n⁻¹ * (φ p * p⁻¹) * (p * n * p⁻¹) := by group
      rw [e2]
      exact mul_mem (mul_mem (inv_mem hnN) (h2 p)) (Subgroup.Normal.conj_mem inferInstance n hnN p)
    have hmemP2 : (n⁻¹ * φ p * n) * p⁻¹ ∈ (P : Subgroup X) := mul_mem hmemP (inv_mem hp)
    have : (n⁻¹ * φ p * n) * p⁻¹ ∈ (P : Subgroup X) ⊓ N := ⟨hmemP2, hmemN⟩
    rw [hPN, Subgroup.mem_bot] at this
    exact mul_inv_eq_one.1 this
  have hψN : ∀ m ∈ N, n⁻¹ * φ m * n = m := by
    intro m hm
    rw [h1 m hm]
    have := hNab n hnN m hm
    calc n⁻¹ * m * n = n⁻¹ * (m * n) := by group
      _ = n⁻¹ * (n * m) := by rw [this]
      _ = m := by group
  obtain ⟨p, hp, m, hm, rfl⟩ := hprod x
  have hx : n⁻¹ * φ (p * m) * n = p * m := by
    rw [map_mul]
    calc n⁻¹ * (φ p * φ m) * n = (n⁻¹ * φ p * n) * (n⁻¹ * φ m * n) := by group
      _ = p * m := by rw [hψP p hp, hψN m hm]
  calc φ (p * m) = n * (n⁻¹ * φ (p * m) * n) * n⁻¹ := by group
    _ = n * (p * m) * n⁻¹ := by rw [hx]

end CFSG.QuasithinUnique.AppD
