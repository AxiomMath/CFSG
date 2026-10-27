module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized
public import CFSG.LocalAnalysis.EvenBN.TwoF4.RotationOrbits

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Finset

variable {K : Type*} [Field K]

theorem twisted_additive_linearized {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hK : Nat.card K = p ^ n) {ι : Type*} (χ ψ : ι → K) {φ : K → K}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hφ : ∀ i x, φ (χ i * x) = ψ i * φ x) :
    ∃ c : Fin n → K, (∀ x, φ x = ∑ k, c k * x ^ p ^ (k : ℕ)) ∧
      ∀ k, c k ≠ 0 → ∀ i, ψ i = χ i ^ p ^ (k : ℕ) := by
  obtain ⟨h1, -⟩ := ComponentInitial.finite_field_linearized_map_bases hp hn hK
  obtain ⟨c, hc, -⟩ := h1 (AddMonoidHom.mk' φ hadd)
  have hc' : ∀ x, φ x = ∑ k, c k * x ^ p ^ (k : ℕ) := hc
  refine ⟨c, hc', fun k hk i => ?_⟩
  obtain ⟨d, -, hd⟩ :=
    h1 (AddMonoidHom.mk' (fun x => φ (χ i * x)) fun x y => by rw [mul_add, hadd])
  have hA := hd (fun k => c k * χ i ^ p ^ (k : ℕ)) fun x => by
    show φ (χ i * x) = _
    rw [hc']
    exact sum_congr rfl fun k _ => by rw [mul_pow]; ring
  have hB := hd (fun k => ψ i * c k) fun x => by
    show φ (χ i * x) = _
    rw [hφ, hc', mul_sum]
    exact sum_congr rfl fun k _ => by ring
  have hk' := congrFun (hA.trans hB.symm) k
  exact (mul_left_cancel₀ hk (hk'.trans (mul_comm _ _))).symm

theorem twisted_additive_eq_zero {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hK : Nat.card K = p ^ n)
    {ι : Type*} (χ ψ : ι → K) {φ : K → K} (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hφ : ∀ i x, φ (χ i * x) = ψ i * φ x) (hsep : ∀ k < n, ∃ i, ψ i ≠ χ i ^ p ^ k) (x : K) :
    φ x = 0 := by
  obtain ⟨c, hc, hck⟩ := twisted_additive_linearized hp hn hK χ ψ hadd hφ
  have h0 : ∀ k, c k = 0 := fun k => by
    by_contra hk
    obtain ⟨i, hi⟩ := hsep k k.isLt
    exact hi (hck k hk i)
  rw [hc]
  simp [h0]

theorem twisted_zpow_eq_zero {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hK : Nat.card K = p ^ n)
    {a b : ℤ} {φ : K → K} (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hφ : ∀ (u : Kˣ) (x : K), φ (((u ^ a : Kˣ) : K) * x) = ((u ^ b : Kˣ) : K) * φ x)
    (hab : ∀ k : ℕ, (b : ZMod (p ^ n - 1)) ≠ p ^ k * a) (x : K) : φ x = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos n).ne')
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = p ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  refine twisted_additive_eq_zero hp hn hK (fun u : Kˣ => ((u ^ a : Kˣ) : K))
    (fun u => ((u ^ b : Kˣ) : K)) hadd hφ (fun k _ => ⟨g, fun h => hab k ?_⟩) x
  have h' : g ^ b = (g ^ a) ^ p ^ k := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h)
  have h1 : g ^ ((p : ℤ) ^ k * a - b) = 1 := by
    rw [zpow_sub, mul_comm ((p : ℤ) ^ k) a, zpow_mul, ← Nat.cast_pow, zpow_natCast, ← h',
      mul_inv_cancel]
  have hdvd := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hord] at hdvd
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub b ((p : ℤ) ^ k * a) (p ^ n - 1)).2 hdvd
  push_cast at h2
  exact h2

theorem twisted_zpow_eq_zero_of_not_sameTwoOrbit {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {a b : ℤ} {φ : K → K} (hadd : ∀ x y, φ (x + y) = φ x + φ y)
    (hφ : ∀ (u : Kˣ) (x : K), φ (((u ^ a : Kˣ) : K) * x) = ((u ^ b : Kˣ) : K) * φ x)
    (hab : ¬ SameTwoOrbit (a : ZMod (2 ^ n - 1)) (b : ZMod (2 ^ n - 1))) (x : K) : φ x = 0 :=
  twisted_zpow_eq_zero Nat.prime_two hn hK hadd hφ
    (fun k hk => hab ⟨k, by rw [hk, Nat.cast_ofNat]⟩) x

end CFSG.LocalAnalysis.EvenBN.TwoF4
