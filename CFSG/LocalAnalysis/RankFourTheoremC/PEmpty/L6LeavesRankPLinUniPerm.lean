module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Finite.Perm
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU

open Equiv MulAction

theorem sum_eq_zero_of_shift {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpn : (n : ZMod p) = 0)
    (σ : Perm (Fin n)) (ℓ : Fin n → ZMod p) {γ : ZMod p} (hγ : γ ≠ 0)
    (h : ∀ k, ℓ (σ k) = ℓ k + γ) : ∑ k, ℓ k = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h1)
  have hsum : ∑ k, ℓ (σ k) ^ 2 = ∑ k, ℓ k ^ 2 := Equiv.sum_comp σ (fun k => ℓ k ^ 2)
  have hexp : ∑ k, ℓ (σ k) ^ 2 =
      ∑ k, ℓ k ^ 2 + 2 * γ * ∑ k, ℓ k + (n : ZMod p) * γ ^ 2 := by
    have h1 : ∀ k, ℓ (σ k) ^ 2 = ℓ k ^ 2 + 2 * γ * ℓ k + γ ^ 2 := fun k => by
      rw [h k]
      ring
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hexp, hpn, zero_mul, add_zero] at hsum
  have h3 : 2 * γ * ∑ k, ℓ k = 0 := add_eq_left.1 hsum
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd h4 (mul_ne_zero h2 hγ)
  · exact h4

theorem sum_eq_zero_of_isPGroup {p : ℕ} [Fact p.Prime] {X G : Type*} [Fintype X] [Group G]
    [MulAction G X] (hG : IsPGroup p G) (hfix : ∀ x : X, ∃ g : G, g • x ≠ x)
    (ℓ : X → ZMod p) (hℓ : ∀ (g : G) (x : X), ℓ (g • x) = ℓ x) : ∑ x, ℓ x = 0 := by
  classical
  have hdvd : ∀ v : ZMod p, p ∣ (Finset.univ.filter fun x => ℓ x = v).card := by
    intro v
    let S : SubMulAction G X := ⟨{x | ℓ x = v}, fun g x hx => by
      change ℓ x = v at hx
      change ℓ (g • x) = v
      rw [hℓ, hx]⟩
    have h1 := hG.card_modEq_card_fixedPoints S
    have h2 : Nat.card (fixedPoints G S) = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun ⟨x, hx⟩ => ?_⟩
      obtain ⟨g, hg⟩ := hfix (x : X)
      apply hg
      have := hx g
      exact congrArg Subtype.val this
    rw [h2] at h1
    have h3 : Nat.card S = (Finset.univ.filter fun x => ℓ x = v).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Iff.rfl
    rw [h3] at h1
    exact (Nat.modEq_zero_iff_dvd).1 h1
  calc ∑ x, ℓ x = ∑ v : ZMod p, ∑ x ∈ Finset.univ.filter (fun x => ℓ x = v), ℓ x :=
        (Finset.sum_fiberwise Finset.univ ℓ ℓ).symm
    _ = ∑ v : ZMod p, ((Finset.univ.filter fun x => ℓ x = v).card : ZMod p) * v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => v) (fun x hx => (Finset.mem_filter.1 hx).2),
          Finset.sum_const, nsmul_eq_mul]
    _ = 0 := by
        refine Finset.sum_eq_zero fun v _ => ?_
        rw [(ZMod.natCast_eq_zero_iff _ _).2 (hdvd v), zero_mul]

theorem card_stabilizer_perm {n : ℕ} (hn : 0 < n) (i : Fin n) :
    Nat.card (stabilizer (Perm (Fin n)) i) = (n - 1).factorial := by
  have h1 := Nat.card_congr (orbitProdStabilizerEquivGroup (Perm (Fin n)) i)
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, orbit_eq_univ, Nat.card_univ,
    Nat.card_fin] at h1
  rw [← Nat.mul_factorial_pred hn.ne'] at h1
  exact Nat.eq_of_mul_eq_mul_left hn h1

theorem exists_moved_of_card {p n : ℕ} [Fact p.Prime] (hpn : p ∣ n) (hn : 0 < n)
    (B : Subgroup (Perm (Fin n))) (hB : Nat.card B = p ^ padicValNat p n.factorial) (i : Fin n) :
    ∃ σ ∈ B, σ i ≠ i := by
  by_contra hcon
  push Not at hcon
  have hle : B ≤ stabilizer (Perm (Fin n)) i := fun σ hσ => by
    rw [mem_stabilizer_iff, Perm.smul_def]
    exact hcon σ hσ
  have hdvd : Nat.card B ∣ (n - 1).factorial :=
    card_stabilizer_perm hn i ▸ Subgroup.card_dvd_of_le hle
  rw [hB, padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)] at hdvd
  have h1 : padicValNat p n.factorial = padicValNat p n + padicValNat p (n - 1).factorial := by
    rw [← Nat.mul_factorial_pred hn.ne', padicValNat.mul hn.ne' (Nat.factorial_ne_zero _)]
  have h2 : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn.ne' hpn
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP.LU
