module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Aut
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

variable {Λ : Type*} [Group Λ]

theorem card_modEq_ncard_fixed [Finite Λ] {x : MulAut Λ} (hx5 : x ^ 5 = 1) (S : Subgroup Λ)
    (hxS : ∀ l, l ∈ S → x l ∈ S) : Nat.card S ≡ {l : Λ | l ∈ S ∧ x l = l}.ncard [MOD 5] := by
  classical
  let f : ↥S → ↥S := fun l => ⟨x l.1, hxS l.1 l.2⟩
  have hf : ∀ n : ℕ, ∀ a : ↥S, ((f^[n] a : ↥S) : Λ) = (x ^ n) a.1 := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', pow_succ']
      change x ((f^[n] a : ↥S) : Λ) = (x * x ^ n) a.1
      rw [ih]
      rfl
  have hf5 : ∀ a, f^[5] a = a := by
    intro a
    apply Subtype.ext
    rw [hf, hx5]
    rfl
  have hmod := card_modEq_five_fixed f hf5
  have hset : Subtype.val '' Function.fixedPoints f = {l : Λ | l ∈ S ∧ x l = l} := by
    ext l
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, congrArg Subtype.val ha⟩
    · rintro ⟨hl, hxl⟩
      exact ⟨⟨l, hl⟩, Subtype.ext hxl, rfl⟩
  rw [← hset, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact hmod

theorem card_modEq_of_fixed_le [Finite Λ] {x : MulAut Λ} (hx5 : x ^ 5 = 1) {N F : Subgroup Λ}
    (hxN : ∀ l, l ∈ N → x l ∈ N) (hxF : ∀ l, l ∈ F → x l ∈ F) (hNF : N ≤ F)
    (hfix : ∀ l ∈ F, x l = l → l ∈ N) : Nat.card F ≡ Nat.card N [MOD 5] := by
  have h1 := card_modEq_ncard_fixed hx5 F hxF
  have h2 := card_modEq_ncard_fixed hx5 N hxN
  have hset : {l : Λ | l ∈ F ∧ x l = l} = {l : Λ | l ∈ N ∧ x l = l} := by
    ext l
    exact ⟨fun ⟨hl, hxl⟩ => ⟨hfix l hl hxl, hxl⟩, fun ⟨hl, hxl⟩ => ⟨hNF hl, hxl⟩⟩
  rw [hset] at h1
  exact h1.trans h2.symm

theorem fpf_quot [Finite Λ] (hcomm : ∀ a b : Λ, a * b = b * a) {x : MulAut Λ} (hx5 : x ^ 5 = 1)
    {N M : Subgroup Λ} (hNM : N ≤ M) (hxN : ∀ l, l ∈ N → x l ∈ N) (hxM : ∀ l, l ∈ M → x l ∈ M)
    (hN5 : ¬ 5 ∣ Nat.card N) (hidx : Nat.card M = 16 * Nat.card N)
    (hfix : ∀ l ∈ M, x l = l → l ∈ N) {C : Subgroup Λ} (hC : ∀ l ∈ M, x l = l → l ∈ C)
    (hCcard : Nat.card C < 16) : ∀ l ∈ M, x l * l⁻¹ ∈ N → l ∈ N := by
  classical
  let F : Subgroup Λ :=
    { carrier := {l | l ∈ M ∧ x l * l⁻¹ ∈ N}
      one_mem' := ⟨M.one_mem, by simpa using N.one_mem⟩
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨M.mul_mem haM hbM, ?_⟩
        have e : x (a * b) * (a * b)⁻¹ = (x a * a⁻¹) * (x b * b⁻¹) := by
          rw [map_mul, mul_inv_rev]
          calc x a * x b * (b⁻¹ * a⁻¹) = x a * ((x b * b⁻¹) * a⁻¹) := by group
            _ = x a * (a⁻¹ * (x b * b⁻¹)) := by rw [hcomm (x b * b⁻¹) a⁻¹]
            _ = (x a * a⁻¹) * (x b * b⁻¹) := by group
        rw [e]
        exact N.mul_mem ha hb
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨M.inv_mem haM, ?_⟩
        have e : x a⁻¹ * (a⁻¹)⁻¹ = (x a * a⁻¹)⁻¹ := by
          rw [map_inv, mul_inv_rev, inv_inv, hcomm]
        rw [e]
        exact N.inv_mem ha }
  have hmemF : ∀ l, l ∈ F ↔ l ∈ M ∧ x l * l⁻¹ ∈ N := fun l => Iff.rfl
  have hNF : N ≤ F := fun l hl =>
    (hmemF l).2 ⟨hNM hl, N.mul_mem (hxN l hl) (N.inv_mem hl)⟩
  have hFM : F ≤ M := fun l hl => ((hmemF l).1 hl).1
  have hxF : ∀ l, l ∈ F → x l ∈ F := by
    intro l hl
    obtain ⟨hlM, hl'⟩ := (hmemF l).1 hl
    refine (hmemF _).2 ⟨hxM l hlM, ?_⟩
    have := hxN _ hl'
    rwa [map_mul, map_inv] at this
  have hfixF : ∀ l ∈ F, x l = l → l ∈ N := fun l hl hxl => hfix l (hFM hl) hxl
  have hmod := card_modEq_of_fixed_le hx5 hxN hxF hNF hfixF
  have hNpos : 0 < Nat.card N := Nat.card_pos
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hNF
  have hdvd16 : m ∣ 16 := by
    have h1 := Subgroup.card_dvd_of_le hFM
    rw [hm, hidx, mul_comm 16 (Nat.card N)] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hNpos h1
  have hcop : Nat.gcd 5 (Nat.card N) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hN5
  have hm1 : m ≡ 1 [MOD 5] := by
    rw [hm] at hmod
    have : Nat.card N * m ≡ Nat.card N * 1 [MOD 5] := by rwa [mul_one]
    rw [mul_comm (Nat.card N) m, mul_comm (Nat.card N) 1] at this
    exact Nat.ModEq.cancel_right_of_coprime hcop this
  obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using hdvd16 : m ∣ 2 ^ 4)
  have hk' : k = 0 ∨ k = 4 := by
    rw [hk] at hm1
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hm1; decide)
  rcases hk' with rfl | rfl
  ·
    have hmeq : Nat.card F = Nat.card N := by rw [hm, hk]; simp
    have hFN : F = N := (Subgroup.eq_of_le_of_card_ge hNF (by rw [hmeq])).symm
    intro l hl hlN
    have : l ∈ F := (hmemF l).2 ⟨hl, hlN⟩
    rw [hFN] at this
    exact this
  ·
    exfalso
    have hFcard : Nat.card F = Nat.card M := by rw [hm, hk, hidx]; ring
    have hFeq : F = M := Subgroup.eq_of_le_of_card_ge hFM (by rw [hFcard])
    have hall : ∀ l ∈ M, x l * l⁻¹ ∈ N := fun l hl => ((hmemF l).1 (hFeq ▸ hl)).2
    let φ : ↥M →* ↥M :=
      { toFun := fun l => ⟨x l.1 * l.1⁻¹, M.mul_mem (hxM l.1 l.2) (M.inv_mem l.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          show x (a.1 * b.1) * (a.1 * b.1)⁻¹ = (x a.1 * a.1⁻¹) * (x b.1 * b.1⁻¹)
          rw [map_mul, mul_inv_rev]
          calc x a.1 * x b.1 * (b.1⁻¹ * a.1⁻¹) = x a.1 * ((x b.1 * b.1⁻¹) * a.1⁻¹) := by group
            _ = x a.1 * (a.1⁻¹ * (x b.1 * b.1⁻¹)) := by rw [hcomm (x b.1 * b.1⁻¹) a.1⁻¹]
            _ = (x a.1 * a.1⁻¹) * (x b.1 * b.1⁻¹) := by group) }
    have hker : Nat.card φ.ker ≤ Nat.card C := by
      refine Nat.card_le_card_of_injective (fun l => ⟨l.1.1, hC l.1.1 l.1.2 ?_⟩) ?_
      · have h1 : φ l.1 = 1 := l.2
        have h2 : x l.1.1 * l.1.1⁻¹ = 1 := congrArg Subtype.val h1
        exact mul_inv_eq_one.1 h2
      · intro a b hab
        have h := Subtype.mk.inj hab
        exact Subtype.ext (Subtype.ext h)
    have hrange : Nat.card φ.range ≤ Nat.card N := by
      have hle : φ.range ≤ N.subgroupOf M := by
        rintro _ ⟨l, rfl⟩
        exact hall l.1 l.2
      calc Nat.card φ.range ≤ Nat.card (N.subgroupOf M) := Subgroup.card_le_of_le hle
        _ = Nat.card N := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    have hcard := Subgroup.card_ker_mul_card_range φ
    have h3 : Nat.card ↥M ≤ Nat.card C * Nat.card N := by
      rw [← hcard]
      exact Nat.mul_le_mul hker hrange
    rw [hidx] at h3
    nlinarith

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
