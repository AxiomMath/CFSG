module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open Polynomial

structure KDat (F K : Type) [Field F] [Field K] [Algebra F K] where
  τ : K →+* K
  tau_alg : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a
  tau_tau : ∀ x : K, τ (τ x) = x
  tau_pow : ∀ x : K, τ x = x ^ Nat.card F
  card_K : Nat.card K = Nat.card F ^ 2
  fixed : ∀ x : K, τ x = x → ∃ a : F, algebraMap F K a = x
  θ : K
  theta_sq : θ ^ 2 = -1
  tau_theta : τ θ = -θ

section Exists

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [Finite K]

theorem exists_kdat (p e : ℕ) [Fact p.Prime] [CharP K p] (hF : Nat.card F = p ^ e)
    (hK : Nat.card K = (p ^ e) ^ 2) (hp2 : p ≠ 2) (hnsq : ¬ IsSquare (-1 : F)) :
    Nonempty (KDat F K) := by
  classical
  have := Fintype.ofFinite F
  have := Fintype.ofFinite K
  have : ExpChar K p := ExpChar.prime Fact.out
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hpowF : ∀ a : F, a ^ Nat.card F = a := fun a => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  have hpowK : ∀ x : K, x ^ Nat.card K = x := fun x => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  let τ : K →+* K := iterateFrobenius K p e
  have hτpow : ∀ x : K, τ x = x ^ Nat.card F := fun x => by
    simp only [τ, iterateFrobenius_def, hF]
  have hK' : Nat.card K = Nat.card F ^ 2 := by rw [hK, hF]
  have htt : ∀ x : K, τ (τ x) = x := fun x => by
    rw [hτpow, hτpow, ← pow_mul, ← sq, ← hK']
    exact hpowK x
  have htalg : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a := fun a => by
    rw [hτpow, ← map_pow, hpowF]
  have hfixed : ∀ x : K, τ x = x → ∃ a : F, algebraMap F K a = x := by
    intro x hx
    set P : Polynomial K := Polynomial.X ^ Nat.card F - Polynomial.X with hP
    have hdeg : P.natDegree = Nat.card F := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
    have hP0 : P ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hdeg
      omega
    have hsub : Finset.univ.image (algebraMap F K) ⊆ P.roots.toFinset := by
      intro y hy
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← map_pow, hpowF, sub_self]
    have hcard : P.roots.toFinset.card ≤ (Finset.univ.image (algebraMap F K)).card := by
      rw [Finset.card_image_of_injective _ (algebraMap F K).injective, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
      calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ = Nat.card F := hdeg
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hx' : x ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← hτpow, hx, sub_self]
    rw [← heq] at hx'
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx'
    exact ⟨a, ha⟩
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.Prime.eq_two_or_odd' Fact.out).resolve_left hp2 |>.pow
  have hsq : ∃ θ : K, θ ^ 2 = -1 := by
    have hne : (-1 : K) ≠ 0 := neg_ne_zero.2 one_ne_zero
    have hchar : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      exact hp2
    obtain ⟨k, hk⟩ := hodd
    have hcardF : Fintype.card F = 2 * k + 1 := by rw [← Nat.card_eq_fintype_card]; exact hk
    have h1 : (-1 : K) ^ (Fintype.card F - 1) = 1 := by
      rw [hcardF, show 2 * k + 1 - 1 = 2 * k by omega, pow_mul]
      simp
    have hcardK : Fintype.card K = (2 * k + 1) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hK, ← hF, hk]
    have hexp : Fintype.card K / 2 = (Fintype.card F - 1) * (k + 1) := by
      rw [hcardK, hcardF]
      have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
      rw [this]
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]
      omega
    obtain ⟨θ, hθ⟩ := (FiniteField.isSquare_iff hchar hne).2 (by
      rw [hexp, pow_mul, h1, one_pow])
    exact ⟨θ, by rw [sq]; exact hθ.symm⟩
  obtain ⟨θ, hθ2⟩ := hsq
  have hτθ : τ θ = -θ := by
    have h1 : (τ θ) ^ 2 = θ ^ 2 := by
      rw [← map_pow, hθ2, map_neg, map_one]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exfalso
      obtain ⟨a, ha⟩ := hfixed θ h
      apply hnsq
      refine ⟨a, ?_⟩
      apply (algebraMap F K).injective
      rw [map_neg, map_one, map_mul, ha]
      linear_combination -hθ2
    · exact h
  exact ⟨{
    τ := τ
    tau_alg := htalg
    tau_tau := htt
    tau_pow := hτpow
    card_K := hK'
    fixed := hfixed
    θ := θ
    theta_sq := hθ2
    tau_theta := hτθ }⟩

end Exists

section Norm

set_option linter.unusedSectionVars false

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [Finite K] (D : KDat F K)

theorem KDat.tau_ne_zero {x : K} (hx : x ≠ 0) : D.τ x ≠ 0 := by
  intro h
  apply hx
  have := congrArg D.τ h
  rwa [D.tau_tau, map_zero] at this

theorem KDat.norm_fixed (x : K) : D.τ (x * D.τ x) = x * D.τ x := by
  rw [map_mul, D.tau_tau, mul_comm]

theorem KDat.norm_ne_zero {x : K} (hx : x ≠ 0) : x * D.τ x ≠ 0 :=
  mul_ne_zero hx (D.tau_ne_zero hx)

theorem KDat.card_norm_le [Fintype K] [DecidableEq K] (δ : K) :
    (Finset.univ.filter fun m : K => m * D.τ m = δ).card ≤ Nat.card F + 1 := by
  set P : K[X] := X ^ (Nat.card F + 1) - C δ with hP
  have hdeg : P.natDegree = Nat.card F + 1 := natDegree_X_pow_sub_C
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  calc (Finset.univ.filter fun m : K => m * D.τ m = δ).card
      ≤ P.roots.toFinset.card := by
        refine Finset.card_le_card fun m hm => ?_
        rw [Finset.mem_filter] at hm
        rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
        simp only [eval_sub, eval_pow, eval_X, eval_C]
        rw [← hm.2, D.tau_pow, pow_succ]
        ring
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = Nat.card F + 1 := hdeg

theorem KDat.card_norm_fibre [Fintype K] [Fintype F] [DecidableEq K] {a : K} (ha0 : a ≠ 0)
    (ha : D.τ a = a) :
    (Finset.univ.filter fun m : K => m * D.τ m = a).card = Fintype.card F + 1 := by
  have hcF : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hcK : Fintype.card K = Fintype.card F ^ 2 := by
    rw [← Nat.card_eq_fintype_card, D.card_K, hcF]
  have hq2 : 2 ≤ Fintype.card F := by
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  classical
  set q := Fintype.card F with hq
  set S : Finset K := (Finset.univ.filter fun x : F => x ≠ 0).image (algebraMap F K) with hSdef
  have hSmem : ∀ b : K, b ∈ S ↔ b ≠ 0 ∧ D.τ b = b := by
    intro b
    rw [hSdef, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨fun h => hx ((map_eq_zero_iff _ (algebraMap F K).injective).1 h), D.tau_alg x⟩
    · rintro ⟨hb0, hb⟩
      obtain ⟨x, hx⟩ := D.fixed b hb
      refine ⟨x, ?_, hx⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro rfl
      exact hb0 (by rw [← hx, map_zero])
  have hScard : S.card = q - 1 := by
    rw [hSdef, Finset.card_image_of_injective _ (algebraMap F K).injective]
    have : (Finset.univ.filter fun x : F => x ≠ 0) = Finset.univ.erase 0 := by
      ext x
      simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  set s : Finset K := Finset.univ.filter fun m : K => m ≠ 0 with hs
  have hscard : s.card = q ^ 2 - 1 := by
    have : s = Finset.univ.erase 0 := by
      ext x
      simp [hs]
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcK]
  have hmaps : ∀ m ∈ s, m * D.τ m ∈ S := by
    intro m hm
    rw [hs, Finset.mem_filter] at hm
    rw [hSmem]
    exact ⟨D.norm_ne_zero hm.2, D.norm_fixed m⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise hmaps
  have hle : ∀ b ∈ S, (s.filter fun m : K => m * D.τ m = b).card ≤ q + 1 := by
    intro b _
    refine le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _)))
      ?_
    have := D.card_norm_le b
    rwa [hcF] at this
  have heq : ∀ b ∈ S, (s.filter fun m : K => m * D.τ m = b).card = q + 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b0, hb0S, hne⟩ := hcon
    have hlt : (s.filter fun m : K => m * D.τ m = b0).card < q + 1 :=
      lt_of_le_of_ne (hle b0 hb0S) hne
    have hsum := Finset.sum_lt_sum hle ⟨b0, hb0S, hlt⟩
    rw [← hfiber, hscard, Finset.sum_const, hScard, smul_eq_mul] at hsum
    have h1 : (q - 1) * (q + 1) = q ^ 2 - 1 := by
      have hq1 : 1 ≤ q := by omega
      have hq3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [hq1, hq3]
      ring
    omega
  have haS : a ∈ S := (hSmem a).2 ⟨ha0, ha⟩
  have h := heq a haS
  have hsub : (s.filter fun m : K => m * D.τ m = a) =
      Finset.univ.filter fun m : K => m * D.τ m = a := by
    ext m
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hm
      refine ⟨?_, hm⟩
      rintro rfl
      simp at hm
      exact ha0 hm.symm
  rw [← hsub]
  exact h

end Norm

end CFSG.ClassicalInvolution.PhanB3.S
