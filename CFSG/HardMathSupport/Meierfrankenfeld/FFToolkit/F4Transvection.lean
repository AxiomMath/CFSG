module

public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section F4

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_zmod_two (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

theorem neg_eq_zmod_two (v : V) : -v = v := neg_eq_of_add_eq_zero_right (add_self_zmod_two v)

theorem two_eq_zero_end : (2 : Module.End (ZMod 2) V) = 0 := by
  ext v
  simp [two_smul, add_self_zmod_two]

theorem pow_four_eq_one_of_pow_three {R : Type*} [Ring R] (h2 : (2 : R) = 0) {X : R}
    (hX : X ^ 3 = 0) : (1 + X) ^ 4 = 1 := by
  have h4 : (4 : R) = 0 := by rw [show (4 : R) = 2 * 2 by norm_num, h2, zero_mul]
  have h6 : (6 : R) = 0 := by rw [show (6 : R) = 3 * 2 by norm_num, h2, mul_zero]
  have hX4 : X ^ 4 = 0 := by rw [pow_succ, hX, zero_mul]
  have : (1 + X) ^ 4 = 1 + 4 * X + 6 * X ^ 2 + 4 * X ^ 3 + X ^ 4 := by noncomm_ring
  rw [this, h4, h6, hX4]
  simp

variable {z : Module.End (ZMod 2) V}

theorem sum_zz_eq_zero (hz3 : ∀ v, z (z (z v)) = v) (hfpf : ∀ v, z v = v → v = 0) (v : V) :
    v + z v + z (z v) = 0 := by
  apply hfpf
  rw [map_add, map_add, hz3]
  abel

theorem zx_ne_zero (hz3 : ∀ v, z (z (z v)) = v) {x : V} (hx : x ≠ 0) : z x ≠ 0 := by
  intro h
  apply hx
  rw [← hz3 x, h, map_zero, map_zero]

theorem four_elems [Finite V] (hz3 : ∀ v, z (z (z v)) = v) (hfpf : ∀ v, z v = v → v = 0)
    (S : Submodule (ZMod 2) V) (hcard : Nat.card S = 4) {x : V} (hx : x ∈ S) (hx0 : x ≠ 0)
    (hzx : z x ∈ S) : ∀ s ∈ S, s = 0 ∨ s = x ∨ s = z x ∨ s = x + z x := by
  classical
  intro s hs
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1, h2, h3⟩ := hcon
  have hzx0 := zx_ne_zero hz3 hx0
  have hzxx : z x ≠ x := fun h => hx0 (hfpf x h)
  have hxzx : x + z x ≠ 0 := by
    intro h
    apply hzxx
    have := eq_neg_of_add_eq_zero_right h
    rw [this, neg_eq_zmod_two]
  have hsub : (({0, x, z x, x + z x, s} : Finset V) : Set V) ⊆ (S : Set V) := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact S.zero_mem
    · exact hx
    · exact hzx
    · exact S.add_mem hx hzx
    · exact hs
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hle
  have hS : (S : Set V).ncard = 4 := by
    rw [← hcard]; exact (Nat.card_coe_set_eq _).symm
  rw [hS] at hle
  have hcard5 : ({0, x, z x, x + z x, s} : Finset V).card = 5 := by
    have e1 : x + z x ≠ x := fun h => hzx0 (by simpa using h)
    have e2 : x + z x ≠ z x := fun h => hx0 (by simpa using h)
    have hnd : [0, x, z x, x + z x, s].Nodup := by
      simp [hx0.symm, hzx0.symm, hxzx.symm, h0.symm, hzxx.symm, e1.symm, h1.symm, e2.symm,
        h2.symm, h3.symm]
    have := List.toFinset_card_of_nodup hnd
    simpa using this
  omega

theorem pow_four_eq_one_of_nilp {N N' g : Module.End (ZMod 2) V}
    (hg : ∀ v, g v = v + N' v + N v + N (N' v)) (hN2 : ∀ v, N (N v) = 0)
    (hN'2 : ∀ v, N' (N' v) = 0) (h : (∀ v, N (N' v) = 0) ∨ (∀ v, N' (N v) = 0)) :
    g ^ 4 = 1 := by
  have hX : ∀ v, (g - 1) v = N' v + N v + N (N' v) := by
    intro v
    rw [LinearMap.sub_apply, hg, Module.End.one_apply]
    abel
  have hX3 : (g - 1) ^ 3 = 0 := by
    ext v
    simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, hX, map_add, hN2, hN'2,
      LinearMap.zero_apply]
    rcases h with h | h
    · simp [h]
    · simp [h]
  have := pow_four_eq_one_of_pow_three (two_eq_zero_end (V := V)) hX3
  simpa using this

noncomputable def theta4 (b : Fin 4 → V) : (Fin 4 → ZMod 2) →ₗ[ZMod 2] V :=
  ∑ i, (LinearMap.proj i : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2).smulRight (b i)

theorem theta4_apply (b : Fin 4 → V) (c : Fin 4 → ZMod 2) : theta4 b c = ∑ i, c i • b i := by
  simp [theta4]

@[expose] def f4Mat (p0 p1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1 + p0, p1, 1, 0; p1, 1 + p0 + p1, 0, 1; p0, p1, 1, 0; p1, p0 + p1, 0, 1]

theorem f4Mat_pow_of_cases {p0 p1 : ZMod 2}
    (h : (p0 = 1 ∧ p1 = 0) ∨ (p0 = 0 ∧ p1 = 1) ∨ (p0 = 1 ∧ p1 = 1)) :
    ∃ n, 1 ≤ n ∧ n ≤ 5 ∧ f4Mat p0 p1 ^ n = 1 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨3, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨5, by norm_num, by norm_num, by decide +kernel⟩
  · exact ⟨5, by norm_num, by norm_num, by decide +kernel⟩

theorem zz_eq (hz3 : ∀ v, z (z (z v)) = v) (hfpf : ∀ v, z v = v → v = 0) (v : V) :
    z (z v) = v + z v := by
  have h := eq_neg_of_add_eq_zero_right (sum_zz_eq_zero hz3 hfpf v)
  rw [h, neg_add, neg_eq_zmod_two, neg_eq_zmod_two]

theorem general_position_order [Finite V] {N N' g : Module.End (ZMod 2) V}
    (hz3 : ∀ v, z (z (z v)) = v) (hfpf : ∀ v, z v = v → v = 0)
    (hNz : ∀ v, N (z v) = z (N v)) (hN'z : ∀ v, N' (z v) = z (N' v))
    (hN2 : ∀ v, N (N v) = 0) (hN'2 : ∀ v, N' (N' v) = 0)
    (hA : Nat.card (LinearMap.range N) = 4) (hA' : Nat.card (LinearMap.range N') = 4)
    (hg : ∀ v, g v = v + N' v + N v + N (N' v))
    (hNN' : ¬ ∀ v, N (N' v) = 0) (hN'N : ¬ ∀ v, N' (N v) = 0) :
    ∃ n, 1 ≤ n ∧ n ≤ 5 ∧ g ^ n = 1 := by
  obtain ⟨w0, hw0⟩ := not_forall.1 hNN'
  set u' : V := N' w0 with hu'def
  have hNu'0 : N u' ≠ 0 := hw0
  have hu'0 : u' ≠ 0 := fun h => hNu'0 (by rw [h, map_zero])
  set u : V := N u' with hudef
  have hu0 : u ≠ 0 := hNu'0
  have hNu'u : N u' = u := rfl
  have hNu : N u = 0 := hN2 u'
  have hN'u' : N' u' = 0 := hN'2 w0
  have huA : u ∈ LinearMap.range N := ⟨u', rfl⟩
  have hNzu' : N (z u') = z u := hNz u'
  have hzuA : z u ∈ LinearMap.range N := ⟨z u', hNzu'⟩
  have hu'A' : u' ∈ LinearMap.range N' := ⟨w0, rfl⟩
  have hzu'A' : z u' ∈ LinearMap.range N' := ⟨z w0, hN'z w0⟩
  have hA4 := four_elems hz3 hfpf (LinearMap.range N) hA huA hu0 hzuA
  have hA'4 := four_elems hz3 hfpf (LinearMap.range N') hA' hu'A' hu'0 hzu'A'
  have hNzu : N (z u) = 0 := by rw [hNz, hNu, map_zero]
  have hN'zu : N' (z u) = z (N' u) := hN'z u
  have hN'zu' : N' (z u') = 0 := by rw [hN'z, hN'u', map_zero]
  have hc0 : N' u ≠ 0 := by
    intro h
    apply hN'N
    intro v
    have hNv : N v ∈ LinearMap.range N := ⟨v, rfl⟩
    rcases hA4 _ hNv with h1 | h1 | h1 | h1 <;> rw [h1]
    · simp
    · exact h
    · rw [hN'zu, h, map_zero]
    · simp [map_add, hN'zu, h]
  have hc0A' : N' u ∈ LinearMap.range N' := ⟨u, rfl⟩
  have hzc0A' : z (N' u) ∈ LinearMap.range N' := ⟨z u, hN'zu⟩
  have hA'4' := four_elems hz3 hfpf (LinearMap.range N') hA' hc0A' hc0 hzc0A'
  obtain ⟨p0, p1, hc0eq, hp⟩ : ∃ p0 p1 : ZMod 2, N' u = p0 • u' + p1 • z u' ∧
      ((p0 = 1 ∧ p1 = 0) ∨ (p0 = 0 ∧ p1 = 1) ∨ (p0 = 1 ∧ p1 = 1)) := by
    rcases hA'4 _ hc0A' with h | h | h | h
    · exact absurd h hc0
    · exact ⟨1, 0, by simp [h], Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, 1, by simp [h], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨1, 1, by simp [h], Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  have hzzu := zz_eq hz3 hfpf u
  have hzzu' := zz_eq hz3 hfpf u'
  have hzc0 : z (N' u) = p0 • z u' + p1 • (u' + z u') := by
    rw [hc0eq, map_add, map_smul, map_smul, hzzu']
  have hNzc0 : N (z (N' u)) = p0 • z u + p1 • (u + z u) := by
    rw [hzc0, map_add, map_smul, map_smul, map_add, hNzu', hNu'u]
  have gu : g u = (1 + p0) • u + p1 • z u + p0 • u' + p1 • z u' := by
    rw [hg, hc0eq, hNu, map_add, map_smul, map_smul, hNu'u, hNzu']
    module
  have gzu : g (z u) = p1 • u + (1 + p0 + p1) • z u + p1 • u' + (p0 + p1) • z u' := by
    rw [hg, hN'zu, hNzu, hNzc0, hzc0]
    module
  have gu' : g u' = u' + u := by
    rw [hg, hN'u', map_zero, hNu'u]
    abel
  have gzu' : g (z u') = z u' + z u := by
    rw [hg, hN'zu', map_zero, hNzu']
    abel
  let b : Fin 4 → V := ![u, z u, u', z u']
  have hθ : ∀ c, g (theta4 b c) = theta4 b ((f4Mat p0 p1).mulVec c) := by
    intro c
    rw [theta4_apply, theta4_apply, map_sum]
    simp only [Fin.sum_univ_four, map_smul, b, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.mulVec, dotProduct, f4Mat, Matrix.of_apply]
    rw [gu, gzu, gu', gzu']
    simp
    module
  have hpow : ∀ k c, (g ^ k) (theta4 b c) = theta4 b ((f4Mat p0 p1 ^ k).mulVec c) := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
      intro c
      rw [pow_succ, Module.End.mul_apply, hθ, ih, Matrix.mulVec_mulVec, pow_succ]
  obtain ⟨n, hn1, hn5, hMn⟩ := f4Mat_pow_of_cases hp
  refine ⟨n, hn1, hn5, ?_⟩
  ext w
  rw [Module.End.one_apply]
  obtain ⟨γ, δ, hγδ⟩ : ∃ γ δ : ZMod 2, N w = γ • u + δ • z u := by
    rcases hA4 _ ⟨w, rfl⟩ with h | h | h | h
    · exact ⟨0, 0, by simp [h]⟩
    · exact ⟨1, 0, by simp [h]⟩
    · exact ⟨0, 1, by simp [h]⟩
    · exact ⟨1, 1, by simp [h]⟩
  obtain ⟨α, β, hαβ⟩ : ∃ α β : ZMod 2, N' w = α • N' u + β • z (N' u) := by
    rcases hA'4' _ ⟨w, rfl⟩ with h | h | h | h
    · exact ⟨0, 0, by simp [h]⟩
    · exact ⟨1, 0, by simp [h]⟩
    · exact ⟨0, 1, by simp [h]⟩
    · exact ⟨1, 1, by simp [h]⟩
  set c : Fin 4 → ZMod 2 := ![α, β, γ, δ] with hc
  set p : V := theta4 b c with hp'
  have hpexp : p = α • u + β • z u + γ • u' + δ • z u' := by
    simp [hp', theta4_apply, Fin.sum_univ_four, b, c]
  have hNp : N p = γ • u + δ • z u := by
    rw [hpexp, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hNu, hNzu,
      hNu'u, hNzu']
    simp
  have hN'p : N' p = α • N' u + β • z (N' u) := by
    rw [hpexp, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hN'zu, hN'u',
      hN'zu']
    simp
  have hq : g (w - p) = w - p := by
    have h1 : N (w - p) = 0 := by rw [map_sub, hγδ, hNp, sub_self]
    have h2 : N' (w - p) = 0 := by rw [map_sub, hαβ, hN'p, sub_self]
    rw [hg, h1, h2, map_zero]
    simp
  have hqpow : ∀ k, (g ^ k) (w - p) = w - p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hq, ih]
  have hpp : (g ^ n) p = p := by
    rw [hp', hpow, hMn]
    simp
  have hw : w = p + (w - p) := by abel
  conv_rhs => rw [hw]
  rw [hw, map_add, hpp, hqpow]
  simp

theorem f4_transvection_order [Finite V] {t t' : Module.End (ZMod 2) V} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ v, z v = v → v = 0) (htz : t * z = z * t) (ht'z : t' * z = z * t')
    (ht2 : t * t = 1) (ht'2 : t' * t' = 1)
    (hA : Nat.card (LinearMap.range (t - 1)) = 4) (hA' : Nat.card (LinearMap.range (t' - 1)) = 4) :
    ∃ n, 1 ≤ n ∧ n ≤ 5 ∧ (t * t') ^ n = 1 := by
  have hz3' : ∀ v, z (z (z v)) = v := by
    intro v
    have := congrArg (fun f : Module.End (ZMod 2) V => f v) hz3
    simpa [pow_succ] using this
  have htt : ∀ v, t (t v) = v := fun v => by
    simpa using congrArg (fun f : Module.End (ZMod 2) V => f v) ht2
  have ht't' : ∀ v, t' (t' v) = v := fun v => by
    simpa using congrArg (fun f : Module.End (ZMod 2) V => f v) ht'2
  have hN : ∀ v, (t - 1) v = t v + v := fun v => by
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_neg, neg_eq_zmod_two]
  have hN' : ∀ v, (t' - 1) v = t' v + v := fun v => by
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_neg, neg_eq_zmod_two]
  have hN2 : ∀ v, (t - 1) ((t - 1) v) = 0 := fun v => by
    rw [hN, hN, map_add, htt]
    have := add_self_zmod_two (t v)
    have h2 := add_self_zmod_two v
    calc v + t v + (t v + v) = (v + v) + (t v + t v) := by abel
      _ = 0 := by rw [this, h2, add_zero]
  have hN'2 : ∀ v, (t' - 1) ((t' - 1) v) = 0 := fun v => by
    rw [hN', hN', map_add, ht't']
    have := add_self_zmod_two (t' v)
    have h2 := add_self_zmod_two v
    calc v + t' v + (t' v + v) = (v + v) + (t' v + t' v) := by abel
      _ = 0 := by rw [this, h2, add_zero]
  have hNz : ∀ v, (t - 1) (z v) = z ((t - 1) v) := fun v => by
    have := congrArg (fun f : Module.End (ZMod 2) V => f v) htz
    simp only [Module.End.mul_apply] at this
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, this]
    simp
  have hN'z : ∀ v, (t' - 1) (z v) = z ((t' - 1) v) := fun v => by
    have := congrArg (fun f : Module.End (ZMod 2) V => f v) ht'z
    simp only [Module.End.mul_apply] at this
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, this]
    simp
  have hg : ∀ v, (t * t') v = v + (t' - 1) v + (t - 1) v + (t - 1) ((t' - 1) v) := fun v => by
    have e1 : t' v = v + (t' - 1) v := by rw [hN', add_comm v, add_assoc, add_self_zmod_two, add_zero]
    have e2 : ∀ x, t x = x + (t - 1) x := fun x => by
      rw [hN, add_comm x, add_assoc, add_self_zmod_two, add_zero]
    rw [Module.End.mul_apply, e1, map_add, e2 v, e2 ((t' - 1) v)]
    abel
  by_cases h1 : ∀ v, (t - 1) ((t' - 1) v) = 0
  · exact ⟨4, by norm_num, by norm_num, pow_four_eq_one_of_nilp hg hN2 hN'2 (Or.inl h1)⟩
  by_cases h2 : ∀ v, (t' - 1) ((t - 1) v) = 0
  · exact ⟨4, by norm_num, by norm_num, pow_four_eq_one_of_nilp hg hN2 hN'2 (Or.inr h2)⟩
  exact general_position_order hz3' hfpf hNz hN'z hN2 hN'2 hA hA' hg h1 h2

end F4

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
