module

public import Certificates.Data.Kernel.ThCensus.Defs
public import Certificates.Data.Kernel.ThCensus.PermDefs
import CFSG.Certificates.Kernel.Th.Spec.DceMat
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.OrderOfElement
public import CFSG.Certificates.Kernel.Th.Spec.SylowPcGrp
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.KC.ThCensus.Sound

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.ThCensus

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem rec_and {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem elem_core {z a0 a1 a2 c0 c1 c2 rr : Bool}
    (h : bIf(z, true, bAnd(notB (bAnd(a0, bAnd(a1, a2))),
      bIf(bAnd(c0, bAnd(c1, c2)), rr, true))) = true) (hz : z = false) :
    ¬ (a0 = true ∧ a1 = true ∧ a2 = true) ∧
      (c0 = true → c1 = true → c2 = true → rr = true) := by
  subst hz
  revert h
  cases a0 <;> cases a1 <;> cases a2 <;> cases c0 <;> cases c1 <;> cases c2 <;> cases rr <;> decide

theorem rec_all (F : ℕ → Bool) : ∀ k, Nat.rec (motive := fun _ => Bool) true
    (fun l ih => bAnd(F l, ih)) k = true → ∀ l < k, F l = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero _)
  | k + 1, h, l, hl => by
    have h' : bAnd(F k, Nat.rec (motive := fun _ => Bool) true (fun l ih => bAnd(F l, ih)) k) =
        true := h
    obtain ⟨h1, h2⟩ := rec_and h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · exact rec_all F k h2 l hl
    · exact h1

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : CFSG.KC.Loop.allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := rec_all (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi h
    (i / 64) (by omega)
  have h2 := rec_all (fun l => (fun i => bIf(Nat.blt i m, f i, true))
      (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64) (Nat.mod_lt _ (by norm_num))
  have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, h64]
    omega
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

@[expose] def nfFrom {G : Type*} [Group G] (g : ℕ → G) : ℕ → ℕ → ℕ → G
  | 0, _, _ => 1
  | t + 1, s, n => g s ^ (n % 3) * nfFrom g t (s + 1) (n / 3)

theorem nfFrom_succ {G : Type*} [Group G] (g : ℕ → G) (t s n : ℕ) :
    nfFrom g (t + 1) s n = g s ^ (n % 3) * nfFrom g t (s + 1) (n / 3) := rfl

theorem nfFrom_zero {G : Type*} [Group G] (g : ℕ → G) : ∀ t s, nfFrom g t s 0 = 1
  | 0, _ => rfl
  | t + 1, s => by rw [nfFrom_succ, Nat.zero_mod, pow_zero, Nat.zero_div, nfFrom_zero g t, one_mul]

theorem nfFrom_mem {G : Type*} [Group G] (g : ℕ → G) (N : ℕ) :
    ∀ t s n, s + t ≤ N → nfFrom g t s n ∈ SylowPc.pcSub g N s
  | 0, _, _, _ => one_mem _
  | t + 1, s, n, h => by
    rw [nfFrom_succ]
    exact mul_mem (pow_mem (SylowPc.mem_pcSub le_rfl (by omega)) _)
      (SylowPc.pcSub_succ_le g N s (nfFrom_mem g N t (s + 1) (n / 3) (by omega)))

theorem nf_step {G : Type*} [Group G] [Finite G] (g : ℕ → G) (N : ℕ)
    (hpow : ∀ i < N, g i ^ 3 ∈ SylowPc.pcSub g N (i + 1))
    (hconj : ∀ i j, i < j → j < N → (g i)⁻¹ * g j * g i ∈ SylowPc.pcSub g N (i + 1))
    {i : ℕ} (hi : i < N) :
    ∀ x ∈ SylowPc.pcSub g N i, ∃ e < 3, ∃ y ∈ SylowPc.pcSub g N (i + 1), x = g i ^ e * y := by
  have hc1 : ∀ a ∈ SylowPc.pcSub g N (i + 1), (g i)⁻¹ * a * g i ∈ SylowPc.pcSub g N (i + 1) := by
    intro a ha
    have ha' : a ∈ Subgroup.closure (g '' Set.Ico (i + 1) N) := ha
    clear ha
    induction ha' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact hconj i j (by have := hj.1; omega) hj.2
    | one => simp
    | mul a b _ _ iha ihb =>
      have e : (g i)⁻¹ * (a * b) * g i = ((g i)⁻¹ * a * g i) * ((g i)⁻¹ * b * g i) := by group
      rw [e]
      exact mul_mem iha ihb
    | inv a _ iha =>
      have e : (g i)⁻¹ * a⁻¹ * g i = ((g i)⁻¹ * a * g i)⁻¹ := by group
      rw [e]
      exact inv_mem iha
  have hcp : ∀ k, ∀ a ∈ SylowPc.pcSub g N (i + 1),
      (g i ^ k)⁻¹ * a * g i ^ k ∈ SylowPc.pcSub g N (i + 1) := by
    intro k
    induction k with
    | zero =>
      intro a ha
      simpa using ha
    | succ k ih =>
      intro a ha
      have e : (g i ^ (k + 1))⁻¹ * a * g i ^ (k + 1) =
          (g i)⁻¹ * ((g i ^ k)⁻¹ * a * g i ^ k) * g i := by
        rw [pow_succ]
        group
      rw [e]
      exact hc1 _ (ih a ha)
  let T : G → Prop := fun x => ∃ e < 3, ∃ y ∈ SylowPc.pcSub g N (i + 1), x = g i ^ e * y
  have hTmul : ∀ a b, T a → T b → T (a * b) := by
    rintro a b ⟨e, -, y, hy, rfl⟩ ⟨f, -, y', hy', rfl⟩
    refine ⟨(e + f) % 3, Nat.mod_lt _ (by norm_num),
      (g i ^ 3) ^ ((e + f) / 3) * ((g i ^ f)⁻¹ * y * g i ^ f) * y',
      mul_mem (mul_mem (pow_mem (hpow i hi) _) (hcp f y hy)) hy', ?_⟩
    have h1 : g i ^ e * y * (g i ^ f * y') = g i ^ (e + f) * ((g i ^ f)⁻¹ * y * g i ^ f * y') := by
      rw [pow_add]
      group
    have h2 : g i ^ (e + f) = g i ^ ((e + f) % 3) * (g i ^ 3) ^ ((e + f) / 3) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [h1, h2]
    simp only [mul_assoc]
  have hT1 : T 1 := ⟨0, by norm_num, 1, one_mem _, by simp⟩
  have hTpow : ∀ a, T a → ∀ k : ℕ, T (a ^ k) := by
    intro a ha k
    induction k with
    | zero => simpa using hT1
    | succ k ih =>
      rw [pow_succ]
      exact hTmul _ _ ih ha
  have hTinv : ∀ a, T a → T a⁻¹ := by
    intro a ha
    have ho := orderOf_pos a
    have e : a ^ (orderOf a - 1) = a⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel ho, pow_orderOf_eq_one]
    rw [← e]
    exact hTpow a ha _
  intro x hx
  have hx' : x ∈ Subgroup.closure (g '' Set.Ico i N) := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    rcases Nat.lt_or_ge i j with hij | hij
    · exact ⟨0, by norm_num, g j, SylowPc.mem_pcSub hij hj.2, by simp⟩
    · obtain rfl : j = i := le_antisymm hij hj.1
      exact ⟨1, by norm_num, 1, one_mem _, by simp⟩
  | one => exact hT1
  | mul a b _ _ iha ihb => exact hTmul a b iha ihb
  | inv a _ iha => exact hTinv a iha

theorem nf_surj {G : Type*} [Group G] [Finite G] (g : ℕ → G) (N : ℕ)
    (hpow : ∀ i < N, g i ^ 3 ∈ SylowPc.pcSub g N (i + 1))
    (hconj : ∀ i j, i < j → j < N → (g i)⁻¹ * g j * g i ∈ SylowPc.pcSub g N (i + 1)) :
    ∀ t s, s + t = N → ∀ x ∈ SylowPc.pcSub g N s, ∃ m < 3 ^ t, nfFrom g t s m = x := by
  intro t
  induction t with
  | zero =>
    intro s hs x hx
    have hs' : s = N := by omega
    rw [hs'] at hx
    have hx' : x ∈ Subgroup.closure (g '' Set.Ico N N) := hx
    rw [Set.Ico_self, Set.image_empty, Subgroup.closure_empty, Subgroup.mem_bot] at hx'
    exact ⟨0, by norm_num, by rw [hx']; rfl⟩
  | succ t ih =>
    intro s hs x hx
    obtain ⟨e, he, y, hy, rfl⟩ := nf_step g N hpow hconj (by omega : s < N) x hx
    obtain ⟨m, hm, rfl⟩ := ih (s + 1) (by omega) y hy
    refine ⟨e + 3 * m, ?_, ?_⟩
    · rw [pow_succ]
      omega
    · have h1 : (e + 3 * m) % 3 = e := by omega
      have h2 : (e + 3 * m) / 3 = m := by omega
      rw [nfFrom_succ, h1, h2]

section Perm

variable {G : Type*} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)) (g : ℕ → G)
  (vec : ℕ → Fin 248 → ZMod 2) (TT : ℕ)

theorem walkFrom_succ (t s p n : ℕ) :
    permWalkFrom TT (t + 1) s p n = permWalkFrom TT t (s + 1) (permStep TT s (n % 3) p) (n / 3) := by
  change CFSG.KC.Loop.strictN (permStep TT s (Nat.mod n 3) p)
    (fun q => permWalkFrom TT t (Nat.succ s) q (Nat.div n 3)) = _
  rw [strictN_eq]
  rfl

theorem step_of_tables (T : ℕ → ℕ → ℕ)
    (htt : ∀ k < 10, ∀ p < 243, permStep TT k 1 p = T k p ∧
      permStep TT k 2 p = permStep TT k 1 (T k p))
    (htab : ∀ k < 10, ∀ p < 243, T k p < 243 ∧ vec (T k p) = Matrix.vecMul (vec p) (φ (g k))) :
    ∀ k < 10, ∀ d < 3, ∀ p < 243, permStep TT k d p < 243 ∧
      vec (permStep TT k d p) = Matrix.vecMul (vec p) (φ (g k ^ d)) := by
  intro k hk d hd p hp
  obtain ⟨h1, h2⟩ := htt k hk p hp
  obtain ⟨h3, h4⟩ := htab k hk p hp
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl
  · have e : permStep TT k 0 p = p := rfl
    rw [e, pow_zero, map_one, Matrix.vecMul_one]
    exact ⟨hp, rfl⟩
  · rw [h1, pow_one]
    exact ⟨h3, h4⟩
  · obtain ⟨h5, h6⟩ := htt k hk (T k p) h3
    obtain ⟨h7, h8⟩ := htab k hk (T k p) h3
    rw [h2, h5, pow_two, map_mul, ← Matrix.vecMul_vecMul, ← h4]
    exact ⟨h7, h8⟩

variable {φ g vec TT}

theorem walk_spec
    (hstep : ∀ k < 10, ∀ d < 3, ∀ p < 243, permStep TT k d p < 243 ∧
      vec (permStep TT k d p) = Matrix.vecMul (vec p) (φ (g k ^ d))) :
    ∀ t s, s + t ≤ 10 → ∀ p < 243, ∀ n, permWalkFrom TT t s p n < 243 ∧
      vec (permWalkFrom TT t s p n) = Matrix.vecMul (vec p) (φ (nfFrom g t s n)) := by
  intro t
  induction t with
  | zero =>
    intro s _ p hp n
    refine ⟨hp, ?_⟩
    change vec p = Matrix.vecMul (vec p) (φ 1)
    rw [map_one, Matrix.vecMul_one]
  | succ t ih =>
    intro s hs p hp n
    rw [walkFrom_succ]
    obtain ⟨h1, h2⟩ := hstep s (by omega) (n % 3) (Nat.mod_lt _ (by norm_num)) p hp
    obtain ⟨h3, h4⟩ := ih (s + 1) (by omega) _ h1 (n / 3)
    refine ⟨h3, ?_⟩
    rw [h4, h2, Matrix.vecMul_vecMul, ← map_mul, nfFrom_succ]

theorem permWalk_spec
    (hstep : ∀ k < 10, ∀ d < 3, ∀ p < 243, permStep TT k d p < 243 ∧
      vec (permStep TT k d p) = Matrix.vecMul (vec p) (φ (g k ^ d))) {p : ℕ} (hp : p < 243)
    (n : ℕ) : permWalk TT p n < 243 ∧
      vec (permWalk TT p n) = Matrix.vecMul (vec p) (φ (nfFrom g 10 0 n)) :=
  walk_spec hstep 10 0 le_rfl p hp n

theorem fix_of_eq {v : Fin 248 → ZMod 2} {A B : G}
    (h : Matrix.vecMul v (φ A) = Matrix.vecMul v (φ B)) : Matrix.vecMul v (φ (A * B⁻¹)) = v := by
  rw [map_mul, ← Matrix.vecMul_vecMul, h, Matrix.vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one,
    Matrix.vecMul_one]

variable (hstep : ∀ k < 10, ∀ d < 3, ∀ p < 243, permStep TT k d p < 243 ∧
      vec (permStep TT k d p) = Matrix.vecMul (vec p) (φ (g k ^ d)))
  (hinj : ∀ p < 243, ∀ q < 243, vec p = vec q → p = q) {o0 o1 o2 : ℕ}
  (ho0 : o0 < 243) (ho1 : o1 < 243) (ho2 : o2 < 243)
  (hsurj : ∀ x ∈ SylowPc.pcSub g 10 0, ∃ m < 3 ^ 10, nfFrom g 10 0 m = x)
  (hmove : ∀ n < 3 ^ 10, n ≠ 0 →
    ¬ (permWalk TT o0 n = o0 ∧ permWalk TT o1 n = o1 ∧ permWalk TT o2 n = o2))
include hstep hinj ho0 ho1 ho2 hsurj hmove

theorem base_spec {x : G} (hx : x ∈ SylowPc.pcSub g 10 0)
    (h0 : Matrix.vecMul (vec o0) (φ x) = vec o0) (h1 : Matrix.vecMul (vec o1) (φ x) = vec o1)
    (h2 : Matrix.vecMul (vec o2) (φ x) = vec o2) : x = 1 := by
  obtain ⟨m, hm, rfl⟩ := hsurj x hx
  by_cases hm0 : m = 0
  · rw [hm0, nfFrom_zero]
  · exfalso
    have fix : ∀ o < 243, Matrix.vecMul (vec o) (φ (nfFrom g 10 0 m)) = vec o →
        permWalk TT o m = o := by
      intro o ho h
      obtain ⟨hw1, hw2⟩ := permWalk_spec hstep ho m
      exact hinj _ hw1 _ ho (hw2.trans h)
    exact hmove m hm hm0 ⟨fix o0 ho0 h0, fix o1 ho1 h1, fix o2 ho2 h2⟩

omit hmove in
theorem cubeFix_of_pow {o n : ℕ} (ho : o < 243) (h3 : nfFrom g 10 0 n ^ 3 = 1) :
    permCubeFix TT o n = true := by
  obtain ⟨a1, a2⟩ := permWalk_spec hstep ho n
  obtain ⟨b1, b2⟩ := permWalk_spec hstep a1 n
  obtain ⟨c1, c2⟩ := permWalk_spec hstep b1 n
  have e : permWalk TT (permWalk TT (permWalk TT o n) n) n = o := by
    refine hinj _ c1 _ ho ?_
    rw [c2, b2, a2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← map_mul, ← map_mul,
      ← pow_three, h3, map_one, Matrix.vecMul_one]
  unfold permCubeFix
  rw [e]
  exact Nat.beq_refl o

theorem conj_spec {reps : List (List ℕ)} {nr : ℕ}
    (hrec : ∀ n < 3 ^ 10, n ≠ 0 → permCubeFix TT o0 n = true → permCubeFix TT o1 n = true →
      permCubeFix TT o2 n = true → ∃ m1 c, 0 < m1 ∧ m1 ≤ nr ∧
        permKeyAt TT o0 c n (permNfNum (reps.getD (m1 - 1) [])) = true ∧
        permKeyAt TT o1 c n (permNfNum (reps.getD (m1 - 1) [])) = true ∧
        permKeyAt TT o2 c n (permNfNum (reps.getD (m1 - 1) [])) = true)
    {x : G} (hx : x ∈ SylowPc.pcSub g 10 0) (h3 : x ^ 3 = 1) :
    x = 1 ∨ ∃ m < nr, ∃ c ∈ SylowPc.pcSub g 10 0,
      c * x * c⁻¹ = nfFrom g 10 0 (permNfNum (reps.getD m [])) := by
  obtain ⟨n, hn, rfl⟩ := hsurj x hx
  by_cases hn0 : n = 0
  · left
    rw [hn0, nfFrom_zero]
  right
  obtain ⟨m1, c, hm1, hm1r, k0, k1, k2⟩ := hrec n hn hn0 (cubeFix_of_pow hstep hinj ho0 ho1 ho2
    hsurj ho0 h3) (cubeFix_of_pow hstep hinj ho0 ho1 ho2 hsurj ho1 h3)
    (cubeFix_of_pow hstep hinj ho0 ho1 ho2 hsurj ho2 h3)
  set r := permNfNum (reps.getD (m1 - 1) []) with hr
  have key : ∀ o < 243, permKeyAt TT o c n r = true →
      Matrix.vecMul (vec o) (φ (nfFrom g 10 0 c * nfFrom g 10 0 n *
        (nfFrom g 10 0 r * nfFrom g 10 0 c)⁻¹)) = vec o := by
    intro o ho hk
    have e := Nat.eq_of_beq_eq_true hk
    obtain ⟨a1, a2⟩ := permWalk_spec hstep ho c
    obtain ⟨b1, b2⟩ := permWalk_spec hstep a1 n
    obtain ⟨c1, c2⟩ := permWalk_spec hstep ho r
    obtain ⟨d1, d2⟩ := permWalk_spec hstep c1 c
    apply fix_of_eq
    have ev := congrArg vec e
    rw [b2, a2, d2, c2, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← map_mul, ← map_mul] at ev
    exact ev
  have hmem : ∀ k, nfFrom g 10 0 k ∈ SylowPc.pcSub g 10 0 := fun k => nfFrom_mem g 10 10 0 k le_rfl
  have hy := base_spec hstep hinj ho0 ho1 ho2 hsurj hmove
    (mul_mem (mul_mem (hmem c) (hmem n)) (inv_mem (mul_mem (hmem r) (hmem c))))
    (key o0 ho0 k0) (key o1 ho1 k1) (key o2 ho2 k2)
  have e := mul_inv_eq_one.mp hy
  refine ⟨m1 - 1, by omega, nfFrom g 10 0 c, hmem c, ?_⟩
  rw [e]
  group
  rfl

end Perm

theorem elem_spec {TT R : ℕ} {reps : List (List ℕ)} {nr o0 o1 o2 b i : ℕ}
    (h : permElemOK TT R reps nr o0 o1 o2 b i = true) (hn : 729 * b + i ≠ 0) :
    ¬ (permWalk TT o0 (729 * b + i) = o0 ∧ permWalk TT o1 (729 * b + i) = o1 ∧
        permWalk TT o2 (729 * b + i) = o2) ∧
      (permCubeFix TT o0 (729 * b + i) = true → permCubeFix TT o1 (729 * b + i) = true →
        permCubeFix TT o2 (729 * b + i) = true →
        permRecOK TT reps nr o0 o1 o2 (729 * b + i) (bitsN R (24 * i) 24) = true) := by
  have hz : Nat.beq (729 * b + i) 0 = false := by
    cases hb : Nat.beq (729 * b + i) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hn
  obtain ⟨hA, hB⟩ := elem_core (z := Nat.beq (729 * b + i) 0)
    (a0 := Nat.beq (permWalk TT o0 (729 * b + i)) o0)
    (a1 := Nat.beq (permWalk TT o1 (729 * b + i)) o1)
    (a2 := Nat.beq (permWalk TT o2 (729 * b + i)) o2)
    (c0 := permCubeFix TT o0 (729 * b + i)) (c1 := permCubeFix TT o1 (729 * b + i))
    (c2 := permCubeFix TT o2 (729 * b + i))
    (rr := permRecOK TT reps nr o0 o1 o2 (729 * b + i) (bitsN R (24 * i) 24)) h hz
  refine ⟨fun ⟨e0, e1, e2⟩ => hA ⟨?_, ?_, ?_⟩, hB⟩
  · rw [e0]
    exact Nat.beq_refl o0
  · rw [e1]
    exact Nat.beq_refl o1
  · rw [e2]
    exact Nat.beq_refl o2

theorem rec_spec {TT : ℕ} {reps : List (List ℕ)} {nr o0 o1 o2 n rc : ℕ}
    (h : permRecOK TT reps nr o0 o1 o2 n rc = true) :
    0 < rc % 64 ∧ rc % 64 ≤ nr ∧
      permKeyAt TT o0 (rc / 64) n (permNfNum (reps.getD (rc % 64 - 1) [])) = true ∧
      permKeyAt TT o1 (rc / 64) n (permNfNum (reps.getD (rc % 64 - 1) [])) = true ∧
      permKeyAt TT o2 (rc / 64) n (permNfNum (reps.getD (rc % 64 - 1) [])) = true := by
  have h' : bAnd(Nat.blt 0 (rc % 64), bAnd(Nat.ble (rc % 64) nr,
      bAnd(permKeyAt TT o0 (rc / 64) n (permNfNum (reps.getD (rc % 64 - 1) [])),
        bAnd(permKeyAt TT o1 (rc / 64) n (permNfNum (reps.getD (rc % 64 - 1) [])),
          permKeyAt TT o2 (rc / 64) n (permNfNum (reps.getD (rc % 64 - 1) [])))))) = true := h
  obtain ⟨a, h1⟩ := rec_and h'
  obtain ⟨b, h2⟩ := rec_and h1
  obtain ⟨k0, h3⟩ := rec_and h2
  obtain ⟨k1, k2⟩ := rec_and h3
  exact ⟨Nat.blt_eq.mp a, Nat.le_of_ble_eq_true b, k0, k1, k2⟩

theorem blocks_spec {TT : ℕ} {R : ℕ → ℕ} {reps : List (List ℕ)} {nr o0 o1 o2 : ℕ}
    (h : ∀ b < 81, permBlockOK TT (R b) reps nr o0 o1 o2 b = true) :
    (∀ n < 3 ^ 10, n ≠ 0 →
      ¬ (permWalk TT o0 n = o0 ∧ permWalk TT o1 n = o1 ∧ permWalk TT o2 n = o2)) ∧
    (∀ n < 3 ^ 10, n ≠ 0 → permCubeFix TT o0 n = true → permCubeFix TT o1 n = true →
      permCubeFix TT o2 n = true → ∃ m1 c, 0 < m1 ∧ m1 ≤ nr ∧
        permKeyAt TT o0 c n (permNfNum (reps.getD (m1 - 1) [])) = true ∧
        permKeyAt TT o1 c n (permNfNum (reps.getD (m1 - 1) [])) = true ∧
        permKeyAt TT o2 c n (permNfNum (reps.getD (m1 - 1) [])) = true) := by
  have hel : ∀ n < 3 ^ 10, permElemOK TT (R (n / 729)) reps nr o0 o1 o2 (n / 729) (n % 729) =
      true := by
    intro n hn
    exact allBelow_spec (h (n / 729) (by omega)) (by norm_num) (n % 729) (Nat.mod_lt _ (by norm_num))
  have hdiv : ∀ n, 729 * (n / 729) + n % 729 = n := fun n => Nat.div_add_mod n 729
  refine ⟨fun n hn hn0 => ?_, fun n hn hn0 c0 c1 c2 => ?_⟩
  · have hs := (elem_spec (hel n hn) (by rw [hdiv]; exact hn0)).1
    rw [hdiv] at hs
    exact hs
  · have hs := (elem_spec (hel n hn) (by rw [hdiv]; exact hn0)).2
    rw [hdiv] at hs
    obtain ⟨a, b, k0, k1, k2⟩ := rec_spec (hs c0 c1 c2)
    exact ⟨_, _, a, b, k0, k1, k2⟩

theorem lenN_eq {α : Type} : ∀ l : List α, lenN l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenN l) = _
    rw [lenN_eq l]
    rfl

theorem ttRow_spec {TT g : ℕ} : ∀ (l : List ℕ) (j : ℕ), permTtRowOK TT g l j = true →
    ∀ i < l.length, permStep TT g 1 (j + i) = l.getD i 0 ∧
      permStep TT g 2 (j + i) = permStep TT g 1 (l.getD i 0)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | t :: l, j, h, i, hi => by
    have h' : bAnd(Nat.beq (permStep TT g 1 j) t,
        bAnd(Nat.beq (permStep TT g 2 j) (permStep TT g 1 t), permTtRowOK TT g l (Nat.succ j))) =
        true := h
    obtain ⟨h1, h2⟩ := rec_and h'
    obtain ⟨h3, h4⟩ := rec_and h2
    rcases i with _ | i
    · exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h3⟩
    · have hr := ttRow_spec l (j + 1) h4 i (by simpa using hi)
      have e : j + (i + 1) = j + 1 + i := by omega
      rw [e]
      exact hr

theorem tabRow_spec {PTS : ℕ → ℕ} {rm P off m : ℕ} : ∀ (l : List ℕ) (j : ℕ),
    tabRowOK PTS rm P off m l j = true → ∀ i < l.length, l.getD i 0 < m ∧
      inLayout rm (PTS (off + (j + i))) = true ∧
      vecB rm (PTS (off + (j + i))) P = PTS (off + l.getD i 0)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | t :: l, j, h, i, hi => by
    have h' : andB (andB (Nat.blt t m) (andB (inLayout rm (PTS (Nat.add off j)))
        (Nat.beq (vecB rm (PTS (Nat.add off j)) P) (PTS (Nat.add off t)))))
        (tabRowOK PTS rm P off m l (Nat.succ j)) = true := h
    obtain ⟨h1, h2⟩ := Dce.andB_iff.1 h'
    obtain ⟨h3, h4⟩ := Dce.andB_iff.1 h1
    obtain ⟨h5, h6⟩ := Dce.andB_iff.1 h4
    rcases i with _ | i
    · exact ⟨Nat.blt_eq.mp h3, h5, Nat.eq_of_beq_eq_true h6⟩
    · have hr := tabRow_spec l (j + 1) h2 i (by simpa using hi)
      have e : j + (i + 1) = j + 1 + i := by omega
      rw [e]
      exact hr

end CFSG.KC.ThCensus.Sound

end
