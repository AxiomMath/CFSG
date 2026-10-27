module

public import Certificates.Data.Kernel.F4Syl3Model
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

namespace CFSG.KC.F4Syl3

theorem dg_lt (a i : ℕ) : dg a i < 3 := Nat.mod_lt _ (by decide)

theorem dg_vec4 (x0 x1 x2 x3 : ℕ) :
    dg (vec4 x0 x1 x2 x3) 0 = x0 % 3 ∧ dg (vec4 x0 x1 x2 x3) 1 = x1 % 3 ∧
      dg (vec4 x0 x1 x2 x3) 2 = x2 % 3 ∧ dg (vec4 x0 x1 x2 x3) 3 = x3 % 3 := by
  simp only [dg, vec4]
  omega

theorem vec4_lt (x0 x1 x2 x3 : ℕ) : vec4 x0 x1 x2 x3 < 81 := by
  simp only [vec4]
  omega

theorem vadd_lt (a c : ℕ) : vadd a c < 81 := vec4_lt _ _ _ _

theorem dg_vadd (a c : ℕ) :
    dg (vadd a c) 0 = (dg a 0 + dg c 0) % 3 ∧ dg (vadd a c) 1 = (dg a 1 + dg c 1) % 3 ∧
      dg (vadd a c) 2 = (dg a 2 + dg c 2) % 3 ∧ dg (vadd a c) 3 = (dg a 3 + dg c 3) % 3 :=
  dg_vec4 _ _ _ _

theorem vadd_comm (a c : ℕ) : vadd a c = vadd c a := by
  simp only [vadd, Nat.add_comm]

theorem eq_of_dg {a c : ℕ} (ha : a < 81) (hc : c < 81) (h0 : dg a 0 = dg c 0)
    (h1 : dg a 1 = dg c 1) (h2 : dg a 2 = dg c 2) (h3 : dg a 3 = dg c 3) : a = c := by
  simp only [dg] at h0 h1 h2 h3
  omega

theorem dg_zero (i : ℕ) : dg 0 i = 0 := by simp [dg]

theorem vadd_neg_eq_zero {a c : ℕ} (ha : a < 81) (hc : c < 81) (h : vadd a (vneg c) = 0) :
    a = c := by
  have hn := dg_vadd 0 c
  have hn2 := dg_vadd (vadd 0 c) c
  have hv := dg_vadd a (vneg c)
  rw [h] at hv
  simp only [vneg, vmulk] at hv
  simp only [dg_zero, Nat.zero_add] at hv hn hn2
  have := dg_lt a 0
  have := dg_lt a 1
  have := dg_lt a 2
  have := dg_lt a 3
  have := dg_lt c 0
  have := dg_lt c 1
  have := dg_lt c 2
  have := dg_lt c 3
  apply eq_of_dg ha hc <;> omega

theorem vmulk_three (c : ℕ) : vmulk 3 c = 0 := by
  have h1 := dg_vadd 0 c
  have h2 := dg_vadd (vadd 0 c) c
  have h3 := dg_vadd (vadd (vadd 0 c) c) c
  simp only [dg_zero, Nat.zero_add] at h1
  simp only [vmulk]
  have := dg_lt c 0
  have := dg_lt c 1
  have := dg_lt c 2
  have := dg_lt c 3
  apply eq_of_dg (vadd_lt _ _) (by decide) <;> simp only [dg_zero] <;> omega

theorem lin_lt (c0 c1 c2 c3 a : ℕ) : lin c0 c1 c2 c3 a < 81 := vadd_lt _ _

theorem m4_lt (a : ℕ) : m4 a < 81 := vadd_lt _ _

theorem m5_lt (a : ℕ) : m5 a < 81 := vadd_lt _ _

theorem itr_lt {f : ℕ → ℕ} (hf : ∀ a, f a < 81) (n : ℕ) {a : ℕ} (ha : a < 81) :
    itr f n a < 81 := by
  cases n with
  | zero => exact ha
  | succ n => exact hf _

theorem actQ_lt (q : ℕ) {a : ℕ} (ha : a < 81) : actQ q a < 81 :=
  itr_lt m4_lt _ (itr_lt m5_lt _ ha)

theorem qadd_lt (q r : ℕ) : qadd q r < 9 := by
  simp only [qadd]
  omega

theorem pmul_lt (m n : ℕ) : pmul m n < 729 := by
  have h1 := vadd_lt (m % 81) (actQ (m / 81) (n % 81))
  have h2 := qadd_lt (m / 81) (n / 81)
  simp only [pmul]
  omega

theorem pmul_mod (m n : ℕ) : pmul m n % 81 = vadd (m % 81) (actQ (m / 81) (n % 81)) := by
  have h1 := vadd_lt (m % 81) (actQ (m / 81) (n % 81))
  simp only [pmul]
  omega

theorem pmul_div (m n : ℕ) : pmul m n / 81 = qadd (m / 81) (n / 81) := by
  have h1 := vadd_lt (m % 81) (actQ (m / 81) (n % 81))
  simp only [pmul]
  omega

@[expose] def ModelOK : Prop :=
  (∀ a, a < 81 → n4 (n4 (n4 a)) = 0) ∧ (∀ a, a < 81 → n5 (n5 (n5 a)) = 0) ∧
  (∀ a, a < 81 → n4 a = 0 → m4 a = a) ∧ (∀ a, a < 81 → n5 a = 0 → m5 a = a) ∧
  (∀ a, a < 81 → m4 a = a → m4 (n5 a) = n5 a) ∧
  (∀ a, a < 81 → a ≠ 0 → m4 a = a → m5 a = a → a = 26 ∨ a = 13) ∧
  (∀ q, q < 9 → actQ q 1 = 1 → actQ q 3 = 3 → actQ q 9 = 9 → actQ q 27 = 27 → q = 0) ∧
  m4 26 = 26 ∧ m5 26 = 26 ∧
  (∀ q, q < 9 → q ≠ 0 → fixCnt q = 9) ∧
  (∀ q, q < 9 → ∀ r, r < 9 → q ≠ 0 → r ≠ 0 → r ≠ q → r ≠ qadd q q → fixCnt2 q r = 3)

theorem allB_spec {n : ℕ} {f : ℕ → Bool} (h : allB n f = true) (i : ℕ) (hi : i < n) :
    f i = true :=
  List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem modelOK_of_chk (h : modelChk = true) : ModelOK := by
  simp only [modelChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hQ⟩, h26a⟩, h26b⟩, hF⟩, hF2⟩ := h
  have hA' := allB_spec hA
  have hQ' := allB_spec hQ
  have hF' := allB_spec hF
  have hF2' := allB_spec hF2
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hA' hQ' hF' hF2'
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha e => ?_, fun a ha e => ?_, fun a ha e => ?_,
    fun a ha e0 e4 e5 => ?_, fun q hq e1 e3 e9 e27 => ?_, beq_iff_eq.1 h26a, beq_iff_eq.1 h26b,
    fun q hq e => ?_, fun q hq r hr eq er erq erqq => ?_⟩
  · exact (hA' a ha).1.1.1.1.1
  · exact (hA' a ha).1.1.1.1.2
  · exact (hA' a ha).1.1.1.2.resolve_left (not_not.2 e)
  · exact (hA' a ha).1.1.2.resolve_left (not_not.2 e)
  · exact (hA' a ha).1.2.resolve_left (not_not.2 e)
  · rcases (hA' a ha).2 with (((h | h) | h) | h) | h
    · exact absurd h e0
    · exact absurd e4 h
    · exact absurd e5 h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hQ' q hq with (((h | h) | h) | h) | h
    · exact absurd e1 h
    · exact absurd e3 h
    · exact absurd e9 h
    · exact absurd e27 h
    · exact h
  · exact (hF' q hq).resolve_left e
  · have := allB_spec (hF2' q hq) r hr
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with (((h | h) | h) | h) | h
    · exact absurd h eq
    · exact absurd h er
    · exact absurd h erq
    · exact absurd h erqq
    · exact h

variable {G : Type*} [Group G]

@[expose] def sE4 (s : Fin 4 → G) (x0 x1 x2 x3 : ℕ) : G := s 0 ^ x0 * s 1 ^ x1 * s 2 ^ x2 * s 3 ^ x3

@[expose] def fS (s : Fin 4 → G) (a : ℕ) : G := sE4 s (dg a 0) (dg a 1) (dg a 2) (dg a 3)

theorem pow_mod3 {g : G} (h : g ^ 3 = 1) (n : ℕ) : g ^ (n % 3) = g ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h, one_pow, mul_one]

theorem inv_eq_sq {g : G} (h : g ^ 3 = 1) : g⁻¹ = g ^ 2 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ', h]

section Torus

variable {s : Fin 4 → G} (hc : ∀ i j, s i * s j = s j * s i) (h3 : ∀ i, s i ^ 3 = 1)
include hc

theorem sE4_mul (x0 x1 x2 x3 y0 y1 y2 y3 : ℕ) :
    sE4 s x0 x1 x2 x3 * sE4 s y0 y1 y2 y3 = sE4 s (x0 + y0) (x1 + y1) (x2 + y2) (x3 + y3) := by
  have c : ∀ i j (m n : ℕ) (r : G), s i ^ m * (s j ^ n * r) = s j ^ n * (s i ^ m * r) := by
    intro i j m n r
    rw [← mul_assoc, ((Commute.pow_pow (hc i j) m n)).eq, mul_assoc]
  have p : ∀ i (m n : ℕ) (r : G), s i ^ m * (s i ^ n * r) = s i ^ (m + n) * r := by
    intro i m n r
    rw [← mul_assoc, ← pow_add]
  simp only [sE4, mul_assoc]
  rw [c 3 0, c 2 0, c 1 0, p 0, c 3 1, c 2 1, p 1, c 3 2, p 2, ← pow_add]

include h3

theorem sE4_mod (x0 x1 x2 x3 : ℕ) :
    sE4 s (x0 % 3) (x1 % 3) (x2 % 3) (x3 % 3) = sE4 s x0 x1 x2 x3 := by
  simp only [sE4, pow_mod3 (h3 _)]

theorem fS_vadd (a c : ℕ) : fS s (vadd a c) = fS s a * fS s c := by
  obtain ⟨e0, e1, e2, e3⟩ := dg_vadd a c
  rw [fS, e0, e1, e2, e3, sE4_mod hc h3, fS, fS, sE4_mul hc]

omit hc h3 in
theorem fS_zero : fS s 0 = 1 := by simp [fS, sE4, dg_zero]

theorem fS_vmulk (k c : ℕ) : fS s (vmulk k c) = fS s c ^ k := by
  induction k with
  | zero => simp [vmulk, fS_zero]
  | succ k ih => rw [vmulk, fS_vadd hc h3, ih, pow_succ]

theorem fS_cube (c : ℕ) : fS s c ^ 3 = 1 := by
  rw [← fS_vmulk hc h3, vmulk_three, fS_zero]

theorem fS_comm (a c : ℕ) : fS s a * fS s c = fS s c * fS s a := by
  rw [← fS_vadd hc h3, ← fS_vadd hc h3, vadd_comm]

theorem fS_inv (a : ℕ) : (fS s a)⁻¹ = fS s (vneg a) := by
  rw [inv_eq_sq (fS_cube hc h3 a), vneg, fS_vmulk hc h3]

theorem conj_fS {g : G} {c0 c1 c2 c3 : ℕ} (h0 : g * s 0 * g⁻¹ = fS s c0)
    (h1 : g * s 1 * g⁻¹ = fS s c1) (h2 : g * s 2 * g⁻¹ = fS s c2)
    (h3' : g * s 3 * g⁻¹ = fS s c3) (a : ℕ) : g * fS s a * g⁻¹ = fS s (lin c0 c1 c2 c3 a) := by
  have e : ∀ x : G, g * x * g⁻¹ = MulAut.conj g x := fun x => rfl
  rw [lin, fS_vadd hc h3, fS_vadd hc h3, fS_vadd hc h3, fS_vmulk hc h3, fS_vmulk hc h3,
    fS_vmulk hc h3, fS_vmulk hc h3, ← h0, ← h1, ← h2, ← h3', e, e, e, e, e, fS, sE4]
  simp only [map_mul, map_pow, mul_assoc]

end Torus

theorem conj_itr {s : Fin 4 → G} {g : G} {F : ℕ → ℕ} (h : ∀ a, g * fS s a * g⁻¹ = fS s (F a))
    (n a : ℕ) : g ^ n * fS s a * (g ^ n)⁻¹ = fS s (itr F n a) := by
  induction n with
  | zero => simp [itr]
  | succ n ih =>
    rw [pow_succ', mul_inv_rev, itr, ← h, ← ih]
    simp only [mul_assoc]

structure Pres (s : Fin 4 → G) (g4 g5 : G) : Prop where
  comm : ∀ i j, s i * s j = s j * s i
  cube : ∀ i, s i ^ 3 = 1
  cube4 : g4 ^ 3 = 1
  cube5 : g5 ^ 3 = 1
  comm45 : g4 * g5 = g5 * g4
  act4 : ∀ i : Fin 4, g4 * s i = fS s (m4 (3 ^ (i : ℕ))) * g4
  act5 : ∀ i : Fin 4, g5 * s i = fS s (m5 (3 ^ (i : ℕ))) * g5
  z_ne : fS s 26 ≠ 1

@[expose] def gQ (g4 g5 : G) (q : ℕ) : G := g4 ^ (q % 3) * g5 ^ (q / 3 % 3)

@[expose] def phi (s : Fin 4 → G) (g4 g5 : G) (m : ℕ) : G := fS s (m % 81) * gQ g4 g5 (m / 81)

section Pres

variable {s : Fin 4 → G} {g4 g5 : G} (hp : Pres s g4 g5)
include hp

theorem conj4 (a : ℕ) : g4 * fS s a * g4⁻¹ = fS s (m4 a) := by
  have h : ∀ i : Fin 4, g4 * s i * g4⁻¹ = fS s (m4 (3 ^ (i : ℕ))) := fun i => by
    rw [hp.act4 i, mul_inv_cancel_right]
  have c : m4 1 = 9 ∧ m4 3 = 1 ∧ m4 9 = 3 ∧ m4 27 = 27 := by decide +kernel
  have e : m4 a = lin (m4 1) (m4 3) (m4 9) (m4 27) a := by
    rw [c.1, c.2.1, c.2.2.1, c.2.2.2]
    rfl
  rw [e]
  exact conj_fS hp.comm hp.cube (h 0) (h 1) (h 2) (h 3) a

theorem conj5 (a : ℕ) : g5 * fS s a * g5⁻¹ = fS s (m5 a) := by
  have h : ∀ i : Fin 4, g5 * s i * g5⁻¹ = fS s (m5 (3 ^ (i : ℕ))) := fun i => by
    rw [hp.act5 i, mul_inv_cancel_right]
  have c : m5 1 = 76 ∧ m5 3 = 68 ∧ m5 9 = 70 ∧ m5 27 = 40 := by decide +kernel
  have e : m5 a = lin (m5 1) (m5 3) (m5 9) (m5 27) a := by
    rw [c.1, c.2.1, c.2.2.1, c.2.2.2]
    rfl
  rw [e]
  exact conj_fS hp.comm hp.cube (h 0) (h 1) (h 2) (h 3) a

theorem conjQ (q a : ℕ) : gQ g4 g5 q * fS s a * (gQ g4 g5 q)⁻¹ = fS s (actQ q a) := by
  rw [actQ, ← conj_itr (conj4 hp), ← conj_itr (conj5 hp), gQ, mul_inv_rev]
  simp only [mul_assoc]

theorem gQ_mul (q r : ℕ) : gQ g4 g5 q * gQ g4 g5 r = gQ g4 g5 (qadd q r) := by
  have e1 : qadd q r % 3 = (q % 3 + r % 3) % 3 := by simp only [qadd]; omega
  have e2 : qadd q r / 3 % 3 = (q / 3 % 3 + r / 3 % 3) % 3 := by simp only [qadd]; omega
  rw [gQ, gQ, gQ, e1, e2, pow_mod3 hp.cube4 (q % 3 + r % 3), pow_mod3 hp.cube5 (q / 3 % 3 + r / 3 % 3),
    pow_add, pow_add, mul_assoc, ← mul_assoc (g5 ^ (q / 3 % 3)),
    ((Commute.pow_pow hp.comm45.symm (q / 3 % 3) (r % 3))).eq]
  simp only [mul_assoc]

theorem phi_pmul (m n : ℕ) : phi s g4 g5 (pmul m n) = phi s g4 g5 m * phi s g4 g5 n := by
  have e : phi s g4 g5 m * phi s g4 g5 n = fS s (m % 81) *
      (gQ g4 g5 (m / 81) * fS s (n % 81) * (gQ g4 g5 (m / 81))⁻¹) *
      (gQ g4 g5 (m / 81) * gQ g4 g5 (n / 81)) := by
    simp only [phi, mul_assoc, inv_mul_cancel_left]
  rw [e, conjQ hp, gQ_mul hp, ← fS_vadd hp.comm hp.cube, phi, pmul_mod, pmul_div]

theorem phi_zero : phi s g4 g5 0 = 1 := by simp [phi, gQ, fS_zero]

theorem fS_eq_one (hm : ModelOK) {a : ℕ} (ha : a < 81) (h1 : fS s a = 1) : a = 0 := by
  obtain ⟨k1, k2, k3, k4, k5, k6, -⟩ := hm
  have hc := hp.comm
  have h3 := hp.cube
  have hn4 : ∀ y, fS s y = 1 → fS s (n4 y) = 1 := fun y hy => by
    rw [n4, fS_vadd hc h3, ← conj4 hp, ← fS_inv hc h3, hy]
    group
  have hn5 : ∀ y, fS s y = 1 → fS s (n5 y) = 1 := fun y hy => by
    rw [n5, fS_vadd hc h3, ← conj5 hp, ← fS_inv hc h3, hy]
    group
  have n4lt : ∀ y, n4 y < 81 := fun y => vadd_lt _ _
  have n5lt : ∀ y, n5 y < 81 := fun y => vadd_lt _ _
  by_contra ha0
  obtain ⟨y, hy, hy1, hy0, hy4⟩ : ∃ y, y < 81 ∧ fS s y = 1 ∧ y ≠ 0 ∧ m4 y = y := by
    by_cases e1 : n4 a = 0
    · exact ⟨a, ha, h1, ha0, k3 a ha e1⟩
    by_cases e2 : n4 (n4 a) = 0
    · exact ⟨n4 a, n4lt a, hn4 a h1, e1, k3 _ (n4lt a) e2⟩
    exact ⟨n4 (n4 a), n4lt _, hn4 _ (hn4 a h1), e2, k3 _ (n4lt _) (k1 a ha)⟩
  obtain ⟨w, hw, hw1, hw0, hw4, hw5⟩ :
      ∃ w, w < 81 ∧ fS s w = 1 ∧ w ≠ 0 ∧ m4 w = w ∧ m5 w = w := by
    have f1 := k5 y hy hy4
    have f2 := k5 _ (n5lt y) f1
    by_cases e1 : n5 y = 0
    · exact ⟨y, hy, hy1, hy0, hy4, k4 y hy e1⟩
    by_cases e2 : n5 (n5 y) = 0
    · exact ⟨n5 y, n5lt y, hn5 y hy1, e1, f1, k4 _ (n5lt y) e2⟩
    exact ⟨n5 (n5 y), n5lt _, hn5 _ (hn5 y hy1), e2, f2, k4 _ (n5lt _) (k2 y hy)⟩
  have hz : fS s 26 = 1 := by
    rcases k6 w hw hw0 hw4 hw5 with rfl | rfl
    · exact hw1
    · have e : vadd 13 13 = 26 := by decide +kernel
      rw [← e, fS_vadd hc h3, hw1, one_mul]
  exact hp.z_ne hz

theorem fS_injOn (hm : ModelOK) {a c : ℕ} (ha : a < 81) (hc : c < 81) (h : fS s a = fS s c) :
    a = c := by
  refine vadd_neg_eq_zero ha hc (fS_eq_one hp hm (vadd_lt _ _) ?_)
  rw [fS_vadd hp.comm hp.cube, ← fS_inv hp.comm hp.cube, h, mul_inv_cancel]

theorem gQ_eq_fS (hm : ModelOK) {q e : ℕ} (hq : q < 9) (h : gQ g4 g5 q = fS s e) : q = 0 := by
  have k7 := hm.2.2.2.2.2.2.1
  have hi : ∀ a, a < 81 → actQ q a = a := fun a ha => by
    refine fS_injOn hp hm (actQ_lt q ha) ha ?_
    rw [← conjQ hp, h, fS_comm hp.comm hp.cube, mul_inv_cancel_right]
  exact k7 q hq (hi 1 (by decide)) (hi 3 (by decide)) (hi 9 (by decide)) (hi 27 (by decide))

theorem gQ_inv (q : ℕ) : (gQ g4 g5 q)⁻¹ = gQ g4 g5 (qadd q q) := by
  refine inv_eq_of_mul_eq_one_right ?_
  have e : gQ g4 g5 (qadd q (qadd q q)) = 1 := by
    have e1 : qadd q (qadd q q) % 3 = 0 := by simp only [qadd]; omega
    have e2 : qadd q (qadd q q) / 3 % 3 = 0 := by simp only [qadd]; omega
    rw [gQ, e1, e2, pow_zero, pow_zero, one_mul]
  rw [gQ_mul hp, e]

theorem phi_injOn (hm : ModelOK) : Set.InjOn (phi s g4 g5) {m | m < 729} := by
  intro m hm' n hn h
  simp only [Set.mem_setOf_eq] at hm' hn
  simp only [phi] at h
  have hg : gQ g4 g5 (qadd (m / 81) (qadd (n / 81) (n / 81))) =
      fS s (vadd (vneg (m % 81)) (n % 81)) := by
    rw [← gQ_mul hp, ← gQ_inv hp, fS_vadd hp.comm hp.cube, ← fS_inv hp.comm hp.cube]
    calc gQ g4 g5 (m / 81) * (gQ g4 g5 (n / 81))⁻¹
        = (fS s (m % 81))⁻¹ * (fS s (m % 81) * gQ g4 g5 (m / 81)) * (gQ g4 g5 (n / 81))⁻¹ := by
          group
      _ = (fS s (m % 81))⁻¹ * fS s (n % 81) := by rw [h, mul_assoc, mul_inv_cancel_right]
  have hq := gQ_eq_fS hp hm (qadd_lt _ _) hg
  have key : ∀ x, x < 9 → ∀ y, y < 9 → qadd x (qadd y y) = 0 → x = y := by decide
  have hqq : m / 81 = n / 81 := key _ (by omega) _ (by omega) hq
  rw [hqq, mul_left_inj] at h
  have ha := fS_injOn hp hm (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h
  omega

theorem fS_pow3 (i : Fin 4) : fS s (3 ^ (i : ℕ)) = s i := by
  fin_cases i <;> simp [fS, sE4, dg]

theorem fS_pow3_sq (i : Fin 4) : fS s (2 * 3 ^ (i : ℕ)) = s i ^ 2 := by
  fin_cases i <;> simp [fS, sE4, dg]

theorem coe_T : (Subgroup.closure (Set.range s) : Set G) = fS s '' {a | a < 81} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, ← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩ | hx
      · exact ⟨_, by have := i.2; simp only [Set.mem_setOf_eq]; interval_cases (i : ℕ) <;> decide,
          fS_pow3 hp i⟩
      · rw [Set.mem_inv] at hx
        obtain ⟨i, hi⟩ := hx
        refine ⟨2 * 3 ^ (i : ℕ), ?_, ?_⟩
        · have := i.2
          simp only [Set.mem_setOf_eq]
          interval_cases (i : ℕ) <;> decide
        · rw [fS_pow3_sq hp, ← inv_eq_sq (hp.cube i), hi, inv_inv]
    | one => exact ⟨0, by simp, fS_zero⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨c, -, rfl⟩ := hy
      exact ⟨vadd a c, vadd_lt a c, fS_vadd hp.comm hp.cube a c⟩
  · rintro _ ⟨a, -, rfl⟩
    have h : ∀ i, s i ∈ Subgroup.closure (Set.range s) := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    simp only [fS, sE4, SetLike.mem_coe]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (h 0) _)
      (Subgroup.pow_mem _ (h 1) _)) (Subgroup.pow_mem _ (h 2) _)) (Subgroup.pow_mem _ (h 3) _)

omit hp in
theorem card_lt (n : ℕ) : Nat.card {m : ℕ | m < n} = n := by
  have e : {m : ℕ | m < n} ≃ Fin n := (Fin.equivSubtype).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_T (hm : ModelOK) : Nat.card (Subgroup.closure (Set.range s)) = 81 := by
  have e : Nat.card (Subgroup.closure (Set.range s)) =
      Nat.card ((Subgroup.closure (Set.range s) : Set G)) := rfl
  have hinj : Set.InjOn (fS s) {a | a < 81} := fun a ha c hc h => fS_injOn hp hm ha hc h
  rw [e, coe_T hp, Nat.card_image_of_injOn hinj, card_lt]

theorem T_comm {x y : G} (hx : x ∈ Subgroup.closure (Set.range s))
    (hy : y ∈ Subgroup.closure (Set.range s)) : x * y = y * x := by
  rw [← SetLike.mem_coe, coe_T hp] at hx hy
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨c, -, rfl⟩ := hy
  exact fS_comm hp.comm hp.cube a c

theorem T_cube {x : G} (hx : x ∈ Subgroup.closure (Set.range s)) : x ^ 3 = 1 := by
  rw [← SetLike.mem_coe, coe_T hp] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact fS_cube hp.comm hp.cube a

@[expose] def gensP (s : Fin 4 → G) (g4 g5 : G) : Set G := Set.range s ∪ {g4, g5}

theorem coe_P : (Subgroup.closure (gensP s g4 g5) : Set G) = phi s g4 g5 '' {m | m < 729} := by
  have hphiS : ∀ a, a < 81 → phi s g4 g5 a = fS s a := fun a ha => by
    simp [phi, gQ, Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha]
  have h4 : phi s g4 g5 81 = g4 := by simp [phi, gQ, fS_zero]
  have h4' : phi s g4 g5 162 = g4 ^ 2 := by simp [phi, gQ, fS_zero]
  have h5 : phi s g4 g5 243 = g5 := by simp [phi, gQ, fS_zero]
  have h5' : phi s g4 g5 486 = g5 ^ 2 := by simp [phi, gQ, fS_zero]
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, ← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with (⟨i, rfl⟩ | rfl | rfl) | hx
      · refine ⟨3 ^ (i : ℕ), ?_, ?_⟩
        · have := i.2
          simp only [Set.mem_setOf_eq]
          interval_cases (i : ℕ) <;> decide
        · rw [hphiS _ (by have := i.2; interval_cases (i : ℕ) <;> decide), fS_pow3 hp]
      · exact ⟨81, by simp, h4⟩
      · exact ⟨243, by simp, h5⟩
      · rw [Set.mem_inv] at hx
        rcases hx with ⟨i, hi⟩ | hx | hx
        · refine ⟨2 * 3 ^ (i : ℕ), ?_, ?_⟩
          · have := i.2
            simp only [Set.mem_setOf_eq]
            interval_cases (i : ℕ) <;> decide
          · rw [hphiS _ (by have := i.2; interval_cases (i : ℕ) <;> decide), fS_pow3_sq hp,
              ← inv_eq_sq (hp.cube i), hi, inv_inv]
        · refine ⟨162, by simp, ?_⟩
          rw [h4', ← inv_eq_sq hp.cube4, ← hx, inv_inv]
        · refine ⟨486, by simp, ?_⟩
          rw [h5', ← inv_eq_sq hp.cube5, ← hx, inv_inv]
    | one => exact ⟨0, by simp, phi_zero hp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨m, -, rfl⟩ := hx
      obtain ⟨n, -, rfl⟩ := hy
      exact ⟨pmul m n, pmul_lt m n, phi_pmul hp m n⟩
  · rintro _ ⟨m, -, rfl⟩
    have hT : Subgroup.closure (Set.range s) ≤ Subgroup.closure (gensP s g4 g5) :=
      Subgroup.closure_mono Set.subset_union_left
    have hs : fS s (m % 81) ∈ Subgroup.closure (Set.range s) := by
      rw [← SetLike.mem_coe, coe_T hp]
      exact ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    have h4m : g4 ∈ Subgroup.closure (gensP s g4 g5) :=
      Subgroup.subset_closure (Or.inr (Or.inl rfl))
    have h5m : g5 ∈ Subgroup.closure (gensP s g4 g5) :=
      Subgroup.subset_closure (Or.inr (Or.inr rfl))
    exact Subgroup.mul_mem _ (hT hs)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ h4m _) (Subgroup.pow_mem _ h5m _))

theorem card_P (hm : ModelOK) : Nat.card (Subgroup.closure (gensP s g4 g5)) = 729 := by
  have e : Nat.card (Subgroup.closure (gensP s g4 g5)) =
      Nat.card ((Subgroup.closure (gensP s g4 g5) : Set G)) := rfl
  rw [e, coe_P hp, Nat.card_image_of_injOn (phi_injOn hp hm), card_lt]

end Pres

theorem T_le_P (s : Fin 4 → G) (g4 g5 : G) :
    Subgroup.closure (Set.range s) ≤ Subgroup.closure (gensP s g4 g5) :=
  Subgroup.closure_mono Set.subset_union_left

end CFSG.KC.F4Syl3

end
