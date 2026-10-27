module

public import Mathlib.Data.List.Sublists
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.C14F4LatticeCheck

@[ext] structure Q4 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

namespace Q4

@[expose] def beq (x y : Q4) : Bool := x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d

instance : BEq Q4 := ⟨beq⟩
instance : Zero Q4 := ⟨⟨0, 0, 0, 0⟩⟩
instance : Add Q4 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Neg Q4 := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Sub Q4 := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩⟩
instance : SMul ℤ Q4 := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩⟩

@[simp] theorem zero_a : (0 : Q4).a = 0 := rfl
@[simp] theorem add_a (x y : Q4) : (x + y).a = x.a + y.a := rfl
@[simp] theorem neg_a (x : Q4) : (-x).a = -x.a := rfl
@[simp] theorem sub_a (x y : Q4) : (x - y).a = x.a - y.a := rfl
@[simp] theorem smul_a (n : ℤ) (x : Q4) : (n • x).a = n * x.a := rfl
@[simp] theorem zero_b : (0 : Q4).b = 0 := rfl
@[simp] theorem add_b (x y : Q4) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_b (x : Q4) : (-x).b = -x.b := rfl
@[simp] theorem sub_b (x y : Q4) : (x - y).b = x.b - y.b := rfl
@[simp] theorem smul_b (n : ℤ) (x : Q4) : (n • x).b = n * x.b := rfl
@[simp] theorem zero_c : (0 : Q4).c = 0 := rfl
@[simp] theorem add_c (x y : Q4) : (x + y).c = x.c + y.c := rfl
@[simp] theorem neg_c (x : Q4) : (-x).c = -x.c := rfl
@[simp] theorem sub_c (x y : Q4) : (x - y).c = x.c - y.c := rfl
@[simp] theorem smul_c (n : ℤ) (x : Q4) : (n • x).c = n * x.c := rfl
@[simp] theorem zero_d : (0 : Q4).d = 0 := rfl
@[simp] theorem add_d (x y : Q4) : (x + y).d = x.d + y.d := rfl
@[simp] theorem neg_d (x : Q4) : (-x).d = -x.d := rfl
@[simp] theorem sub_d (x y : Q4) : (x - y).d = x.d - y.d := rfl
@[simp] theorem smul_d (n : ℤ) (x : Q4) : (n • x).d = n * x.d := rfl

@[expose] def dot (x y : Q4) : ℤ := x.a * y.a + x.b * y.b + x.c * y.c + x.d * y.d

@[expose] def cross (x y z : Q4) : Q4 :=
  ⟨-(x.b * (y.c * z.d - y.d * z.c) - x.c * (y.b * z.d - y.d * z.b) + x.d * (y.b * z.c - y.c * z.b)),
    x.a * (y.c * z.d - y.d * z.c) - x.c * (y.a * z.d - y.d * z.a) + x.d * (y.a * z.c - y.c * z.a),
    -(x.a * (y.b * z.d - y.d * z.b) - x.b * (y.a * z.d - y.d * z.a) + x.d * (y.a * z.b - y.b * z.a)),
    x.a * (y.b * z.c - y.c * z.b) - x.b * (y.a * z.c - y.c * z.a) + x.c * (y.a * z.b - y.b * z.a)⟩

@[expose] def det4 (x y z w : Q4) : ℤ := dot (cross x y z) w

end Q4

open Q4

@[expose] def e0 : Q4 := ⟨1, 0, 0, 0⟩
@[expose] def e1 : Q4 := ⟨0, 1, 0, 0⟩
@[expose] def e2 : Q4 := ⟨0, 0, 1, 0⟩
@[expose] def e3 : Q4 := ⟨0, 0, 0, 1⟩

@[expose] def f4Pos : List Q4 := [⟨0, 0, 0, 1⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 0⟩, ⟨0, 1, 1, 0⟩, ⟨0, 1, 1, 1⟩, ⟨0, 1, 2, 0⟩, ⟨0, 1, 2, 1⟩, ⟨0, 1, 2, 2⟩, ⟨1, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨1, 1, 1, 0⟩, ⟨1, 1, 1, 1⟩, ⟨1, 1, 2, 0⟩, ⟨1, 1, 2, 1⟩, ⟨1, 1, 2, 2⟩, ⟨1, 2, 2, 0⟩, ⟨1, 2, 2, 1⟩, ⟨1, 2, 2, 2⟩, ⟨1, 2, 3, 1⟩, ⟨1, 2, 3, 2⟩, ⟨1, 2, 4, 2⟩, ⟨1, 3, 4, 2⟩, ⟨2, 3, 4, 2⟩]

@[expose] def f4Roots : List Q4 := f4Pos ++ f4Pos.map Neg.neg

@[expose] def f4Lines : List Q4 := [⟨0, 0, 0, 1⟩, ⟨0, 0, 1, -3⟩, ⟨0, 0, 1, -2⟩, ⟨0, 0, 1, -1⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 2, -3⟩, ⟨0, 1, -2, 2⟩, ⟨0, 1, -1, 0⟩, ⟨0, 1, -1, 1⟩, ⟨0, 1, 0, -2⟩, ⟨0, 1, 0, -1⟩, ⟨0, 1, 0, 0⟩, ⟨0, 2, -3, 2⟩, ⟨0, 2, -3, 3⟩, ⟨0, 2, -2, 1⟩, ⟨0, 2, -1, -2⟩, ⟨0, 2, -1, -1⟩, ⟨0, 2, -1, 0⟩, ⟨0, 2, -1, 1⟩, ⟨0, 2, 0, -3⟩, ⟨0, 2, 0, -1⟩, ⟨0, 3, -2, 0⟩, ⟨0, 4, -3, 0⟩, ⟨0, 4, -3, 1⟩, ⟨0, 4, -2, -1⟩, ⟨1, -3, 1, 1⟩, ⟨1, -3, 2, -1⟩, ⟨1, -3, 2, 0⟩, ⟨1, -2, 0, 1⟩, ⟨1, -2, 0, 2⟩, ⟨1, -2, 1, -1⟩, ⟨1, -2, 1, 0⟩, ⟨1, -2, 1, 1⟩, ⟨1, -2, 2, -2⟩, ⟨1, -2, 2, -1⟩, ⟨1, -1, -1, 2⟩, ⟨1, -1, 0, 0⟩, ⟨1, -1, 0, 1⟩, ⟨1, -1, 1, -2⟩, ⟨1, -1, 1, -1⟩, ⟨1, -1, 1, 0⟩, ⟨1, 0, -1, 0⟩, ⟨1, 0, -1, 1⟩, ⟨1, 0, -1, 2⟩, ⟨1, 0, 0, -1⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 1, -2⟩, ⟨1, 1, -2, 1⟩, ⟨1, 1, -2, 2⟩, ⟨1, 1, -1, -1⟩, ⟨1, 1, -1, 0⟩, ⟨1, 1, -1, 1⟩, ⟨1, 1, 0, -2⟩, ⟨1, 1, 0, -1⟩, ⟨1, 2, -2, 0⟩, ⟨1, 2, -2, 1⟩, ⟨1, 2, -1, -1⟩, ⟨2, -4, 1, 1⟩, ⟨2, -4, 1, 2⟩, ⟨2, -4, 2, -1⟩, ⟨2, -4, 2, 1⟩, ⟨2, -4, 3, -2⟩, ⟨2, -4, 3, -1⟩, ⟨2, -3, 1, 0⟩, ⟨2, -3, 1, 1⟩, ⟨2, -3, 2, -1⟩, ⟨2, -2, -1, 2⟩, ⟨2, -2, -1, 3⟩, ⟨2, -2, 0, 1⟩, ⟨2, -2, 1, -2⟩, ⟨2, -2, 1, -1⟩, ⟨2, -2, 1, 0⟩, ⟨2, -2, 1, 1⟩, ⟨2, -2, 2, -3⟩, ⟨2, -2, 2, -1⟩, ⟨2, -1, -1, 1⟩, ⟨2, -1, -1, 2⟩, ⟨2, -1, 0, -1⟩, ⟨2, -1, 0, 0⟩, ⟨2, -1, 0, 1⟩, ⟨2, -1, 1, -2⟩, ⟨2, -1, 1, -1⟩, ⟨2, 0, -2, 1⟩, ⟨2, 0, -2, 3⟩, ⟨2, 0, -1, -1⟩, ⟨2, 0, -1, 0⟩, ⟨2, 0, -1, 1⟩, ⟨2, 0, -1, 2⟩, ⟨2, 0, 0, -1⟩, ⟨2, 0, 1, -3⟩, ⟨2, 0, 1, -2⟩, ⟨2, 1, -2, 1⟩, ⟨2, 1, -1, -1⟩, ⟨2, 1, -1, 0⟩, ⟨2, 2, -3, 1⟩, ⟨2, 2, -3, 2⟩, ⟨2, 2, -2, -1⟩, ⟨2, 2, -2, 1⟩, ⟨2, 2, -1, -2⟩, ⟨2, 2, -1, -1⟩, ⟨3, -3, 1, 0⟩, ⟨3, -2, 0, 0⟩, ⟨3, -2, 0, 1⟩, ⟨3, -2, 1, -1⟩, ⟨3, -1, -1, 1⟩, ⟨3, -1, 0, -1⟩, ⟨3, -1, 0, 0⟩, ⟨3, 0, -1, 0⟩, ⟨4, -4, 1, 0⟩, ⟨4, -4, 1, 1⟩, ⟨4, -4, 2, -1⟩, ⟨4, -2, -1, 1⟩, ⟨4, -2, -1, 2⟩, ⟨4, -2, 0, -1⟩, ⟨4, -2, 0, 1⟩, ⟨4, -2, 1, -2⟩, ⟨4, -2, 1, -1⟩, ⟨4, 0, -2, 1⟩, ⟨4, 0, -1, -1⟩, ⟨4, 0, -1, 0⟩]

@[expose] def xgcdAux : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ × ℤ
  | 0, _, s, t, _, _, _ => (s, t)
  | fuel + 1, r, s, t, r', s', t' =>
    if r' = 0 then (s, t) else
      xgcdAux fuel r' s' t' (r - r / r' * r') (s - r / r' * s') (t - r / r' * t')

@[expose] def xgcd (a b : ℤ) : ℤ × ℤ := xgcdAux 64 a 1 0 b 0 1

@[expose] def comb (k p s : Q4) : Q4 :=
  let uv := xgcd (dot k p) (dot k s)
  uv.1 • p + uv.2 • s

@[expose] def stepK (k : Q4) (S : List Q4) (t : Q4) : List Q4 × Q4 :=
  let p := S.foldl (comb k) 0
  let a := dot k p
  (S.map fun s => s - (dot k s / a) • p, t - (dot k t / a) • p)

@[expose] def runK : List Q4 → List Q4 → Q4 → Q4
  | [], _, t => t
  | k :: K, S, t => runK K (stepK k S t).1 (stepK k S t).2

@[expose] def normalize (k : Q4) : Q4 :=
  let g : ℤ := ((k.a.gcd k.b).gcd (k.c.gcd k.d) : ℕ)
  let k' : Q4 := ⟨k.a / g, k.b / g, k.c / g, k.d / g⟩
  if 0 < k'.a ∨ (k'.a = 0 ∧ (0 < k'.b ∨ (k'.b = 0 ∧ (0 < k'.c ∨ (k'.c = 0 ∧ 0 < k'.d))))) then k'
  else -k'

@[expose] def barEq (K : List Q4) (u v : Q4) : Bool := K.all fun k => dot k u == dot k v

@[expose] def classSize (K : List Q4) (β : Q4) : ℕ :=
  (if K.all (fun k => dot k β == 0) then 4 else 0) + (f4Roots.filter fun γ => barEq K γ β).length

@[expose] def latOK (K : List Q4) : Bool :=
  let G := f4Roots.map fun β => (classSize K β : ℤ) • β
  [e0, e1, e2, e3].all fun e => K.all fun k => dot k (runK K G ((6 : ℤ) • e)) == 0

@[expose] def coef : List ℤ := [-2, -1, 0, 1, 2]

@[expose] def dep3 (x y z : Q4) : Bool :=
  coef.any fun a => coef.any fun b => coef.any fun c =>
    !(a == 0 && b == 0 && c == 0) && (a • x + b • y + c • z == 0)

@[expose] def dep2 (x y : Q4) : Bool :=
  coef.any fun a => coef.any fun b => !(a == 0 && b == 0) && (a • x + b • y == 0)

@[expose] def dep1 (x : Q4) : Bool := x == 0

@[expose] def line3 (x y z : Q4) : Bool :=
  let k := normalize (cross x y z)
  f4Lines.any (beq k) && dot x k == 0 && dot y k == 0 && dot z k == 0 && det4 x y z k != 0

@[expose] def case3 (x y z : Q4) : Bool := line3 x y z || dep3 x y z

@[expose] def basis : List Q4 := [e0, e1, e2, e3]

@[expose] def compl2 (x y : Q4) : Bool :=
  let C := basis.map (cross x y)
  C.any fun k₁ => C.any fun k₂ =>
    dot x k₁ == 0 && dot y k₁ == 0 && dot x k₂ == 0 && dot y k₂ == 0 &&
      det4 x y k₁ k₂ != 0 && latOK [k₁, k₂]

@[expose] def case2 (x y : Q4) : Bool := compl2 x y || dep2 x y

@[expose] def compl1 (x : Q4) : Bool :=
  let C := basis.flatMap fun u => basis.map (cross x u)
  C.any fun k₁ => C.any fun k₂ => C.any fun k₃ =>
    dot x k₁ == 0 && dot x k₂ == 0 && dot x k₃ == 0 &&
      det4 x k₁ k₂ k₃ != 0 && latOK [k₁, k₂, k₃]

@[expose] def case1 (x : Q4) : Bool := compl1 x || dep1 x


theorem q4_add_assoc (x y z : Q4) : x + y + z = x + (y + z) := by
  ext <;> simp only [add_a, add_b, add_c, add_d] <;> ring

theorem beq_iff {x y : Q4} : beq x y = true ↔ x = y := by
  simp only [beq, Bool.and_eq_true, beq_iff_eq, Q4.ext_iff, and_assoc]

theorem cramer (x y z w l : Q4) : det4 x y z w • l =
    det4 l y z w • x + det4 x l z w • y + det4 x y l w • z + det4 x y z l • w := by
  ext <;> simp only [smul_a, smul_b, smul_c, smul_d, add_a, add_b, add_c, add_d, det4, cross,
    dot] <;> ring

theorem core {l x u v : Q4} {D : ℤ} (hD : D ≠ 0) (h : D • l = u + v) (hu : dot l u = 0)
    (huv : dot u v = 0) (hx : dot x v = 0) : dot x l = 0 := by
  obtain ⟨l1, l2, l3, l4⟩ := l
  obtain ⟨x1, x2, x3, x4⟩ := x
  obtain ⟨u1, u2, u3, u4⟩ := u
  obtain ⟨v1, v2, v3, v4⟩ := v
  simp only [Q4.ext_iff, smul_a, smul_b, smul_c, smul_d, add_a, add_b, add_c, add_d] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [dot] at hu huv hx ⊢
  have huu : u1 * u1 + u2 * u2 + u3 * u3 + u4 * u4 = 0 := by
    linear_combination D * hu - huv - u1 * h1 - u2 * h2 - u3 * h3 - u4 * h4
  obtain ⟨hu1, hu2, hu3, hu4⟩ : u1 = 0 ∧ u2 = 0 ∧ u3 = 0 ∧ u4 = 0 := by
    have := mul_self_nonneg u1; have := mul_self_nonneg u2
    have := mul_self_nonneg u3; have := mul_self_nonneg u4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  subst hu1 hu2 hu3 hu4
  have : D * (x1 * l1 + x2 * l2 + x3 * l3 + x4 * l4) = 0 := by
    linear_combination hx + x1 * h1 + x2 * h2 + x3 * h3 + x4 * h4
  exact (mul_eq_zero.1 this).resolve_left hD

@[expose] def Frame (B K : List Q4) : Prop :=
  (∀ b ∈ B, ∀ k ∈ K, dot b k = 0) ∧
    ∀ l x, (∀ b ∈ B, dot b l = 0) → (∀ k ∈ K, dot k x = 0) → dot x l = 0

theorem frame3 {x y z k : Q4} (hx : dot x k = 0) (hy : dot y k = 0) (hz : dot z k = 0)
    (hD : det4 x y z k ≠ 0) : Frame [x, y, z] [k] := by
  refine ⟨by simp [hx, hy, hz], fun l u hB hK => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hB hK
  obtain ⟨hxl, hyl, hzl⟩ := hB
  refine core hD (cramer x y z k l) ?_ ?_ ?_ <;> simp only [dot, add_a, add_b, add_c, add_d,
    smul_a, smul_b, smul_c, smul_d] at * 
  · linear_combination det4 l y z k * hxl + det4 x l z k * hyl + det4 x y l k * hzl
  · linear_combination det4 x y z l * (det4 l y z k * hx + det4 x l z k * hy + det4 x y l k * hz)
  · linear_combination det4 x y z l * hK

theorem frame2 {x y k₁ k₂ : Q4} (hx₁ : dot x k₁ = 0) (hy₁ : dot y k₁ = 0) (hx₂ : dot x k₂ = 0)
    (hy₂ : dot y k₂ = 0) (hD : det4 x y k₁ k₂ ≠ 0) : Frame [x, y] [k₁, k₂] := by
  refine ⟨by simp [hx₁, hy₁, hx₂, hy₂], fun l u hB hK => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hB hK
  obtain ⟨hxl, hyl⟩ := hB
  obtain ⟨hk₁, hk₂⟩ := hK
  have h := cramer x y k₁ k₂ l
  rw [q4_add_assoc] at h
  refine core hD h ?_ ?_ ?_ <;> simp only [dot, add_a, add_b, add_c, add_d,
    smul_a, smul_b, smul_c, smul_d] at *
  · linear_combination det4 l y k₁ k₂ * hxl + det4 x l k₁ k₂ * hyl
  · linear_combination det4 x y l k₂ * (det4 l y k₁ k₂ * hx₁ + det4 x l k₁ k₂ * hy₁) +
      det4 x y k₁ l * (det4 l y k₁ k₂ * hx₂ + det4 x l k₁ k₂ * hy₂)
  · linear_combination det4 x y l k₂ * hk₁ + det4 x y k₁ l * hk₂

theorem frame1 {x k₁ k₂ k₃ : Q4} (h₁ : dot x k₁ = 0) (h₂ : dot x k₂ = 0) (h₃ : dot x k₃ = 0)
    (hD : det4 x k₁ k₂ k₃ ≠ 0) : Frame [x] [k₁, k₂, k₃] := by
  refine ⟨by simp [h₁, h₂, h₃], fun l u hB hK => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hB hK
  obtain ⟨hk₁, hk₂, hk₃⟩ := hK
  have h := cramer x k₁ k₂ k₃ l
  rw [q4_add_assoc, q4_add_assoc] at h
  refine core hD h ?_ ?_ ?_ <;> simp only [dot, add_a, add_b, add_c, add_d,
    smul_a, smul_b, smul_c, smul_d] at *
  · linear_combination det4 l k₁ k₂ k₃ * hB
  · linear_combination det4 l k₁ k₂ k₃ * (det4 x l k₂ k₃ * h₁ + det4 x k₁ l k₃ * h₂ +
      det4 x k₁ k₂ l * h₃)
  · linear_combination det4 x l k₂ k₃ * hk₁ + det4 x k₁ l k₃ * hk₂ + det4 x k₁ k₂ l * hk₃

theorem frame0 : Frame [] basis := by
  refine ⟨by simp, fun l u _ hK => ?_⟩
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    e0, e1, e2, e3, dot] at hK
  obtain ⟨h0, h1, h2, h3⟩ := hK
  simp only [dot]
  linear_combination l.a * h0 + l.b * h1 + l.c * h2 + l.d * h3

@[expose] def linesOK (_ : Unit := ()) : Bool := f4Lines.all fun k => latOK [k]

@[expose] def rank3OK (_ : Unit := ()) : Bool :=
  (f4Pos.sublistsLen 3).all fun l => match l with
    | [x, y, z] => case3 x y z
    | _ => false

@[expose] def rank2OK (_ : Unit := ()) : Bool :=
  (f4Pos.sublistsLen 2).all fun l => match l with
    | [x, y] => case2 x y
    | _ => false

@[expose] def rank1OK (_ : Unit := ()) : Bool := f4Pos.all case1

@[expose] def rank0OK (_ : Unit := ()) : Bool := latOK basis

theorem line3_spec {x y z : Q4} (h : line3 x y z = true) (hL : linesOK = true) :
    ∃ K, latOK K = true ∧ Frame [x, y, z] K := by
  unfold line3 at h
  generalize normalize (cross x y z) = k at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨k', hk', hkk'⟩, hx⟩, hy⟩, hz⟩, hD⟩ := h
  obtain rfl := beq_iff.1 hkk'
  exact ⟨[k], List.all_eq_true.1 hL k hk', frame3 hx hy hz hD⟩

theorem compl2_spec {x y : Q4} (h : compl2 x y = true) :
    ∃ K, latOK K = true ∧ Frame [x, y] K := by
  unfold compl2 at h
  generalize basis.map (cross x y) = C at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨k₁, -, k₂, -, ⟨⟨⟨⟨⟨hx₁, hy₁⟩, hx₂⟩, hy₂⟩, hD⟩, hlat⟩⟩ := h
  exact ⟨[k₁, k₂], hlat, frame2 hx₁ hy₁ hx₂ hy₂ hD⟩

theorem compl1_spec {x : Q4} (h : compl1 x = true) :
    ∃ K, latOK K = true ∧ Frame [x] K := by
  unfold compl1 at h
  generalize basis.flatMap (fun u => basis.map (cross x u)) = C at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨k₁, -, k₂, -, k₃, -, ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, hD⟩, hlat⟩⟩ := h
  exact ⟨[k₁, k₂, k₃], hlat, frame1 h₁ h₂ h₃ hD⟩

theorem dep3_spec {x y z : Q4} (h : dep3 x y z = true) :
    ∃ a b c : ℤ, ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧ a • x + b • y + c • z = 0 := by
  simp only [dep3, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_iff_eq] at h
  obtain ⟨a, -, b, -, c, -, hne, heq⟩ := h
  refine ⟨a, b, c, ?_, ?_⟩
  · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hne
    tauto
  · revert heq
    simp only [BEq.beq, beq_iff]
    exact id

theorem dep2_spec {x y : Q4} (h : dep2 x y = true) :
    ∃ a b : ℤ, ¬ (a = 0 ∧ b = 0) ∧ a • x + b • y = 0 := by
  simp only [dep2, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨a, -, b, -, hne, heq⟩ := h
  refine ⟨a, b, ?_, ?_⟩
  · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hne
    tauto
  · revert heq
    simp only [BEq.beq, beq_iff]
    exact id

theorem dep1_spec {x : Q4} (h : dep1 x = true) : x = 0 := by
  revert h
  simp only [dep1, BEq.beq, beq_iff]
  exact id

end CFSG.HardMathSupport.C14F4LatticeCheck
