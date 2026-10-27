module

public import CFSG.LieType.Chevalley.EvenRootCommutatorG2
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate3951

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

@[expose] def g2r : Fin Tag.G2.rank → ℤ := ![0, 1]

@[expose] def g2a : Fin Tag.G2.rank → ℤ := ![1, 0]

@[expose] def g2u : Fin Tag.G2.rank → ℤ := ![1, 1]

@[expose] def g2v : Fin Tag.G2.rank → ℤ := ![1, 2]

@[expose] def g2b : Fin Tag.G2.rank → ℤ := ![1, 3]

@[expose] def g2c : Fin Tag.G2.rank → ℤ := ![2, 3]

@[expose] def g2nr : Fin Tag.G2.rank → ℤ := ![0, -1]

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem two_eq_zero_K : (2 : K) = 0 := CharTwo.two_eq_zero

theorem pinnedX_mul_self (α : Fin Tag.G2.rank → ℤ) (x : K) : X α x * X α x = 1 := by
  rw [← pinnedX_add, ← two_mul, two_eq_zero_K, zero_mul, pinnedX_zero]

theorem pinnedX_inv_eq (α : Fin Tag.G2.rank → ℤ) (x : K) : (X α x)⁻¹ = X α x :=
  inv_eq_of_mul_eq_one_right (pinnedX_mul_self α x)

omit [CharP K 2] in
theorem merge (α : Fin Tag.G2.rank → ℤ) (x y : K) (w : ModGL .G2 K) :
    X α x * (X α y * w) = X α (x + y) * w := by
  rw [pinnedX_add, mul_assoc]

theorem mul_eq_of_commutatorElement_eq {G : Type*} [Group G] {g h k : G} (hk : ⁅g, h⁆ = k)
    (hg : g * g = 1) : h * g = g * k * h := by
  rw [← hk, commutatorElement_def]
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [hg']
  group
  rw [hg, one_mul]

theorem mul_eq_of_commutatorElement_eq' {G : Type*} [Group G] {g h k : G} (hk : ⁅g, h⁆ = k) :
    g * h = k * h * g := by
  rw [← hk, commutatorElement_def]
  group

theorem comm_a_r (x y : K) : ⁅X g2a x, X g2r y⁆ =
    X g2u (x * y) * X g2v (x * y ^ 2) * X g2b (x * y ^ 3) * X g2c (x ^ 2 * y ^ 3) :=
  (g2_even_root_commutator_table x y).1

theorem comm_r_u (x y : K) : ⁅X g2r x, X g2u y⁆ = X g2c (x * y ^ 2) * X g2b (x ^ 2 * y) :=
  (g2_even_root_commutator_table x y).2.1

theorem comm_r_v (x y : K) : ⁅X g2r x, X g2v y⁆ = X g2b (x * y) :=
  (g2_even_root_commutator_table x y).2.2.1

theorem comm_a_b (x y : K) : ⁅X g2a x, X g2b y⁆ = X g2c (x * y) :=
  (g2_even_root_commutator_table x y).2.2.2.1

theorem comm_u_v (x y : K) : ⁅X g2u x, X g2v y⁆ = X g2c (x * y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.1

theorem comm_v_nr (x y : K) : ⁅X g2v x, X g2nr y⁆ = X g2a (x * y ^ 2) * X g2c (x ^ 2 * y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.1

theorem commute_a_u (x y : K) : Commute (X g2a x) (X g2u y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.1

theorem commute_a_v (x y : K) : Commute (X g2a x) (X g2v y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.1

theorem commute_a_c (x y : K) : Commute (X g2a x) (X g2c y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.1

theorem commute_r_b (x y : K) : Commute (X g2r x) (X g2b y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.1

theorem commute_r_c (x y : K) : Commute (X g2r x) (X g2c y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.1

theorem commute_u_b (x y : K) : Commute (X g2u x) (X g2b y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_u_c (x y : K) : Commute (X g2u x) (X g2c y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_v_b (x y : K) : Commute (X g2v x) (X g2b y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_v_c (x y : K) : Commute (X g2v x) (X g2c y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem commute_b_c (x y : K) : Commute (X g2b x) (X g2c y) :=
  (g2_even_root_commutator_table x y).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem swap_of_commute {G : Type*} [Group G] {g h : G} (hc : Commute g h) (w : G) :
    h * (g * w) = g * (h * w) := by
  rw [← mul_assoc, ← mul_assoc, hc.eq]

theorem swap_c_r (x y : K) (w : ModGL .G2 K) : X g2c x * (X g2r y * w) = X g2r y * (X g2c x * w) :=
  swap_of_commute (commute_r_c y x) w

theorem swap_b_r (x y : K) (w : ModGL .G2 K) : X g2b x * (X g2r y * w) = X g2r y * (X g2b x * w) :=
  swap_of_commute (commute_r_b y x) w

theorem swap_c_a (x y : K) (w : ModGL .G2 K) : X g2c x * (X g2a y * w) = X g2a y * (X g2c x * w) :=
  swap_of_commute (commute_a_c y x) w

theorem swap_u_a (x y : K) (w : ModGL .G2 K) : X g2u x * (X g2a y * w) = X g2a y * (X g2u x * w) :=
  swap_of_commute (commute_a_u y x) w

theorem swap_v_a (x y : K) (w : ModGL .G2 K) : X g2v x * (X g2a y * w) = X g2a y * (X g2v x * w) :=
  swap_of_commute (commute_a_v y x) w

theorem swap_b_u (x y : K) (w : ModGL .G2 K) : X g2b x * (X g2u y * w) = X g2u y * (X g2b x * w) :=
  swap_of_commute (commute_u_b y x) w

theorem swap_c_u (x y : K) (w : ModGL .G2 K) : X g2c x * (X g2u y * w) = X g2u y * (X g2c x * w) :=
  swap_of_commute (commute_u_c y x) w

theorem swap_b_v (x y : K) (w : ModGL .G2 K) : X g2b x * (X g2v y * w) = X g2v y * (X g2b x * w) :=
  swap_of_commute (commute_v_b y x) w

theorem swap_c_v (x y : K) (w : ModGL .G2 K) : X g2c x * (X g2v y * w) = X g2v y * (X g2c x * w) :=
  swap_of_commute (commute_v_c y x) w

theorem swap_c_b (x y : K) (w : ModGL .G2 K) : X g2c x * (X g2b y * w) = X g2b y * (X g2c x * w) :=
  swap_of_commute (commute_b_c y x) w

theorem swap_v_u (x y : K) (w : ModGL .G2 K) :
    X g2v x * (X g2u y * w) = X g2u y * (X g2v x * (X g2c (y * x) * w)) := by
  have h := mul_eq_of_commutatorElement_eq (comm_u_v y x) (pinnedX_mul_self _ _)
  rw [← mul_assoc, h]
  simp only [mul_assoc]
  rw [swap_c_v]

theorem swap_b_a (x y : K) (w : ModGL .G2 K) :
    X g2b x * (X g2a y * w) = X g2a y * (X g2b x * (X g2c (y * x) * w)) := by
  have h := mul_eq_of_commutatorElement_eq (comm_a_b y x) (pinnedX_mul_self _ _)
  rw [← mul_assoc, h]
  simp only [mul_assoc]
  rw [swap_c_b]

theorem swap_v_r (x y : K) (w : ModGL .G2 K) :
    X g2v x * (X g2r y * w) = X g2r y * (X g2v x * (X g2b (y * x) * w)) := by
  have h := mul_eq_of_commutatorElement_eq (comm_r_v y x) (pinnedX_mul_self _ _)
  rw [← mul_assoc, h]
  simp only [mul_assoc]
  rw [swap_b_v]

theorem swap_u_r (x y : K) (w : ModGL .G2 K) :
    X g2u x * (X g2r y * w) =
      X g2r y * (X g2u x * (X g2b (y ^ 2 * x) * (X g2c (y * x ^ 2) * w))) := by
  have h := mul_eq_of_commutatorElement_eq (comm_r_u y x) (pinnedX_mul_self _ _)
  rw [← mul_assoc, h]
  simp only [mul_assoc]
  rw [swap_b_u, swap_c_u, swap_c_b]

omit [CharP K 2] in
theorem tail_congr {α : Fin Tag.G2.rank → ℤ} {x x' : K} {w w' : ModGL .G2 K} (hx : x = x')
    (hw : w = w') : X α x * w = X α x' * w' := by
  rw [hx, hw]

omit [CharP K 2] in
theorem ofNat_eq_mod_two {L : Type} [Field L] [CharP L 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : L) = ((n % 2 : ℕ) : L) := by
  rw [← Nat.cast_ofNat, CharP.cast_eq_mod L 2]
  rfl

macro "char2_ring" : tactic => `(tactic| first
  | ring1
  | (ring_nf
     (try simp only [ofNat_eq_mod_two, Nat.reduceMod, Nat.cast_zero, Nat.cast_one, mul_zero,
       zero_mul, mul_one, one_mul, add_zero, zero_add])
     (try ring_nf)))

theorem swap_a_r (x y : K) (w : ModGL .G2 K) :
    X g2a x * (X g2r y * w) = X g2r y * (X g2a x * (X g2u (x * y) * (X g2v (x * y ^ 2) *
      (X g2b (x * y ^ 3) * (X g2c (x ^ 2 * y ^ 3) * w))))) := by
  rw [← mul_assoc, mul_eq_of_commutatorElement_eq' (comm_a_r x y)]
  simp only [mul_assoc, swap_c_r, swap_b_r, swap_v_r, swap_u_r, swap_c_a, swap_b_a, swap_v_a,
    swap_u_a, swap_c_b, swap_c_v, swap_b_v, merge]
  repeat' first | apply tail_congr | rfl
  all_goals char2_ring

@[expose] def g2N (A B C D E F : K) : ModGL .G2 K :=
  X g2r A * X g2a B * X g2u C * X g2v D * X g2b E * X g2c F

omit [CharP K 2] in
theorem g2N_mul_c (A B C D E F t : K) : g2N A B C D E F * X g2c t = g2N A B C D E (F + t) := by
  have key : ∀ w, g2N A B C D E F * (X g2c t * w) = g2N A B C D E (F + t) * w := by
    intro w
    simp only [g2N, mul_assoc, merge]
  simpa only [mul_one] using key 1

theorem g2N_mul_b (A B C D E F t : K) : g2N A B C D E F * X g2b t = g2N A B C D (E + t) F := by
  have key : ∀ w, g2N A B C D E F * (X g2b t * w) = g2N A B C D (E + t) F * w := by
    intro w
    simp only [g2N, mul_assoc, swap_c_b, merge]
  simpa only [mul_one] using key 1

theorem g2N_mul_v (A B C D E F t : K) : g2N A B C D E F * X g2v t = g2N A B C (D + t) E F := by
  have key : ∀ w, g2N A B C D E F * (X g2v t * w) = g2N A B C (D + t) E F * w := by
    intro w
    simp only [g2N, mul_assoc, swap_c_v, swap_b_v, merge]
  simpa only [mul_one] using key 1

theorem g2N_mul_u (A B C D E F t : K) :
    g2N A B C D E F * X g2u t = g2N A B (C + t) D E (F + t * D) := by
  have key : ∀ w, g2N A B C D E F * (X g2u t * w) = g2N A B (C + t) D E (F + t * D) * w := by
    intro w
    simp only [g2N, mul_assoc, swap_c_u, swap_b_u, swap_v_u, swap_c_b, merge]
    repeat' first | apply tail_congr | rfl
    all_goals char2_ring
  simpa only [mul_one] using key 1

theorem g2N_mul_a (A B C D E F t : K) :
    g2N A B C D E F * X g2a t = g2N A (B + t) C D E (F + t * E) := by
  have key : ∀ w, g2N A B C D E F * (X g2a t * w) = g2N A (B + t) C D E (F + t * E) * w := by
    intro w
    simp only [g2N, mul_assoc, swap_c_a, swap_b_a, swap_v_a, swap_u_a, merge]
    repeat' first | apply tail_congr | rfl
    all_goals char2_ring
  simpa only [mul_one] using key 1

theorem g2N_mul_r (A B C D E F t : K) :
    g2N A B C D E F * X g2r t =
      g2N (A + t) B (C + B * t) (D + B * t ^ 2) (E + B * t ^ 3 + C * t ^ 2 + D * t)
        (F + B ^ 2 * t ^ 3 + B * C * t ^ 2 + C ^ 2 * t) := by
  have key : ∀ w, g2N A B C D E F * (X g2r t * w) =
      g2N (A + t) B (C + B * t) (D + B * t ^ 2) (E + B * t ^ 3 + C * t ^ 2 + D * t)
        (F + B ^ 2 * t ^ 3 + B * C * t ^ 2 + C ^ 2 * t) * w := by
    intro w
    simp only [g2N, mul_assoc, swap_c_r, swap_b_r, swap_v_r, swap_u_r, swap_a_r, swap_c_b,
      swap_c_v, swap_b_v, swap_c_u, swap_b_u, swap_v_u, merge]
    repeat' first | apply tail_congr | rfl
    all_goals char2_ring
  simpa only [mul_one] using key 1

omit [CharP K 2] in
theorem g2N_eq_g2N {A B C D E F A' B' C' D' E' F' : K} (hA : A = A') (hB : B = B') (hC : C = C')
    (hD : D = D') (hE : E = E') (hF : F = F') : g2N A B C D E F = g2N A' B' C' D' E' F' := by
  rw [hA, hB, hC, hD, hE, hF]

omit [CharP K 2] in
theorem g2N_zero : g2N (0 : K) 0 0 0 0 0 = 1 := by
  simp only [g2N, pinnedX_zero, mul_one]

omit [CharP K 2] in
theorem pinnedX_r_eq_g2N (s : K) : X g2r s = g2N s 0 0 0 0 0 := by
  simp only [g2N, pinnedX_zero, mul_one]

omit [CharP K 2] in
theorem pinnedX_a_eq_g2N (s : K) : X g2a s = g2N 0 s 0 0 0 0 := by
  simp only [g2N, pinnedX_zero, mul_one, one_mul]

omit [CharP K 2] in
theorem pinnedX_u_eq_g2N (s : K) : X g2u s = g2N 0 0 s 0 0 0 := by
  simp only [g2N, pinnedX_zero, mul_one, one_mul]

omit [CharP K 2] in
theorem pinnedX_v_eq_g2N (s : K) : X g2v s = g2N 0 0 0 s 0 0 := by
  simp only [g2N, pinnedX_zero, mul_one, one_mul]

omit [CharP K 2] in
theorem pinnedX_b_eq_g2N (s : K) : X g2b s = g2N 0 0 0 0 s 0 := by
  simp only [g2N, pinnedX_zero, mul_one, one_mul]

omit [CharP K 2] in
theorem pinnedX_c_eq_g2N (s : K) : X g2c s = g2N 0 0 0 0 0 s := by
  simp only [g2N, pinnedX_zero, one_mul]

omit [CharP K 2] in
theorem mul_g2N (g : ModGL .G2 K) (A B C D E F : K) :
    g * g2N A B C D E F =
      g * X g2r A * X g2a B * X g2u C * X g2v D * X g2b E * X g2c F := by
  simp only [g2N, mul_assoc]

theorem g2N_mul_self (A B C D E F : K) :
    g2N A B C D E F * g2N A B C D E F =
      g2N 0 0 (A * B) (A ^ 2 * B) (A ^ 3 * B + A ^ 2 * C + A * D)
        (A * C ^ 2 + B * E + A * B * D + C * D + A ^ 2 * B * C) := by
  rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem conj_r (s A B C D E F : K) :
    X g2r s * g2N A B C D E F * X g2r s =
      g2N A B (C + B * s) (D + B * s ^ 2) (E + B * s ^ 3 + C * s ^ 2 + D * s)
        (F + B ^ 2 * s ^ 3 + B * C * s ^ 2 + C ^ 2 * s) := by
  have e : X g2r s * g2N A B C D E F = g2N s 0 0 0 0 0 * g2N A B C D E F := by
    rw [← pinnedX_r_eq_g2N]
  rw [e, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c, g2N_mul_r]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem conj_a (s A B C D E F : K) :
    X g2a s * g2N A B C D E F * X g2a s =
      g2N A B (C + A * s) (D + A ^ 2 * s) (E + A ^ 3 * s)
        (F + A ^ 3 * B * s + A ^ 2 * C * s + E * s) := by
  have e : X g2a s * g2N A B C D E F = g2N 0 s 0 0 0 0 * g2N A B C D E F := by
    rw [← pinnedX_a_eq_g2N]
  rw [e, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c, g2N_mul_a]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem conj_u (s A B C D E F : K) :
    X g2u s * g2N A B C D E F * X g2u s =
      g2N A B C D (E + A ^ 2 * s) (F + A * s ^ 2 + A ^ 2 * B * s + D * s) := by
  have e : X g2u s * g2N A B C D E F = g2N 0 0 s 0 0 0 * g2N A B C D E F := by
    rw [← pinnedX_u_eq_g2N]
  rw [e, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c, g2N_mul_u]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem conj_v (s A B C D E F : K) :
    X g2v s * g2N A B C D E F * X g2v s =
      g2N A B C D (E + A * s) (F + A * B * s + C * s) := by
  have e : X g2v s * g2N A B C D E F = g2N 0 0 0 s 0 0 * g2N A B C D E F := by
    rw [← pinnedX_v_eq_g2N]
  rw [e, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c, g2N_mul_v]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem conj_b (s A B C D E F : K) :
    X g2b s * g2N A B C D E F * X g2b s = g2N A B C D E (F + B * s) := by
  have e : X g2b s * g2N A B C D E F = g2N 0 0 0 0 s 0 * g2N A B C D E F := by
    rw [← pinnedX_b_eq_g2N]
  rw [e, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c, g2N_mul_b]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem conj_c (s A B C D E F : K) :
    X g2c s * g2N A B C D E F * X g2c s = g2N A B C D E F := by
  have e : X g2c s * g2N A B C D E F = g2N 0 0 0 0 0 s * g2N A B C D E F := by
    rw [← pinnedX_c_eq_g2N]
  rw [e, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c, g2N_mul_c]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

section Roots

open CFSG.LieType.Chevalley.RootOps

@[expose] def g2Pos : Fin 6 → Fin Tag.G2.rank → ℤ := ![g2r, g2a, g2u, g2v, g2b, g2c]

theorem g2r_eq : g2r = orbitCertRoot .G2 6 := List.ofFn_injective (by decide +kernel)
theorem g2a_eq : g2a = orbitCertRoot .G2 7 := List.ofFn_injective (by decide +kernel)
theorem g2u_eq : g2u = orbitCertRoot .G2 8 := List.ofFn_injective (by decide +kernel)
theorem g2v_eq : g2v = orbitCertRoot .G2 9 := List.ofFn_injective (by decide +kernel)
theorem g2b_eq : g2b = orbitCertRoot .G2 10 := List.ofFn_injective (by decide +kernel)
theorem g2c_eq : g2c = orbitCertRoot .G2 11 := List.ofFn_injective (by decide +kernel)
theorem g2nr_eq : g2nr = orbitCertRoot .G2 5 := List.ofFn_injective (by decide +kernel)

theorem isRoot_g2r : IsRoot .G2 g2r := by rw [g2r_eq]; exact isRoot_decodeVec_witness (by decide)
theorem isRoot_g2a : IsRoot .G2 g2a := by rw [g2a_eq]; exact isRoot_decodeVec_witness (by decide)
theorem isRoot_g2u : IsRoot .G2 g2u := by rw [g2u_eq]; exact isRoot_decodeVec_witness (by decide)
theorem isRoot_g2v : IsRoot .G2 g2v := by rw [g2v_eq]; exact isRoot_decodeVec_witness (by decide)
theorem isRoot_g2b : IsRoot .G2 g2b := by rw [g2b_eq]; exact isRoot_decodeVec_witness (by decide)
theorem isRoot_g2c : IsRoot .G2 g2c := by rw [g2c_eq]; exact isRoot_decodeVec_witness (by decide)
theorem isRoot_g2nr : IsRoot .G2 g2nr := by
  rw [g2nr_eq]; exact isRoot_decodeVec_witness (by decide)

theorem g2Pos_injective : Function.Injective g2Pos := by
  unfold g2Pos g2r g2a g2u g2v g2b g2c
  decide

theorem g2Pos_pos (i : Fin 6) : IsRoot .G2 (g2Pos i) ∧ 0 < height (g2Pos i) := by
  fin_cases i
  · exact ⟨isRoot_g2r, by decide⟩
  · exact ⟨isRoot_g2a, by decide⟩
  · exact ⟨isRoot_g2u, by decide⟩
  · exact ⟨isRoot_g2v, by decide⟩
  · exact ⟨isRoot_g2b, by decide⟩
  · exact ⟨isRoot_g2c, by decide⟩

theorem g2_rootCertificate_length : Tag.G2.rootCertificate.roots.length = 12 := by decide

@[expose] def g2RootList : List (Fin Tag.G2.rank → ℤ) :=
  [g2r, g2a, g2u, g2v, g2b, g2c, -g2r, -g2a, -g2u, -g2v, -g2b, -g2c]

theorem g2_root_cases {v : Fin Tag.G2.rank → ℤ} (hv : IsRoot .G2 v) :
    v = g2r ∨ v = g2a ∨ v = g2u ∨ v = g2v ∨ v = g2b ∨ v = g2c ∨ v = -g2r ∨ v = -g2a ∨
      v = -g2u ∨ v = -g2v ∨ v = -g2b ∨ v = -g2c := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .G2)).1 hv
  rw [g2_rootCertificate_length] at hk
  have key : ∀ k < 12, ∃ w ∈ g2RootList,
      List.ofFn (Tag.G2.rootCertificate.root k) = List.ofFn w := by
    unfold g2RootList g2r g2a g2u g2v g2b g2c
    decide +kernel
  obtain ⟨w, hw, hkw⟩ := key k hk
  rw [List.ofFn_injective hkw]
  simpa only [g2RootList, List.mem_cons, List.not_mem_nil, or_false] using hw

theorem range_g2Pos :
    Set.range g2Pos = {β : Fin Tag.G2.rank → ℤ | IsRoot .G2 β ∧ 0 < height β} := by
  ext β
  constructor
  · rintro ⟨i, rfl⟩
    exact g2Pos_pos i
  · rintro ⟨hβ, hpos⟩
    rcases g2_root_cases hβ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    all_goals exact absurd hpos (by decide)

omit [CharP K 2] in
theorem prod_ofFn_g2Pos (c : Fin 6 → K) :
    (List.ofFn fun i => X (g2Pos i) (c i)).prod = g2N (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, g2N,
    mul_assoc]
  rfl

omit [CharP K 2] in
theorem g2N_mem_posUnipotent (A B C D E F : K) : g2N A B C D E F ∈ posUnipotent .G2 K := by
  have h := (positive_root_product_injectivity .G2 K g2Pos g2Pos_injective g2Pos_pos).1
    ![A, B, C, D, E, F]
  rwa [prod_ofFn_g2Pos] at h

omit [CharP K 2] in
theorem g2N_injective {A B C D E F A' B' C' D' E' F' : K}
    (h : g2N A B C D E F = g2N A' B' C' D' E' F') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' ∧ E = E' ∧ F = F' := by
  have hinj := (positive_root_product_injectivity .G2 K g2Pos g2Pos_injective g2Pos_pos).2
  have h' := @hinj ![A, B, C, D, E, F] ![A', B', C', D', E', F'] (by
    simp only [prod_ofFn_g2Pos]
    exact h)
  exact ⟨congrFun h' 0, congrFun h' 1, congrFun h' 2, congrFun h' 3, congrFun h' 4,
    congrFun h' 5⟩

omit [CharP K 2] in
theorem exists_g2N_of_mem_posUnipotent {g : ModGL .G2 K} (hg : g ∈ posUnipotent .G2 K) :
    ∃ A B C D E F : K, g2N A B C D E F = g := by
  obtain ⟨c, -, hc⟩ := ((positive_root_collection .G2 K).2 g2Pos g2Pos_injective range_g2Pos).2.2
    hg
  exact ⟨c 0, c 1, c 2, c 3, c 4, c 5, by rw [← prod_ofFn_g2Pos]; exact hc⟩

@[expose] def g2ia : Fin Tag.G2.rank := ⟨0, by decide⟩

@[expose] def g2ir : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem eq_one_of_mul_self_eq_one_two {ε : K} (hε : ε * ε = 1) : ε = 1 := by
  have h : (ε - 1) ^ 2 = 0 := by linear_combination hε + (1 - ε) * two_eq_zero_K (K := K)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

theorem weylElt_conj (i : Fin Tag.G2.rank) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (x : K) : weylElt .G2 K i 1 * X α x * (weylElt .G2 K i 1)⁻¹ = X (reflect .G2 i α) x := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hα
  rw [h, eq_one_of_mul_self_eq_one_two hε, one_mul]

theorem reflect_a_r : reflect .G2 g2ia g2r = g2u := List.ofFn_injective (by decide +kernel)
theorem reflect_a_u : reflect .G2 g2ia g2u = g2r := List.ofFn_injective (by decide +kernel)
theorem reflect_a_v : reflect .G2 g2ia g2v = g2v := List.ofFn_injective (by decide +kernel)
theorem reflect_a_b : reflect .G2 g2ia g2b = g2c := List.ofFn_injective (by decide +kernel)
theorem reflect_a_c : reflect .G2 g2ia g2c = g2b := List.ofFn_injective (by decide +kernel)
theorem reflect_r_a : reflect .G2 g2ir g2a = g2b := List.ofFn_injective (by decide +kernel)
theorem reflect_r_b : reflect .G2 g2ir g2b = g2a := List.ofFn_injective (by decide +kernel)
theorem reflect_r_u : reflect .G2 g2ir g2u = g2v := List.ofFn_injective (by decide +kernel)
theorem reflect_r_v : reflect .G2 g2ir g2v = g2u := List.ofFn_injective (by decide +kernel)
theorem reflect_r_c : reflect .G2 g2ir g2c = g2c := List.ofFn_injective (by decide +kernel)
theorem reflect_r_r : reflect .G2 g2ir g2r = g2nr := List.ofFn_injective (by decide +kernel)

omit [CharP K 2] in
theorem torus_a_c (t : Kˣ) (x : K) :
    torusElt .G2 K g2ia t * X g2c x * (torusElt .G2 K g2ia t)⁻¹ = X g2c (t * x) := by
  rw [root_torus_conjugation g2ia isRoot_g2c t x]
  have h : ∑ j, Tag.G2.cartan g2ia j * g2c j = 1 := by decide
  rw [h, zpow_one]

omit [CharP K 2] in
theorem torus_r_v (t : Kˣ) (x : K) :
    torusElt .G2 K g2ir t * X g2v x * (torusElt .G2 K g2ir t)⁻¹ = X g2v (t * x) := by
  rw [root_torus_conjugation g2ir isRoot_g2v t x]
  have h : ∑ j, Tag.G2.cartan g2ir j * g2v j = 1 := by decide
  rw [h, zpow_one]

theorem commute_a_nr (x y : K) : Commute (X g2a x) (X g2nr y) := by
  have hr : ((7, 8, 12, []) : PairRow) ∈ pairTable .G2 := by decide +kernel
  refine commute_pinnedX_of_two_eq_zero two_eq_zero_K hr rfl
    (simple .G2 g2ir * simple .G2 g2ia * simple .G2 g2ir * simple .G2 g2ia * simple .G2 g2ir)
    ?_ ?_ x y <;>
  · simp only [mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem conj_nr_v (y x : K) :
    X g2nr y * X g2v x * X g2nr y = X g2v x * (X g2a (x * y ^ 2) * X g2c (x ^ 2 * y)) := by
  have h := mul_eq_of_commutatorElement_eq (comm_v_nr x y) (pinnedX_mul_self _ _)
  rw [h, mul_assoc _ (X g2nr y), pinnedX_mul_self, mul_one]

end Roots

end CFSG.ComponentClassification.UnbalancedCatalog
