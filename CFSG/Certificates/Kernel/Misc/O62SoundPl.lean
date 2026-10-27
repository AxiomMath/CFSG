module

public import CFSG.Certificates.Kernel.Misc.O62SoundBits

public section

namespace CFSG.KC.Misc.O62

open CFSG.KC.Ord CFSG.KC.Misc
open CFSG.KC.LQT.P (letB impB allN anyN allL anyL)
open CFSG.LargeExtraspecial.O62

theorem plCnt_lt (p : ℕ) : plCnt p < 256 := Nat.and_lt_two_pow (n := 8) _ (by norm_num)

theorem plCnt_eq (p : ℕ) : plCnt p = p % 256 := by
  show p &&& (255 : ℕ) = p % 256
  rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

theorem plLane_eq (p i : ℕ) : plLane p i = ((p >>> 8) / 2 ^ (37 * i)) % 2 ^ 37 := by
  show (p >>> (8 + 37 * i)) &&& (137438953471 : ℕ) = _
  rw [show (137438953471 : ℕ) = 2 ^ 37 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow]

theorem plLane_lt (p i : ℕ) : plLane p i < 2 ^ 37 := by
  rw [plLane_eq]; exact Nat.mod_lt _ (by positivity)

theorem plPush_eq (p x : ℕ) :
    plPush p x = (((p >>> 8) <<< 37 ||| x) <<< 8) + (plCnt p + 1) := by
  unfold plPush
  rw [letN_eq]
  rfl

theorem plPush_shr8 {p x : ℕ} (hc : plCnt p < 255) :
    plPush p x >>> 8 = (p >>> 8) <<< 37 ||| x := by
  rw [plPush_eq, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem plCnt_push {p x : ℕ} (hc : plCnt p < 255) : plCnt (plPush p x) = plCnt p + 1 := by
  rw [plCnt_eq, plPush_eq, Nat.shiftLeft_eq]
  rw [plCnt_eq] at hc ⊢
  omega

theorem plLane_push_zero {p x : ℕ} (hc : plCnt p < 255) (hx : x < 2 ^ 37) :
    plLane (plPush p x) 0 = x := by
  rw [plLane_eq, plPush_shr8 hc, Nat.mul_zero, Nat.pow_zero, Nat.div_one,
    ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

theorem plLane_push_succ {p x : ℕ} (hc : plCnt p < 255) (hx : x < 2 ^ 37) (i : ℕ) :
    plLane (plPush p x) (i + 1) = plLane p i := by
  have h37 : ((p >>> 8) * 2 ^ 37 + x) / 2 ^ 37 = p >>> 8 := by omega
  rw [plLane_eq, plLane_eq, plPush_shr8 hc, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq,
    show 37 * (i + 1) = 37 + 37 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul, h37]

@[expose] noncomputable def plLanes (p : ℕ) : List ℕ := (List.range (plCnt p)).map (plLane p)

theorem length_plLanes (p : ℕ) : (plLanes p).length = plCnt p := by simp [plLanes]

theorem mem_plLanes {p ℓ : ℕ} : ℓ ∈ plLanes p ↔ ∃ i < plCnt p, plLane p i = ℓ := by
  simp [plLanes]

theorem lane_mem {p i : ℕ} (hi : i < plCnt p) : plLane p i ∈ plLanes p :=
  mem_plLanes.2 ⟨i, hi, rfl⟩

theorem plLanes_zero : plLanes 0 = [] := by
  have : plCnt 0 = 0 := by rw [plCnt_eq]
  simp [plLanes, this]

theorem plLanes_push {p x : ℕ} (hc : plCnt p < 255) (hx : x < 2 ^ 37) :
    plLanes (plPush p x) = x :: plLanes p := by
  unfold plLanes
  rw [plCnt_push hc, List.range_succ_eq_map, List.map_cons, List.map_map, plLane_push_zero hc hx]
  congr 1
  apply List.map_congr_left
  intro i _
  exact plLane_push_succ hc hx i

@[expose] noncomputable def plOfAux (l : List ℕ) (acc : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc) (fun x _ ih acc => ih (plPush acc x)) l acc

theorem plOf_eq (l : List ℕ) : plOf l = plOfAux l 0 := rfl

theorem plOfAux_cons (x : ℕ) (t : List ℕ) (acc : ℕ) :
    plOfAux (x :: t) acc = plOfAux t (plPush acc x) := rfl

theorem plLanes_plOfAux (l : List ℕ) : ∀ (acc : ℕ), plCnt acc + l.length < 256 →
    (∀ x ∈ l, x < 2 ^ 37) → plLanes (plOfAux l acc) = l.reverse ++ plLanes acc := by
  induction l with
  | nil => intro acc _ _; rfl
  | cons x t ih =>
    intro acc hlen hx
    have hc : plCnt acc < 255 := by simp at hlen; omega
    have hx0 : x < 2 ^ 37 := hx x (List.mem_cons_self ..)
    rw [plOfAux_cons, ih (plPush acc x) (by rw [plCnt_push hc]; simp at hlen ⊢; omega)
      (fun y hy => hx y (List.mem_cons_of_mem _ hy)), plLanes_push hc hx0]
    simp

@[expose] noncomputable def pushAll (S : ℕ) (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) S (fun i acc => plPush acc (g i)) n

theorem plLanes_pushAll (S : ℕ) (g : ℕ → ℕ) (n : ℕ) (hn : plCnt S + n < 256)
    (hg : ∀ i < n, g i < 2 ^ 37) :
    plLanes (pushAll S g n) = ((List.range n).map g).reverse ++ plLanes S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (by omega) (fun i hi => hg i (Nat.lt_succ_of_lt hi))
    have hc : plCnt (pushAll S g n) < 255 := by
      have := congrArg List.length ih'
      rw [length_plLanes] at this
      simp [length_plLanes] at this
      omega
    have e : pushAll S g (n + 1) = plPush (pushAll S g n) (g n) := rfl
    rw [e, plLanes_push hc (hg n (Nat.lt_succ_self n)), ih', List.range_succ, List.map_append]
    simp

@[expose] noncomputable def pushIf (C : ℕ) (P : ℕ → Bool) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun j acc => Bool.rec (motive := fun _ => ℕ) acc (plPush acc (plLane C j)) (P j)) n

theorem plLanes_pushIf (C : ℕ) (P : ℕ → Bool) (n : ℕ) (hn : n ≤ 255) :
    plLanes (pushIf C P n) = (((List.range n).filter P).map (plLane C)).reverse := by
  induction n with
  | zero => exact plLanes_zero
  | succ n ih =>
    have ih' := ih (by omega)
    have e : pushIf C P (n + 1) = Bool.rec (motive := fun _ => ℕ) (pushIf C P n)
        (plPush (pushIf C P n) (plLane C n)) (P n) := rfl
    rw [e, List.range_succ, List.filter_append]
    cases hP : P n
    · simp [hP, ih']
    · have hc : plCnt (pushIf C P n) < 255 := by
        have := congrArg List.length ih'
        rw [length_plLanes] at this
        simp only [List.length_reverse, List.length_map] at this
        have h2 := List.length_filter_le P (List.range n)
        simp at h2
        omega
      rw [plLanes_push hc (plLane_lt C n), ih']
      simp [hP]

theorem plAt_eq (p i : ℕ) : plAt p i = plLane p i &&& (2 ^ 36 - 1) := rfl

theorem plAt_of_lt {p i : ℕ} (h : plLane p i < 2 ^ 36) : plAt p i = plLane p i := by
  rw [plAt_eq, Nat.and_two_pow_sub_one_of_lt_two_pow h]

theorem plPar_eq (p i : ℕ) : plPar p i = plLane p i >>> 36 := rfl

theorem lane_code {c b : ℕ} (hc : c < 2 ^ 36) :
    (c ||| (b <<< 36)) &&& (2 ^ 36 - 1) = c ∧ (c ||| (b <<< 36)) >>> 36 = b := by
  have h : (c ||| (b <<< 36)) = b * 2 ^ 36 + c := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hc, Nat.shiftLeft_eq]
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  constructor <;> omega

theorem plLanes_plOf {l : List ℕ} (hl : l.length < 256) (hx : ∀ x ∈ l, x < 2 ^ 37) :
    plLanes (plOf l) = l.reverse := by
  rw [plOf_eq, plLanes_plOfAux l 0 (by rw [plCnt_eq]; simpa using hl) hx, plLanes_zero]
  simp

theorem plLanes_spanAdd {S x : ℕ} (hS : 2 * plCnt S < 256) :
    plLanes (spanAdd S x) =
      ((List.range (plCnt S)).map (fun i => Code.mul (plAt S i) x)).reverse ++ plLanes S := by
  have e : spanAdd S x = pushAll S (fun i => mulK (plAt S i) x) (plCnt S) := rfl
  rw [e, plLanes_pushAll S _ _ (by omega)
    (fun i _ => lt_trans (by rw [mulK_eq]; exact Code.mul_lt _ _) (by norm_num))]
  simp only [mulK_eq]

theorem plCnt_spanAdd {S x : ℕ} (hS : 2 * plCnt S < 256) : plCnt (spanAdd S x) = 2 * plCnt S := by
  rw [← length_plLanes, plLanes_spanAdd hS]
  simp [length_plLanes]
  omega

theorem mem_plLanes_filterFrom {C i ℓ : ℕ} {f : ℕ → Bool} :
    ℓ ∈ plLanes (plFilterFrom C i f) ↔
      ∃ j < plCnt C, i < j ∧ f (plAt C j) = true ∧ plLane C j = ℓ := by
  have e : plFilterFrom C i f =
      pushIf C (fun j => andB (Nat.blt i j) (letB (plAt C j) f)) (plCnt C) := rfl
  have h255 : plCnt C ≤ 255 := by have := plCnt_lt C; omega
  rw [e, plLanes_pushIf _ _ _ h255]
  simp [andB_eq, letB_eq, and_assoc]

theorem mem_plLanes_filter {C ℓ : ℕ} {f : ℕ → Bool} :
    ℓ ∈ plLanes (plFilter C f) ↔ ∃ j < plCnt C, f (plAt C j) = true ∧ plLane C j = ℓ := by
  have e : plFilter C f = pushIf C (fun j => letB (plAt C j) f) (plCnt C) := rfl
  have h255 : plCnt C ≤ 255 := by have := plCnt_lt C; omega
  rw [e, plLanes_pushIf _ _ _ h255]
  simp [letB_eq, and_assoc]

theorem plMem_iff (p y : ℕ) : plMem p y = true ↔ ∃ i < plCnt p, plAt p i = y := by
  unfold plMem
  rw [letB_eq, anyN_iff]
  simp [beq_eq_decide]

end CFSG.KC.Misc.O62

end
