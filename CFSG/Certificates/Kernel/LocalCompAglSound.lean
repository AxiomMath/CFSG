module

public import Certificates.Data.Kernel.WeylE8.Agl
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS

@[expose] def encT (τ : Equiv.Perm (Fin 8)) : ℕ :=
  (τ 0 : ℕ) + 8 * τ 1 + 64 * τ 2 + 512 * τ 4

def Reach (s f : Equiv.Perm (Fin 8)) (t : ℕ) : Prop :=
  ∃ τ ∈ Subgroup.closure ({s, f} : Set (Equiv.Perm (Fin 8))), encT τ = t

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem pg3 (t j : ℕ) : pg 3 7 t j = t / 2 ^ (3 * j) % 8 := by
  change (t >>> (3 * j)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pg_tuple {a b d e : ℕ} (ha : a < 8) (hb : b < 8) (hd : d < 8) (he : e < 8) :
    pg 3 7 (a + 8 * b + 64 * d + 512 * e) 0 = a ∧ pg 3 7 (a + 8 * b + 64 * d + 512 * e) 1 = b ∧
      pg 3 7 (a + 8 * b + 64 * d + 512 * e) 2 = d ∧ pg 3 7 (a + 8 * b + 64 * d + 512 * e) 3 = e := by
  simp only [pg3, Nat.reduceMul, Nat.reducePow]
  omega

theorem bitK_eq (S t : ℕ) : bitK S t = S.testBit t := by
  change ((S >>> t) &&& 1 == 1) = _
  rw [Nat.testBit, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (S >>> t) with h | h <;> simp [h]

theorem actT_encT {s : Equiv.Perm (Fin 8)} {G : ℕ} (hG : ∀ i : Fin 8, pg 3 7 G i = s i)
    (τ : Equiv.Perm (Fin 8)) : actT G (encT τ) = encT (s * τ) := by
  obtain ⟨h0, h1, h2, h3⟩ := pg_tuple (τ 0).2 (τ 1).2 (τ 2).2 (τ 4).2
  change pg 3 7 G (pg 3 7 (encT τ) 0) + ((pg 3 7 G (pg 3 7 (encT τ) 1) <<< 3) +
    ((pg 3 7 G (pg 3 7 (encT τ) 2) <<< 6) + (pg 3 7 G (pg 3 7 (encT τ) 3) <<< 9))) = _
  simp only [encT] at h0 h1 h2 h3 ⊢
  rw [h0, h1, h2, h3, hG, hG, hG, hG]
  simp only [Nat.shiftLeft_eq, Equiv.Perm.mul_apply]
  omega

theorem foldN_inv {P : ℕ → Prop} {f : ℕ → ℕ → ℕ} (hf : ∀ i s, P s → P (f i s)) {n s : ℕ}
    (hs : P s) : P (foldN n f s) := by
  have blk : ∀ b len s, P s → P (foldBlk b f len s) := by
    intro b len
    induction len with
    | zero => exact fun s hs => hs
    | succ l ih =>
      intro s hs
      change P (strictN (f (Nat.add b l) s) (foldBlk b f l))
      rw [strictN_eq']
      exact ih _ (hf _ _ hs)
  change P (Nat.rec (motive := fun _ => ℕ → ℕ) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
      (Nat.shiftRight n (nat_lit 6))
      (foldBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f (Nat.land n (nat_lit 63)) s))
  generalize Nat.shiftRight n (nat_lit 6) = q
  have hs' := blk (Nat.shiftLeft q (nat_lit 6)) (Nat.land n (nat_lit 63)) s hs
  generalize foldBlk (Nat.shiftLeft q (nat_lit 6)) f (Nat.land n (nat_lit 63)) s = s' at hs'
  induction q generalizing s' with
  | zero => exact hs'
  | succ h ih =>
    change P (strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s') _)
    rw [strictN_eq']
    exact ih _ (blk _ _ _ hs')

def Inv (s f : Equiv.Perm (Fin 8)) (S : ℕ) : Prop := ∀ t, S.testBit t = true → Reach s f t

theorem inv_or {s f : Equiv.Perm (Fin 8)} {S x y : ℕ} (hS : Inv s f S) (hx : Reach s f x)
    (hy : Reach s f y) : Inv s f (Nat.lor S (Nat.lor (Nat.shiftLeft 1 x) (Nat.shiftLeft 1 y))) := by
  intro t ht
  change (S ||| ((1 <<< x) ||| (1 <<< y))).testBit t = true at ht
  simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at ht
  rcases ht with ht | rfl | rfl
  · exact hS t ht
  · exact hx
  · exact hy

theorem stepT_inv {s f : Equiv.Perm (Fin 8)} {G H : ℕ} (hG : ∀ i : Fin 8, pg 3 7 G i = s i)
    (hH : ∀ i : Fin 8, pg 3 7 H i = f i) {S : ℕ} (hS : Inv s f S) : Inv s f (stepT G H S) := by
  refine foldN_inv (P := Inv s f) (fun t acc hacc => ?_) hS
  cases hb : bitK S t
  · exact hacc
  · rw [bitK_eq] at hb
    obtain ⟨τ, hτ, rfl⟩ := hS t hb
    refine inv_or hacc ⟨s * τ, ?_, (actT_encT hG τ).symm⟩ ⟨f * τ, ?_, (actT_encT hH τ).symm⟩
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) hτ
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hτ

theorem iterT_inv {s f : Equiv.Perm (Fin 8)} {G H : ℕ} (hG : ∀ i : Fin 8, pg 3 7 G i = s i)
    (hH : ∀ i : Fin 8, pg 3 7 H i = f i) (k : ℕ) {S : ℕ} (hS : Inv s f S) :
    Inv s f (iterT G H k S) := by
  induction k generalizing S with
  | zero => exact hS
  | succ k ih =>
    change Inv s f (strictN (stepT G H S) (iterT G H k))
    rw [strictN_eq']
    exact ih (stepT_inv hG hH hS)

theorem affK_tuple {a b d e : ℕ} (ha : a < 8) (hb : b < 8) (hd : d < 8) (he : e < 8)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (hea : e ≠ a) (heb : e ≠ b) (hed : e ≠ d)
    (hx : e ≠ a ^^^ (b ^^^ d)) : affK (a + 8 * b + 64 * d + 512 * e) = true := by
  obtain ⟨h0, h1, h2, h3⟩ := pg_tuple ha hb hd he
  unfold affK
  rw [h0, h1, h2, h3]
  simp only [strictB_eq']
  have q : ∀ {x y : ℕ}, x ≠ y → Nat.beq x y = false := fun h =>
    Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
  change Bool.rec _ _ (Nat.beq a b) = true
  rw [q hab, q had, q hbd, q hea, q heb, q hed]
  change Bool.rec _ _ (Nat.beq e (a ^^^ (b ^^^ d))) = true
  rw [q hx]

theorem agl_sound {s f : Equiv.Perm (Fin 8)} {G H : ℕ} (hG : ∀ i : Fin 8, pg 3 7 G i = s i)
    (hH : ∀ i : Fin 8, pg 3 7 H i = f i) (h : aglK G H = true) {a b d e : Fin 8} (hab : a ≠ b)
    (had : a ≠ d) (hbd : b ≠ d) (hea : e ≠ a) (heb : e ≠ b) (hed : e ≠ d)
    (hx : (e : ℕ) ≠ a ^^^ (b ^^^ d)) :
    ∃ τ ∈ Subgroup.closure ({s, f} : Set (Equiv.Perm (Fin 8))),
      τ 0 = a ∧ τ 1 = b ∧ τ 2 = d ∧ τ 4 = e := by
  have h0 : ∀ n, Reach s f n → Inv s f (Nat.shiftLeft 1 n) := by
    intro n hn t ht
    change (1 <<< n).testBit t = true at ht
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at ht
    subst ht
    exact hn
  have hI := iterT_inv hG hH 32 (h0 2184 ⟨1, Subgroup.one_mem _, rfl⟩)
  unfold aglK at h
  rw [strictB_eq'] at h
  have := a.2
  have := b.2
  have := d.2
  have := e.2
  have ht : (a : ℕ) + 8 * b + 64 * d + 512 * e < 4096 := by omega
  have hc := allN_spec (n := 4096) h (a + 8 * b + 64 * d + 512 * e) ht
  have v : ∀ {x y : Fin 8}, x ≠ y → (x : ℕ) ≠ y := fun h e => h (Fin.ext e)
  rw [affK_tuple a.2 b.2 d.2 e.2 (v hab) (v had) (v hbd) (v hea) (v heb) (v hed) hx] at hc
  change bitK _ _ = true at hc
  rw [bitK_eq] at hc
  obtain ⟨τ, hτ, hτe⟩ := hI _ hc
  refine ⟨τ, hτ, ?_⟩
  simp only [encT] at hτe
  have := (τ 0).2
  have := (τ 1).2
  have := (τ 2).2
  have := (τ 4).2
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega

end CFSG.KLC.E8

end
