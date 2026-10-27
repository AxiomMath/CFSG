module

public import Certificates.Data.Kernel.Co2Smith.RefineA
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Fi22Snd.Colour
import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.KC.Co2SmithR

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.KC.Fi22Snd (foldN_add packSum_get unpack12_get row_mask imgOK_facts imgMaskK_testBit
  row_d_lt row_lt decodeRow_eq spread_eq hcK_eq hcol_lt idxK_le)

private theorem cgA_eq (C v : Nat) : cgA C v = C / 2 ^ (32 * v) % 2 ^ 32 :=
  CFSG.KS.Raw.Orb.fld_eq C (32 * v) 32

private theorem cgA_packed {n : Nat} {f : Nat → Nat} (hf : ∀ v < n, f v < 2 ^ 32) (u : Nat) :
    cgA (∑ v ∈ Finset.range n, f v * 2 ^ (32 * v)) u = if u < n then f u else 0 := by
  rw [cgA_eq]
  exact packSum_get n hf u

private theorem initA_eq (n : Nat) (Ts pre : List Nat) :
    initA n Ts pre = ∑ v ∈ Finset.range n, initValA Ts pre v * 2 ^ (32 * v) := by
  have h := foldN_add (f := fun v a => Nat.add a (Nat.shiftLeft (initValA Ts pre v)
    (Nat.mul (nat_lit 32) v))) (g := fun v => initValA Ts pre v * 2 ^ (32 * v)) (fun v a => by
      change a + initValA Ts pre v <<< (32 * v) = _
      rw [Nat.shiftLeft_eq]) n 0
  rw [Nat.zero_add] at h
  exact h

private theorem stepA_eq (n : Nat) (S : Nat → Nat) (Ts : List Nat) (C : Nat) :
    stepA n S Ts C = ∑ v ∈ Finset.range n, newColA Ts C (accA n S C) v * 2 ^ (32 * v) := by
  unfold stepA
  rw [CFSG.KC.Pack.strictN_eq]
  have h := foldN_add (f := fun v a => Nat.add a (Nat.shiftLeft (newColA Ts C (accA n S C) v)
    (Nat.mul (nat_lit 32) v))) (g := fun v => newColA Ts C (accA n S C) v * 2 ^ (32 * v))
    (fun v a => by
      change a + newColA Ts C (accA n S C) v <<< (32 * v) = _
      rw [Nat.shiftLeft_eq]) n 0
  rw [Nat.zero_add] at h
  exact h

private theorem accA_eq (n : Nat) (S : Nat → Nat) (C : Nat) :
    accA n S C = ∑ w ∈ Finset.range n, hcK (cgA C w) * S w := by
  have h := foldN_add (f := fun w a => Nat.add a (Nat.mul (hcK (cgA C w)) (S w)))
    (g := fun w => hcK (cgA C w) * S w) (fun _ _ => rfl) n 0
  rw [Nat.zero_add] at h
  exact h

private theorem fixA_lt (v : Nat) : ∀ Ts : List Nat, fixA Ts v < 2 ^ Ts.length
  | [] => Nat.one_pos
  | T :: Ts => by
    have ih := fixA_lt v Ts
    have h2 : nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v, nat_lit 1, nat_lit 0) ≤ 1 := by
      cases Nat.beq (pg 12 4095 T v) v <;> decide
    change nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v, nat_lit 1, nat_lit 0) +
      2 * fixA Ts v < 2 ^ (Ts.length + 1)
    rw [Nat.pow_succ]
    omega

private theorem beq_congr {a b c e : Nat} (h : a = b ↔ c = e) : Nat.beq a b = Nat.beq c e := by
  cases h1 : Nat.beq a b <;> cases h2 : Nat.beq c e
  · rfl
  · exact absurd (h.2 (Nat.eq_of_beq_eq_true h2)) (Nat.ne_of_beq_eq_false h1)
  · exact absurd (h.1 (Nat.eq_of_beq_eq_true h1)) (Nat.ne_of_beq_eq_false h2)
  · rfl

private theorem fixA_congr {v w : Nat} : ∀ Ts : List Nat,
    (∀ T ∈ Ts, (pg 12 4095 T v = v ↔ pg 12 4095 T w = w)) → fixA Ts v = fixA Ts w
  | [], _ => rfl
  | T :: Ts, h => by
    have ih := fixA_congr Ts fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    have hb := beq_congr (h T List.mem_cons_self)
    change nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T v) v, nat_lit 1, nat_lit 0) +
      2 * fixA Ts v = nIf(Nat.beq (pg (nat_lit 12) (nat_lit 4095) T w) w, nat_lit 1, nat_lit 0) +
      2 * fixA Ts w
    rw [ih, hb]

private theorem idxK_of_not_mem {v : Nat} : ∀ pre : List Nat, v ∉ pre → idxK pre v = 0
  | [], _ => rfl
  | a :: l, h => by
    have hav : a ≠ v := fun e => h (e ▸ List.mem_cons_self)
    have ih := idxK_of_not_mem l fun hl => h (List.mem_cons_of_mem _ hl)
    have h1 : Nat.beq a v = false := Bool.eq_false_iff.2 fun e => hav (Nat.eq_of_beq_eq_true e)
    change Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
      (Nat.add (idxK l v) (nat_lit 1)) (nat_lit 0) (Nat.beq (idxK l v) (nat_lit 0))) (nat_lit 1)
      (Nat.beq a v) = 0
    rw [h1, ih]
    rfl

private theorem initValA_lt {Ts pre : List Nat} (hsmall : 2 ^ Ts.length * (pre.length + 1) ≤ 2 ^ 31)
    (v : Nat) : initValA Ts pre v < 2 ^ 32 := by
  have h1 := fixA_lt v Ts
  have h2 : 2 ^ Ts.length * (idxK pre v + 1) ≤ 2 ^ Ts.length * (pre.length + 1) :=
    Nat.mul_le_mul_left _ (by have := idxK_le pre v; omega)
  rw [Nat.mul_succ] at h2
  change 2 ^ Ts.length * idxK pre v + fixA Ts v < 2 ^ 32
  omega

private theorem newColA_lt (Ts : List Nat) (C A v : Nat) : newColA Ts C A v < 2 ^ 32 :=
  lt_trans (Nat.mod_lt _ (by decide)) (by decide)

private theorem newColA_eq (Ts : List Nat) (C A v : Nat) :
    newColA Ts C A v = (List.foldl (fun a T => (a * 1000003 +
      cgA C (pg 12 4095 T v) % 2147483629) % 2147483629) (cgA C v % 2147483629) Ts * 1000003 +
        A / 2 ^ (128 + 48 * v) % 2 ^ 48) % 2147483629 := by
  have h : Nat.land (Nat.shiftRight A (128 + 48 * v)) 281474976710655 =
      A / 2 ^ (128 + 48 * v) % 2 ^ 48 := CFSG.KS.Raw.Orb.fld_eq A (128 + 48 * v) 48
  unfold newColA
  rw [← h]
  rfl

private theorem foldl_congr {f g : Nat → Nat → Nat} : ∀ (l : List Nat) (a : Nat),
    (∀ T ∈ l, ∀ a, f a T = g a T) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | T :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h T List.mem_cons_self a]
    exact foldl_congr l _ fun T' hT' => h T' (List.mem_cons_of_mem _ hT')

private theorem newColA_congr {Ts : List Nat} {C A v w : Nat} (hc : cgA C v = cgA C w)
    (hT : ∀ T ∈ Ts, cgA C (pg 12 4095 T v) = cgA C (pg 12 4095 T w))
    (hA : A / 2 ^ (128 + 48 * v) % 2 ^ 48 = A / 2 ^ (128 + 48 * w) % 2 ^ 48) :
    newColA Ts C A v = newColA Ts C A w := by
  have hf : List.foldl (fun a T => (a * 1000003 + cgA C (pg 12 4095 T v) % 2147483629) %
      2147483629) (cgA C w % 2147483629) Ts = List.foldl (fun a T => (a * 1000003 +
      cgA C (pg 12 4095 T w) % 2147483629) % 2147483629) (cgA C w % 2147483629) Ts :=
    foldl_congr Ts _ fun T hT' a => by rw [hT T hT']
  rw [newColA_eq, newColA_eq, hc, hA, hf]

private def nsA (n d : Nat) (R h : Nat → Nat) (p : Nat) : Nat :=
  ∑ w ∈ Finset.range n, if p ∈ decodeRow d (R w) then h w else 0

private theorem nsA_le (n d : Nat) (R h : Nat → Nat) {b : Nat} (hb : ∀ w, h w ≤ b) (p : Nat) :
    nsA n d R h p ≤ n * b := by
  unfold nsA
  calc _ ≤ ∑ _w ∈ Finset.range n, b := Finset.sum_le_sum fun w _ => by
          split_ifs
          · exact hb w
          · exact Nat.zero_le _
    _ = n * b := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

section Acc

variable {n d : Nat} {R M S : Nat → Nat}

private theorem accA_split (hrow : ∀ x < n, rowOK n d R M S x = true) (C : Nat) :
    accA n S C = (∑ w ∈ Finset.range n, hcK (cgA C w) * (w + 1)) +
      2 ^ 128 * ∑ p ∈ Finset.range n, nsA n d R (fun w => hcK (cgA C w)) p * 2 ^ (48 * p) := by
  have e1 : ∀ w ∈ Finset.range n, hcK (cgA C w) * S w = hcK (cgA C w) * (w + 1) +
      ∑ p ∈ Finset.range n,
        (if p ∈ decodeRow d (R w) then hcK (cgA C w) else 0) * 2 ^ (128 + 48 * p) := by
    intro w hw
    rw [spread_eq (hrow w (Finset.mem_range.1 hw)), Nat.mul_add, Finset.mul_sum]
    refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun p _ => ?_)
    split_ifs <;> simp
  rw [accA_eq, Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_comm, Finset.mul_sum]
  refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun p _ => ?_)
  rw [← Finset.sum_mul, pow_add]
  unfold nsA
  ring

private theorem accA_field (hn : n < 4096) (hrow : ∀ x < n, rowOK n d R M S x = true) (C : Nat)
    {v : Nat} (hv : v < n) :
    accA n S C / 2 ^ (128 + 48 * v) % 2 ^ 48 = nsA n d R (fun w => hcK (cgA C w)) v := by
  have hh : ∀ w, hcK (cgA C w) ≤ 2 ^ 31 := fun w => by
    rw [hcK_eq]
    exact (lt_trans (hcol_lt _) (by norm_num)).le
  have hF : ∀ p < n, nsA n d R (fun w => hcK (cgA C w)) p < 2 ^ 48 := fun p _ => by
    have := nsA_le n d R (fun w => hcK (cgA C w)) hh p
    omega
  have hL : ∑ w ∈ Finset.range n, hcK (cgA C w) * (w + 1) < 2 ^ 128 := by
    calc _ ≤ ∑ _w ∈ Finset.range n, 2 ^ 31 * 4096 := Finset.sum_le_sum fun w hw =>
            Nat.mul_le_mul (hh w) (by have := Finset.mem_range.1 hw; omega)
      _ = n * (2 ^ 31 * 4096) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ < 2 ^ 128 := by omega
  rw [accA_split hrow C, pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hL, Nat.zero_add,
    packSum_get n hF v, if_pos hv]

end Acc

private theorem gen_aut {n d ng : Nat} {R M S G : Nat → Nat}
    (hrow : ∀ x < n, rowOK n d R M S x = true)
    (himg : ∀ j < ng, ∀ x < n, imgOK n d (G j) R M x = true)
    (hperm : ∀ j < ng, CFSG.KC.Misc.ArrEnum.permB n 12 (G j) = true) (j : Fin ng) (w v : Fin n) :
    ((permOfArr n (unpack n 12 (G j.val)) v : Fin n) : ℕ) ∈
        decodeRow d (R (permOfArr n (unpack n 12 (G j.val)) w)) ↔
      (v : ℕ) ∈ decodeRow d (R w) := by
  have hg : ∀ x : Fin n, ((permOfArr n (unpack n 12 (G j.val)) x : Fin n) : ℕ) =
      pg (nat_lit 12) (nat_lit 4095) (G j.val) x := fun x => by
    have hr := (rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack (hperm j.val j.2))).1 x
    rw [← hr, unpack12_get x.2]
  have hinj : ∀ a < n, ∀ b < n, pg (nat_lit 12) (nat_lit 4095) (G j.val) a =
      pg (nat_lit 12) (nat_lit 4095) (G j.val) b → a = b := by
    intro a ha b hb e
    have e' : permOfArr n (unpack n 12 (G j.val)) ⟨a, ha⟩ =
        permOfArr n (unpack n 12 (G j.val)) ⟨b, hb⟩ := Fin.ext (by rw [hg, hg]; exact e)
    exact congrArg Fin.val ((permOfArr n (unpack n 12 (G j.val))).injective e')
  have hrw := hrow w w.2
  obtain ⟨hy, hmask⟩ := imgOK_facts (himg j.val j.2 w w.2)
  have h1 := row_mask (hrow _ hy) (pg (nat_lit 12) (nat_lit 4095) (G j.val) v)
  rw [← hmask, imgMaskK_testBit (row_d_lt hrw)] at h1
  rw [hg w, hg v, ← (decide_eq_decide.1 h1), decodeRow_eq, List.mem_map]
  simp only [List.mem_range]
  constructor
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, hinj _ (row_lt hrw hi) _ v.2 e⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨i, hi, by rw [e]⟩

theorem colourA_inv {n d ng k : Nat} {R M S G : Nat → Nat} {Ts pre : List Nat}
    (hn : n < 4096) (hd : 0 < d) (hrow : ∀ x < n, rowOK n d R M S x = true)
    (himg : ∀ j < ng, ∀ x < n, imgOK n d (G j) R M x = true)
    (hperm : ∀ j < ng, CFSG.KC.Misc.ArrEnum.permB n 12 (G j) = true)
    (hTs : ∀ T ∈ Ts, ∀ y < n, pg 12 4095 T y < n)
    (hsmall : 2 ^ Ts.length * (pre.length + 1) ≤ 2 ^ 31) {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ Subgroup.closure (Set.range fun j : Fin ng => permOfArr n (unpack n 12 (G j.val))))
    (harc : ∀ T ∈ Ts, ∀ y z : Fin n, (z : ℕ) = pg 12 4095 T y →
      ((σ z : Fin n) : ℕ) = pg 12 4095 T (σ y))
    (hpre : ∀ v : Fin n, (v : ℕ) ∈ pre → σ v = v) :
    ∀ v : Fin n, cgA (colourA n S Ts pre k) (σ v) = cgA (colourA n S Ts pre k) v := by
  have _ := hd
  let H : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {τ | ∀ w v : Fin n,
        ((τ v : Fin n) : ℕ) ∈ decodeRow d (R (τ w)) ↔ (v : ℕ) ∈ decodeRow d (R w)}
      mul_mem' := fun {a b} ha hb w v => by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
        exact (ha (b w) (b v)).trans (hb w v)
      one_mem' := fun _ _ => Iff.rfl
      inv_mem' := fun {a} ha w v => by
        have := ha (a⁻¹ w) (a⁻¹ v)
        have e : ∀ x, a (a⁻¹ x) = x := fun x => Equiv.apply_symm_apply a x
        rw [e, e] at this
        exact this.symm }
  have hσH : σ ∈ H := (Subgroup.closure_le H).2 (by
    rintro _ ⟨j, rfl⟩
    exact gen_aut hrow himg hperm j) hσ
  have hAut : ∀ w v : Fin n,
      ((σ v : Fin n) : ℕ) ∈ decodeRow d (R (σ w)) ↔ (v : ℕ) ∈ decodeRow d (R w) := hσH
  have hfix : ∀ v : Fin n, ∀ T ∈ Ts,
      (pg 12 4095 T (σ v) = σ v ↔ pg 12 4095 T v = v) := by
    intro v T hT
    have hz := harc T hT v ⟨pg 12 4095 T v, hTs T hT v v.2⟩ rfl
    constructor
    · intro e
      have e' : σ ⟨pg 12 4095 T v, hTs T hT v v.2⟩ = σ v := Fin.ext (hz.trans e)
      exact congrArg Fin.val (σ.injective e')
    · intro e
      have e' : (⟨pg 12 4095 T v, hTs T hT v v.2⟩ : Fin n) = v := Fin.ext e
      rw [← hz, e']
  have hidx : ∀ v : Fin n, idxK pre (σ v) = idxK pre v := by
    intro v
    by_cases hv : (v : ℕ) ∈ pre
    · rw [hpre v hv]
    · have hv' : ((σ v : Fin n) : ℕ) ∉ pre := fun h => hv (by
        have e := hpre (σ v) h
        rw [σ.injective e] at h
        exact h)
      rw [idxK_of_not_mem pre hv, idxK_of_not_mem pre hv']
  induction k with
  | zero =>
    intro v
    change cgA (initA n Ts pre) (σ v) = cgA (initA n Ts pre) v
    rw [initA_eq, cgA_packed (fun v _ => initValA_lt hsmall v),
      cgA_packed (fun v _ => initValA_lt hsmall v), if_pos (σ v).2, if_pos v.2]
    change 2 ^ Ts.length * idxK pre (σ v) + fixA Ts (σ v) =
      2 ^ Ts.length * idxK pre v + fixA Ts v
    rw [hidx v, fixA_congr Ts (hfix v)]
  | succ k ih =>
    intro v
    have e1 : colourA n S Ts pre (k + 1) = stepA n S Ts (colourA n S Ts pre k) := by
      change strictN (colourA n S Ts pre k) (fun C => stepA n S Ts C) = _
      rw [CFSG.KC.Pack.strictN_eq]
    rw [e1]
    generalize colourA n S Ts pre k = C at ih ⊢
    rw [stepA_eq, cgA_packed (f := newColA Ts C (accA n S C)) (fun v _ => newColA_lt _ _ _ v),
      cgA_packed (f := newColA Ts C (accA n S C)) (fun v _ => newColA_lt _ _ _ v),
      if_pos (σ v).2, if_pos v.2]
    refine newColA_congr (ih v) (fun T hT => ?_) ?_
    · have hz := harc T hT v ⟨pg 12 4095 T v, hTs T hT v v.2⟩ rfl
      rw [← hz]
      exact ih _
    · rw [accA_field hn hrow C (σ v).2, accA_field hn hrow C v.2]
      unfold nsA
      rw [Finset.sum_range, Finset.sum_range]
      refine (Fintype.sum_equiv σ _ _ fun w => ?_).symm
      simp only [hAut w v, ih w]

end CFSG.KC.Co2SmithR

end
