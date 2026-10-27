module

public import CFSG.Certificates.Kernel.Misc.RuInvPack
import CFSG.Certificates.Kernel.SporSch.LyLoop
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

namespace CFSG.KC.Misc.RuInv.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

@[expose] def hst (h v : Nat) : Nat := (h ^^^ v) * 1099511628211 % 2 ^ 64

@[expose] noncomputable def hrun (x : Nat) (l : List Nat) (h : Nat) : Nat :=
  l.foldl (fun h i => if i < 4060 then hst h (pg 12 (mask 12) x i) else h) h

theorem mask_eq (w : Nat) : mask w = 2 ^ w - 1 := by
  unfold mask
  change 1 <<< w - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem fld_fld (x a b : Nat) (hb : b < 64) :
    fld(fld(x, Nat.mul 768 a, mask 768), Nat.mul 12 b, nat_lit 4095) =
      pg 12 (mask 12) x (64 * a + b) := by
  unfold pg
  rw [mask_eq, mask_eq, show (nat_lit 4095) = 2 ^ 12 - 1 by norm_num]
  change ((x >>> (768 * a)) &&& (2 ^ 768 - 1)) >>> (12 * b) &&& (2 ^ 12 - 1) =
    (x >>> (12 * (64 * a + b))) &&& (2 ^ 12 - 1)
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < 12
  · have h1 : 12 * b + k < 768 := by omega
    simp only [hk, h1, decide_true, Bool.and_true]
    congr 1
    ring
  · simp [hk]

theorem land_mask64 (y : Nat) : Nat.land y (mask 64) = y % 2 ^ 64 := by
  rw [mask_eq]
  change y &&& (2 ^ 64 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod y 64

theorem inner_eq (x q : Nat) : ∀ m ≤ 64, ∀ h,
    Nat.rec (motive := fun _ => Nat → Nat) (fun h => h)
      (fun j ih h => strictN (Nat.add (Nat.mul 64 (Nat.sub 63 q)) (Nat.sub 63 j))
        (fun i => ih (nIf(Nat.blt i 4060,
          Nat.land (Nat.mul (Nat.xor h (fld(fld(x, Nat.mul 768 (Nat.sub 63 q), mask 768),
            Nat.mul 12 (Nat.sub 63 j), nat_lit 4095))) 1099511628211) (mask 64), h))))
      m h = hrun x (List.range' (64 * (63 - q) + 64 - m) m) h := by
  intro m
  induction m with
  | zero => intro _ h; rfl
  | succ m ih =>
    intro hm h
    have e1 : 64 * (63 - q) + 64 - (m + 1) = 64 * (63 - q) + (63 - m) := by omega
    have e2 : 64 * (63 - q) + (63 - m) + 1 = 64 * (63 - q) + 64 - m := by omega
    rw [e1, List.range'_succ, e2]
    change strictN (64 * (63 - q) + (63 - m)) _ = _
    rw [strictN_eq, ih (by omega)]
    unfold hrun
    rw [List.foldl_cons]
    congr 1
    have hf := fld_fld x (63 - q) (63 - m) (by omega)
    change Bool.rec (motive := fun _ => Nat) h
      (Nat.land (Nat.mul (Nat.xor h (fld(fld(x, Nat.mul 768 (63 - q), mask 768),
        Nat.mul 12 (63 - m), nat_lit 4095))) 1099511628211) (mask 64))
      (Nat.blt (64 * (63 - q) + (63 - m)) 4060) = _
    rw [hf]
    by_cases hi : 64 * (63 - q) + (63 - m) < 4060
    · rw [Nat.blt_eq.mpr hi, if_pos hi, land_mask64]
      rfl
    · rw [if_neg hi]
      have : Nat.blt (64 * (63 - q) + (63 - m)) 4060 = false := by
        cases e : Nat.blt (64 * (63 - q) + (63 - m)) 4060
        · rfl
        · exact absurd (Nat.blt_eq.mp e) hi
      rw [this]

theorem range_map_rev (n : Nat) : (List.range n).map (fun q => n - 1 - q) = (List.range n).reverse := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]

theorem foldr_rev {β : Type} (F : Nat → β → β) (s : β) (n : Nat) :
    (List.range n).foldr (fun q h => F (n - 1 - q) h) s =
      (List.range n).foldl (fun h a => F a h) s := by
  rw [← List.foldr_map (f := fun q => n - 1 - q) (g := F), range_map_rev, List.foldr_reverse]

theorem hrun_append (x : Nat) (l l' : List Nat) (h : Nat) :
    hrun x (l ++ l') h = hrun x l' (hrun x l h) := by
  unfold hrun
  rw [List.foldl_append]

theorem chunks_eq (x : Nat) (s : Nat) : ∀ k,
    (List.range k).foldl (fun h a => hrun x (List.range' (64 * a) 64) h) s =
      hrun x (List.range (64 * k)) s
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, chunks_eq x s k,
      ← hrun_append, show 64 * (k + 1) = 64 * k + 64 by ring, List.range_add,
      List.range'_eq_map_range]

theorem hrun_tail (x h : Nat) : ∀ l : List Nat, (∀ i ∈ l, 4060 ≤ i) → hrun x l h = h
  | [], _ => rfl
  | i :: l, hl => by
    unfold hrun
    rw [List.foldl_cons, if_neg (by have := hl i List.mem_cons_self; omega)]
    exact hrun_tail x h l fun j hj => hl j (List.mem_cons_of_mem _ hj)

theorem hkeyP_run (x : Nat) : hkeyP x = hrun x (List.range 4060) 14695981039346656037 := by
  have h1 : hkeyP x = (List.range 64).foldr
      (fun q h => hrun x (List.range' (64 * (63 - q)) 64) h) 14695981039346656037 := by
    unfold hkeyP
    rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
    congr 1
    funext q h
    rw [strictN_eq]
    have := inner_eq x q 64 (le_refl _) h
    rw [Nat.add_sub_cancel] at this
    exact this
  rw [h1, foldr_rev (fun a h => hrun x (List.range' (64 * a) 64) h) _ 64, chunks_eq,
    show 64 * 64 = 4060 + 36 by norm_num, List.range_add, hrun_append,
    hrun_tail x _ _ (fun i hi => by simp at hi; omega)]

theorem hkeyOf_toNat (g : G) : ∀ m ≤ 4060,
    (Nat.fold m (fun i _ h => (h ^^^ (UInt32.ofNat (CFSG.Sporadic.Th.idx 4060 g i)).toUInt64) *
      1099511628211) (14695981039346656037 : UInt64)).toNat =
      (List.range m).foldl (fun h i => hst h (CFSG.Sporadic.Th.idx 4060 g i)) 14695981039346656037
  | 0, _ => by rw [Nat.fold_zero]; rfl
  | m + 1, hm => by
    rw [Nat.fold_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← hkeyOf_toNat g m (by omega)]
    have hlt : CFSG.Sporadic.Th.idx 4060 g m < 2 ^ 32 := by
      rw [CFSG.Sporadic.Th.idx_of_lt _ (by omega : m < 4060)]
      exact lt_trans (Fin.isLt _) (by norm_num)
    rw [UInt64.toNat_mul, UInt64.toNat_xor, UInt32.toNat_toUInt64, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt hlt]
    rfl

theorem foldl_congr_mem {β : Type} (f g : β → Nat → β) : ∀ (l : List Nat) (s : β),
    (∀ b, ∀ i ∈ l, f b i = g b i) → l.foldl f s = l.foldl g s
  | [], _, _ => rfl
  | i :: l, s, h => by
    rw [List.foldl_cons, List.foldl_cons, h s i List.mem_cons_self]
    exact foldl_congr_mem f g l _ fun b j hj => h b j (List.mem_cons_of_mem _ hj)

theorem hkeyP_eq {x : Nat} {g : G} (hx : PRep 4060 12 x g) :
    hkeyP x = (CFSG.Sporadic.SmallOddCore.hkeyOf 4060 g).toNat := by
  rw [hkeyP_run, CFSG.Sporadic.SmallOddCore.hkeyOf, hkeyOf_toNat g 4060 (le_refl _)]
  unfold hrun
  refine foldl_congr_mem _ _ _ _ fun h i hi => ?_
  rw [List.mem_range] at hi
  rw [if_pos hi, hx ⟨i, hi⟩, CFSG.Sporadic.Th.idx_of_lt _ hi]
  rfl

end CFSG.KC.Misc.RuInv.P

end
