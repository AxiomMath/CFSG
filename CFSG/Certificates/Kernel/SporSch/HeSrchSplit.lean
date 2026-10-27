module

public import Certificates.Data.Kernel.SporSch.HeSrchK
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

theorem foldl_sum {f : Nat → Nat → Nat} (h : ∀ i s, f i s = s + f i 0) :
    ∀ (l : List Nat) (s : Nat), l.foldl (fun s i => f i s) s = s + (l.map (fun i => f i 0)).sum
  | [], s => by simp
  | i :: l, s => by
    rw [List.foldl_cons, foldl_sum h l, h i s, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem foldUp_sum {f : Nat → Nat → Nat} (h : ∀ i s, f i s = s + f i 0) (m s : Nat) :
    foldUp m f s = s + ((List.range m).map (fun i => f i 0)).sum := by
  rw [foldUp_eq]
  exact foldl_sum h _ s

theorem srchAK1_shift (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat)
    (X Y : Nat → Nat) (k0 k1 s : Nat) :
    srchAK1 w kS NR NL LT PT QT LR bs X Y k0 k1 s =
      s + srchAK1 w kS NR NL LT PT QT LR bs X Y k0 k1 0 := by
  have hf : ∀ (m : Nat) (f : Nat → Nat → Nat), (∀ i s, f i s = s + f i 0) →
      ∀ s, foldUp m f s = s + foldUp m f 0 := fun m f h s => by
    rw [foldUp_sum h, foldUp_sum h m 0, Nat.zero_add]
  unfold srchAK1
  simp only [strictN_eq]
  cases Nat.blt _ _
  · rfl
  · refine hf _ _ (fun k3 s => ?_) s
    refine hf _ _ (fun k4 s => ?_) s
    cases eqOnL _ _ _
    · rfl
    · rfl

theorem srchAK_eq (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat) (b0 : Nat)
    (X Y : Nat → Nat) (k0 lo len : Nat) :
    srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 lo len =
      nIf(Nat.beq (Y (trPtT w NR NL LT PT 0 k0 b0)) (trPtT w NR NL LT PT 0 k0 b0),
        ((List.range len).map (fun j => nIf(Nat.blt (lo + j) (rcnt (LR 1)),
          srchAK1 w kS NR NL LT PT QT LR bs X Y k0 (lo + j) 0, 0))).sum, 0) := by
  unfold srchAK
  rw [strictN_eq]
  cases Nat.beq _ _
  · rfl
  · refine (foldUp_sum (fun j s => ?_) len 0).trans (Nat.zero_add _)
    change nIf(Nat.blt (lo + j) (rcnt (LR 1)), srchAK1 w kS NR NL LT PT QT LR bs X Y k0 (lo + j) s,
      s) = s + nIf(Nat.blt (lo + j) (rcnt (LR 1)),
        srchAK1 w kS NR NL LT PT QT LR bs X Y k0 (lo + j) 0, 0)
    cases Nat.blt _ _
    · rfl
    · exact srchAK1_shift ..

theorem srchAK_add (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat) (b0 : Nat)
    (X Y : Nat → Nat) (k0 lo a b : Nat) :
    srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 lo (a + b) =
      srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 lo a +
        srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 (lo + a) b := by
  rw [srchAK_eq, srchAK_eq, srchAK_eq]
  cases Nat.beq _ _
  · rfl
  · change List.sum _ = List.sum _ + List.sum _
    rw [List.range_add, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def, Nat.add_assoc]

theorem srchAK_sumN (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat) (b0 : Nat)
    (X Y : Nat → Nat) (k0 lo c : Nat) :
    ∀ m, srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 lo (m * c) =
      sumN m (fun i => srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 (lo + i * c) c)
  | 0 => by
    rw [srchAK_eq, Nat.zero_mul]
    cases Nat.beq _ _ <;> rfl
  | m + 1 => by
    change _ = strictN (sumN m _) (fun a => Nat.add _ a)
    rw [strictN_eq, Nat.succ_mul, srchAK_add, srchAK_sumN w kS NR NL LT PT QT LR bs b0 X Y k0 lo c m,
      Nat.add_eq, Nat.add_comm]

theorem srchAAt_eq_K (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat) (b0 : Nat)
    (X Y : Nat → Nat) (k0 : Nat) :
    srchAAt w kS NR NL LT PT QT LR bs b0 X Y k0 =
      srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 0 (rcnt (LR 1)) := by
  rw [srchAK_eq]
  unfold srchAAt
  rw [strictN_eq]
  cases Nat.beq _ _
  · rfl
  · change foldUp _ (fun k1 s => srchAK1 w kS NR NL LT PT QT LR bs X Y k0 k1 s) 0 = _
    rw [foldUp_sum (f := fun k1 s => srchAK1 w kS NR NL LT PT QT LR bs X Y k0 k1 s)
      (fun k1 s => srchAK1_shift ..), Nat.zero_add]
    change _ = List.sum _
    refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
    have hb : Nat.blt j (rcnt (LR 1)) = true := by
      rw [Nat.blt_eq]
      exact List.mem_range.1 hj
    rw [Nat.zero_add, hb]

theorem srchAAt_split (w kS NR NL : Nat) (LT PT QT LR : Nat → Nat) (bs : List Nat) (b0 : Nat)
    (X Y : Nat → Nat) (k0 m c : Nat) (h : rcnt (LR 1) = m * c) :
    srchAAt w kS NR NL LT PT QT LR bs b0 X Y k0 =
      sumN m (fun i => srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 (i * c) c) := by
  rw [srchAAt_eq_K, h, srchAK_sumN]
  simp only [Nat.zero_add]

theorem sumN_zero {f : Nat → Nat} : ∀ {m}, (∀ i < m, f i = 0) → sumN m f = 0
  | 0, _ => rfl
  | m + 1, h => by
    change strictN (sumN m f) (fun a => Nat.add (f m) a) = 0
    rw [strictN_eq, sumN_zero (fun i hi => h i (by omega)), h m (by omega)]

theorem srchAAt_eq_zero {w kS NR NL : Nat} {LT PT QT LR : Nat → Nat} {bs : List Nat} {b0 : Nat}
    {X Y : Nat → Nat} {k0 m c : Nat} (h : rcnt (LR 1) = m * c)
    (hz : ∀ i < m, srchAK w kS NR NL LT PT QT LR bs b0 X Y k0 (i * c) c = 0) :
    srchAAt w kS NR NL LT PT QT LR bs b0 X Y k0 = 0 := by
  rw [srchAAt_split w kS NR NL LT PT QT LR bs b0 X Y k0 m c h]
  exact sumN_zero hz

end CFSG.KS.SporSch

end
