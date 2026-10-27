module

public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CFSG.KC.J4Q

open CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] noncomputable def setN (l : List Nat) (k v : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x l ih k => Nat.rec (motive := fun _ => List Nat) (List.cons v l) (fun k' _ => List.cons x (ih k')) k)
    l k

@[expose] noncomputable def insTgt (ins : Ins) : Nat :=
  Ins.rec (motive := fun _ => Nat) (fun _ _ k => k) (fun _ _ k => k) ins

@[expose] noncomputable def runL (c rm one : Nat) (regs : List Nat) (p : List Ins) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun regs => regs)
    (fun ins _ ih regs => Ins.rec (motive := fun _ => List Nat)
      (fun i j k => strictL (mulJ c rm (getN one regs i) (getN one regs j)) fun v => ih (setN regs k v))
      (fun n i k => strictL (powJ c rm one (getN one regs i) n) fun v => ih (setN regs k v)) ins)
    p regs

theorem length_setN : ∀ (l : List Nat) (k v : Nat), (setN l k v).length = l.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: l, k + 1, v => by
    change (x :: setN l k v).length = _
    rw [List.length_cons, length_setN l k v, List.length_cons]

theorem getN_setN (d : Nat) : ∀ (l : List Nat) (k v r : Nat), k < l.length →
    getN d (setN l k v) r = if r = k then v else getN d l r
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, 0, _ => rfl
  | _ :: _, 0, _, _ + 1, _ => rfl
  | _ :: l, k + 1, v, 0, _ => rfl
  | x :: l, k + 1, v, r + 1, h => by
    change getN d (setN l k v) r = _
    rw [getN_setN d l k v r (by simp at h; omega)]
    simp only [Nat.add_right_cancel_iff]
    rfl

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem runN_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    ∀ (p : List Ins) (R : Nat → Array V2) (regs : List Nat),
      (∀ r, WfA (R r) ∧ encR (R r) = getN one regs r) → (∀ ins ∈ p, insTgt ins < regs.length) →
      ∀ r, WfA (runN R p r) ∧ encR (runN R p r) = getN one (runL c rm one regs p) r
  | [], _, _, hR, _ => hR
  | .mul i j k :: p, R, regs, hR, hp => by
    have hk : k < regs.length := hp _ List.mem_cons_self
    have := runN_enc hK p (fun r => if r = k then mulRows (R i) (R j) else R r)
      (setN regs k (mulJ c rm (getN one regs i) (getN one regs j))) (by
        intro r
        rw [getN_setN _ _ _ _ _ hk]
        by_cases h : r = k
        · simp only [h, ↓reduceIte]
          exact mul_enc hK (hR i) (hR j)
        · simp only [h, ↓reduceIte]
          exact hR r)
      (fun ins hins => by rw [length_setN]; exact hp ins (List.mem_cons_of_mem _ hins))
    intro r
    rw [runN]
    refine ⟨(this r).1, (this r).2.trans ?_⟩
    change _ = getN one (strictL (mulJ c rm (getN one regs i) (getN one regs j))
      (fun v => runL c rm one (setN regs k v) p)) r
    rw [strictL_eq]
  | .pow n i k :: p, R, regs, hR, hp => by
    have hk : k < regs.length := hp _ List.mem_cons_self
    have := runN_enc hK p (fun r => if r = k then powRows (R i) n else R r)
      (setN regs k (powJ c rm one (getN one regs i) n)) (by
        intro r
        rw [getN_setN _ _ _ _ _ hk]
        by_cases h : r = k
        · simp only [h, ↓reduceIte]
          exact pow_enc hK (hR i) n
        · simp only [h, ↓reduceIte]
          exact hR r)
      (fun ins hins => by rw [length_setN]; exact hp ins (List.mem_cons_of_mem _ hins))
    intro r
    rw [runN]
    refine ⟨(this r).1, (this r).2.trans ?_⟩
    change _ = getN one (strictL (powJ c rm one (getN one regs i) n)
      (fun v => runL c rm one (setN regs k v) p)) r
    rw [strictL_eq]

end CFSG.KC.J4Q

end
