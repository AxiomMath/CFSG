module

public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Fi22LH.Bits
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KS.TW CFSG.KC.Enum

@[expose] noncomputable def posC (cq j : Nat) : Nat := fld(cq, Nat.mul (nat_lit 9) j, nat_lit 511)

theorem commK_spec {R X : Nat → Nat} {lb cq : Nat} (hc : commK R X lb cq = true) :
    fd (X 0) 30 4095 = 0 ∧ fd (X 0) 42 511 = 0 ∧
      (∀ j < 351, posC cq j < 351 ∧ fd (X (posC cq j)) 30 4095 = ent lb j) ∧
      (List.range 351).foldl (fun n h => if h < n then (List.range 351).foldl
        (fun m j => commHit X lb cq (R (fd (X h) 30 4095)) h j m) n else 0) 1 = 351 := by
  unfold commK at hc
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨h1, h2, fun j hj => ?_, ?_⟩
  · have := allN_iff.1 h3 j hj
    rw [strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  · simp only [foldUp_eq, nIf_eq, Nat.blt_eq, strictN_eq] at h4
    exact h4

theorem commHit_zero (X : Nat → Nat) (lb cq r h j : Nat) : commHit X lb cq r h j 0 = 0 := by
  unfold commHit
  rw [beq_true rfl]

theorem commHit_spec {X : Nat → Nat} {lb cq r h j n : Nat} (hne : commHit X lb cq r h j n ≠ 0) :
    (ent r (ent lb j) ≠ ent lb j ∧ commHit X lb cq r h j n = n) ∨
      (ent r (ent lb j) = ent lb j ∧ posC cq j < n ∧ commHit X lb cq r h j n = n) ∨
      (ent r (ent lb j) = ent lb j ∧ posC cq j = n ∧ fd (X n) 30 4095 = ent lb j ∧
        fd (X n) 42 511 = h ∧ commHit X lb cq r h j n = n + 1) := by
  have e : commHit X lb cq r h j n = if n = 0 then 0 else
      if ent r (ent lb j) = ent lb j then
        (if posC cq j < n then n else if posC cq j = n then
          (if fd (X n) 30 4095 = ent lb j ∧ fd (X n) 42 511 = h then n + 1 else 0) else 0)
      else n := by
    unfold commHit
    simp only [nIf_eq, strictN_eq, Nat.beq_eq, Nat.blt_eq, bAnd_eq, Bool.and_eq_true]
    rfl
  rw [e] at hne ⊢
  split_ifs at hne ⊢ with h1 h2 h3 h4 h5
  · exact absurd rfl hne
  · exact Or.inr (Or.inl ⟨h2, h3, rfl⟩)
  · exact Or.inr (Or.inr ⟨h2, h4, h5.1, h5.2, rfl⟩)
  · exact absurd rfl hne
  · exact absurd rfl hne
  · exact Or.inl ⟨h2, rfl⟩

variable {R X : Nat → Nat} {lb cq : Nat}

theorem comm_ord (hinc : incK lb = true)
    (hpos : ∀ j < 351, posC cq j < 351 ∧ fd (X (posC cq j)) 30 4095 = ent lb j) :
    (∀ k < 351, ∃ j < 351, posC cq j = k) ∧
      ∀ k < 351, ∀ k' < 351, fd (X k) 30 4095 = fd (X k') 30 4095 → k = k' := by
  have hinj : ∀ j < 351, ∀ j' < 351, ent lb j = ent lb j' → j = j' := by
    intro j hj j' hj' e
    have hi := (incK_spec hinc).1
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hi j j' h hj'
      omega
    · have := hi j' j h hj
      omega
  let f : Fin 351 → Fin 351 := fun j => ⟨posC cq j, (hpos j j.2).1⟩
  have hf : Function.Injective f := by
    intro a b e
    have e' : posC cq a = posC cq b := congrArg Fin.val e
    apply Fin.ext
    apply hinj a a.2 b b.2
    rw [← (hpos a a.2).2, ← (hpos b b.2).2, e']
  have hsurj := Finite.surjective_of_injective hf
  have hall : ∀ k < 351, ∃ j < 351, posC cq j = k := fun k hk => by
    obtain ⟨j, hj⟩ := hsurj ⟨k, hk⟩
    exact ⟨j, j.2, congrArg Fin.val hj⟩
  refine ⟨hall, fun k hk k' hk' e => ?_⟩
  obtain ⟨j, hj, rfl⟩ := hall k hk
  obtain ⟨j', hj', rfl⟩ := hall k' hk'
  rw [(hpos j hj).2, (hpos j' hj').2] at e
  rw [hinj j hj j' hj' e]

@[expose] def CInv (X : Nat → Nat) (m : Nat) (s : Array Nat × Array Nat × Bits) : Prop :=
  s.1.size = m ∧ (∀ k < m, s.1[k]! = fd (X k) 30 4095) ∧ s.2.1.size = m ∧
    (∀ k < m, s.2.1[k]! = fd (X k) 42 511) ∧ BitsIs s.2.2 fun y => ∃ k < m, fd (X k) 30 4095 = y

theorem cinv_eta {X : Nat → Nat} {m : Nat} {a : Array Nat × Array Nat × Bits} (h : CInv X m a) :
    CInv X m (a.1, a.2.1, a.2.2) := h

@[expose] def cStep (T : Array Table) (h x y : Nat) (s : Array Nat × Array Nat × Bits) :
    Array Nat × Array Nat × Bits :=
  if (!bitAt s.2.2 y && ap T[x]! y == y) = true then (s.1.push y, s.2.1.push h, setBit s.2.2 y)
  else s

theorem cStep_inv {T : Array Table} (hT : ∀ k < 3510, TR 3510 T[k]! (ent (R k)))
    (hinc : incK lb = true)
    (hpos : ∀ j < 351, posC cq j < 351 ∧ fd (X (posC cq j)) 30 4095 = ent lb j)
    {h j m : Nat} (hj : j < 351) {s : Array Nat × Array Nat × Bits} (hs : CInv X m s) (hm : m ≤ 351)
    (hx : fd (X h) 30 4095 < 3510)
    (hne : commHit X lb cq (R (fd (X h) 30 4095)) h j m ≠ 0)
    (hle : commHit X lb cq (R (fd (X h) 30 4095)) h j m ≤ 351) :
    CInv X (commHit X lb cq (R (fd (X h) 30 4095)) h j m)
      (cStep T h (fd (X h) 30 4095) (ent lb j) s) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hy : ent lb j < 3510 := (incK_spec hinc).2 j hj
  have hap : ap T[fd (X h) 30 4095]! (ent lb j) = ent (R (fd (X h) 30 4095)) (ent lb j) :=
    ((hT _ hx).2 _ hy).1
  obtain ⟨-, hord⟩ := comm_ord hinc hpos
  rcases commHit_spec hne with ⟨hc, he⟩ | ⟨hc, hp, he⟩ | ⟨hc, hp, ho, hpa, he⟩
  · rw [he]
    unfold cStep
    rw [if_neg (by rw [hap]; simp [hc])]
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [he]
    have hseen : bitAt s.2.2 (ent lb j) = true :=
      (h5.2 _ (by omega)).2 ⟨posC cq j, hp, (hpos j hj).2⟩
    unfold cStep
    rw [if_neg (by rw [hseen]; simp)]
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [he]
    have hseen : bitAt s.2.2 (ent lb j) = false := by
      rw [Bool.eq_false_iff]
      intro e
      obtain ⟨k, hk, hk2⟩ := (h5.2 _ (by omega)).1 e
      rw [← (hpos j hj).2] at hk2
      have := hord k (by omega) (posC cq j) (hpos j hj).1 hk2
      omega
    unfold cStep
    rw [if_pos (by rw [hseen, hap, hc]; simp)]
    refine ⟨by rw [Array.size_push, h1], fun k hk => ?_, by rw [Array.size_push, h3],
      fun k hk => ?_, (bitsIs_setBit h5 (by omega)).congr fun y _ => ?_⟩
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h1]; exact hk'), h2 k hk']
      · have : k = s.1.size := by omega
        rw [this, get!_push_eq, h1, ho]
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h3]; exact hk'), h4 k hk']
      · have : k = s.2.1.size := by omega
        rw [this, get!_push_eq, h3, hpa]
    · constructor
      · rintro (⟨k, hk, e⟩ | e)
        · exact ⟨k, by omega, e⟩
        · exact ⟨m, by omega, by rw [ho, e]⟩
      · rintro ⟨k, hk, e⟩
        rcases Nat.lt_or_ge k m with hk' | hk'
        · exact Or.inl ⟨k, hk', e⟩
        · right
          rw [← e, show k = m by omega, ho]

theorem toList_eq_map {S : Array Nat} (hS : S.size = 351) (hSj : ∀ j < 351, S[j]! = ent lb j) :
    S.toList = (List.range 351).map fun j => ent lb j := by
  apply List.ext_getElem (by simp [hS])
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, Array.getElem_toList, ← getElem!_pos S i (by
    simpa using h1), hSj i (by simpa [hS] using h1)]

theorem commTree_eq_of {T : Array Table} {S : Array Nat}
    (hT : ∀ k < 3510, TR 3510 T[k]! (ent (R k))) (hS : S.size = 351)
    (hSj : ∀ j < 351, S[j]! = ent lb j) (hinc : incK lb = true) (h0 : ent lb 0 = 0)
    (hc : commK R X lb cq = true) :
    commTree T S = (Array.ofFn (n := 351) fun k => fd (X k.val) 30 4095,
      Array.ofFn (n := 351) fun k => fd (X k.val) 42 511) := by
  obtain ⟨ho0, hp0, hpos, hfold⟩ := commK_spec hc
  obtain ⟨hall, hord⟩ := comm_ord hinc hpos
  have hordlt : ∀ k < 351, fd (X k) 30 4095 < 3510 := fun k hk => by
    obtain ⟨j, hj, rfl⟩ := hall k hk
    rw [(hpos j hj).2]
    exact (incK_spec hinc).2 j hj
  let H : Nat → Nat → Nat → Nat := fun h j m => commHit X lb cq (R (fd (X h) 30 4095)) h j m
  let Sf : Nat → Nat → Nat := fun h n =>
    if h < n then (List.range 351).foldl (fun m j => H h j m) n else 0
  let C : Nat → Nat := fun h => (List.range h).foldl (fun n h => Sf h n) 1
  have hCN : C 351 = 351 := by
    simp only [C, Sf, H]
    exact hfold
  have hC_succ : ∀ h, C (h + 1) = Sf h (C h) := fun h => by
    simp only [C, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hH0 : ∀ h j, H h j 0 = 0 := fun h j => commHit_zero _ _ _ _ _ _
  have hHm : ∀ h j m, H h j m ≠ 0 → m ≤ H h j m := fun h j m hne => by
    rcases commHit_spec hne with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, _, he⟩
    · exact Nat.le_of_eq he.symm
    · exact Nat.le_of_eq he.symm
    · change m ≤ commHit X lb cq (R (fd (X h) 30 4095)) h j m
      rw [he]
      omega
  have hS0 : ∀ h, Sf h 0 = 0 := fun h => by simp [Sf]
  have hSm : ∀ h m, Sf h m ≠ 0 → m ≤ Sf h m := fun h m hne => by
    simp only [Sf] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      exact (fold_nonzero (fun j m => H h j m) (fun j => hH0 h j) (fun j m => hHm h j m) _ _ hne).2
    · exact absurd rfl hne
  have hC : ∀ h ≤ 351, C h ≠ 0 ∧ C h ≤ 351 := by
    intro h hh
    have e : (List.range 351).foldl (fun n h => Sf h n) 1 =
        ((List.range (351 - h)).map (h + ·)).foldl (fun n h => Sf h n) (C h) := by
      have eN : 351 = h + (351 - h) := by omega
      conv_lhs => rw [eN]
      rw [List.range_add, List.foldl_append]
    have h2 : ((List.range (351 - h)).map (h + ·)).foldl (fun n h => Sf h n) (C h) ≠ 0 := by
      rw [← e]
      change C 351 ≠ 0
      omega
    have := fold_nonzero Sf hS0 hSm _ _ h2
    rw [← e] at this
    change C h ≠ 0 ∧ C h ≤ C 351 at this
    rw [hCN] at this
    exact this
  have hCh : ∀ h < 351, h < C h := by
    intro h hh
    have := (hC (h + 1) hh).1
    rw [hC_succ] at this
    simp only [Sf] at this
    split at this
    · assumption
    · exact absurd rfl this
  have hinner : ∀ h < 351, ∀ s, CInv X (C h) s →
      CInv X (C (h + 1)) ((List.range 351).foldl
        (fun s j => cStep T h (fd (X h) 30 4095) (ent lb j) s) s) := by
    intro h hh s hs
    have hfin : C (h + 1) = (List.range 351).foldl (fun m j => H h j m) (C h) := by
      rw [hC_succ]
      simp only [Sf, if_pos (hCh h hh)]
    have hgen : ∀ j ≤ 351, CInv X ((List.range j).foldl (fun m j => H h j m) (C h))
        ((List.range j).foldl (fun s j => cStep T h (fd (X h) 30 4095) (ent lb j) s) s) := by
      intro j
      induction j with
      | zero => intro _; exact hs
      | succ j ih =>
        intro hj
        rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_cons, List.foldl_nil]
        have e : (List.range 351).foldl (fun m j => H h j m) (C h) =
            ((List.range (351 - (j + 1))).map ((j + 1) + ·)).foldl (fun m j => H h j m)
              (H h j ((List.range j).foldl (fun m j => H h j m) (C h))) := by
          have enl : 351 = j + 1 + (351 - (j + 1)) := by omega
          conv_lhs => rw [enl]
          rw [List.range_add, List.foldl_append, List.range_succ, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
        have hne : ((List.range (351 - (j + 1))).map ((j + 1) + ·)).foldl (fun m j => H h j m)
            (H h j ((List.range j).foldl (fun m j => H h j m) (C h))) ≠ 0 := by
          rw [← e, ← hfin]
          exact (hC (h + 1) hh).1
        obtain ⟨hne1, hle1⟩ := fold_nonzero (fun j m => H h j m) (fun j => hH0 h j)
          (fun j m => hHm h j m) _ _ hne
        rw [← e, ← hfin] at hle1
        have hle2 := (hC (h + 1) hh).2
        have hm : (List.range j).foldl (fun m j => H h j m) (C h) ≤ 351 := by
          have := hHm h j _ hne1
          omega
        exact cStep_inv hT hinc hpos (by omega) (ih (by omega)) hm (hordlt h hh) hne1
          (Nat.le_trans hle1 hle2)
    rw [hfin]
    exact hgen 351 (Nat.le_refl _)
  obtain ⟨s, hs, hT'⟩ : ∃ s : Array Nat × Array Nat × Bits,
      commTree T S = (s.1, s.2.1) ∧ CInv X 351 s := by
    unfold commTree
    refine ⟨_, rfl, ?_⟩
    rw [hS]
    refine range_loop (fun q s => q ≤ 351 ∧ CInv X (C q) s) (CInv X 351) _ 351 _ ?_ ?_ ?_
    · intro q s hq hI
      obtain ⟨hqN, hI⟩ := hI
      have hqs : q < s.1.size := by rw [hI.1]; exact hCh q hq
      have hx : s.1[q]! = fd (X q) 30 4095 := hI.2.1 q (hCh q hq)
      simp only [hqs, ↓reduceIte, hx]
      rw [← Array.forIn_toList, toList_eq_map hS hSj,
        forIn_yield _ (fun y s => cStep T q (fd (X q) 30 4095) y s) (fun a b => by
          unfold cStep
          split <;> rfl), List.foldl_map]
      exact ⟨by omega, cinv_eta (hinner q hq (s.1, s.2.1, s.2.2) hI)⟩
    · intro s hs
      have := hs.2
      rw [hCN] at this
      exact this
    · refine ⟨Nat.zero_le _, ?_⟩
      change CInv X 1 _
      refine ⟨rfl, fun k hk => ?_, rfl, fun k hk => ?_,
        (bitsIs_setBit bitsIs_empty (by decide)).congr fun y _ => ?_⟩
      · have : k = 0 := by omega
        subst this
        rw [ho0]
        rfl
      · have : k = 0 := by omega
        subst this
        rw [hp0]
        rfl
      · constructor
        · rintro (h | h)
          · exact h.elim
          · exact ⟨0, by omega, by rw [ho0, h]⟩
        · rintro ⟨k, hk, e⟩
          right
          rw [← e, show k = 0 by omega, ho0]
  rw [hs]
  obtain ⟨h1, h2, h3, h4, -⟩ := hT'
  have hof : ∀ (a : Array Nat) (g : Nat → Nat), a.size = 351 → (∀ k < 351, a[k]! = g k) →
      a = Array.ofFn (n := 351) fun k => g k.val := by
    intro a g hs hg
    apply Array.ext (by rw [hs, Array.size_ofFn])
    intro i hi1 hi2
    rw [Array.getElem_ofFn, ← getElem!_pos a i hi1, hg i (by omega)]
  rw [hof _ _ h1 h2, hof _ _ h3 h4]

theorem commK_facts (hc : commK R X lb cq = true) :
    ∀ k, 0 < k → k < 351 → fd (X k) 42 511 < k ∧ (∃ j < 351, fd (X k) 30 4095 = ent lb j) ∧
      ent (R (fd (X (fd (X k) 42 511)) 30 4095)) (fd (X k) 30 4095) = fd (X k) 30 4095 := by
  obtain ⟨-, -, -, hfold⟩ := commK_spec hc
  let H : Nat → Nat → Nat → Nat := fun h j m => commHit X lb cq (R (fd (X h) 30 4095)) h j m
  let Sf : Nat → Nat → Nat := fun h n =>
    if h < n then (List.range 351).foldl (fun m j => H h j m) n else 0
  let C : Nat → Nat := fun h => (List.range h).foldl (fun n h => Sf h n) 1
  have hCN : C 351 = 351 := by
    simp only [C, Sf, H]
    exact hfold
  have hC_succ : ∀ h, C (h + 1) = Sf h (C h) := fun h => by
    simp only [C, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hH0 : ∀ h j, H h j 0 = 0 := fun h j => commHit_zero _ _ _ _ _ _
  have hHm : ∀ h j m, H h j m ≠ 0 → m ≤ H h j m := fun h j m hne => by
    rcases commHit_spec hne with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, _, he⟩
    · exact Nat.le_of_eq he.symm
    · exact Nat.le_of_eq he.symm
    · change m ≤ commHit X lb cq (R (fd (X h) 30 4095)) h j m
      rw [he]
      omega
  have hS0 : ∀ h, Sf h 0 = 0 := fun h => by simp [Sf]
  have hSm : ∀ h m, Sf h m ≠ 0 → m ≤ Sf h m := fun h m hne => by
    simp only [Sf] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      exact (fold_nonzero (fun j m => H h j m) (fun j => hH0 h j) (fun j m => hHm h j m) _ _ hne).2
    · exact absurd rfl hne
  have hC : ∀ h ≤ 351, C h ≠ 0 ∧ C h ≤ 351 := by
    intro h hh
    have e : (List.range 351).foldl (fun n h => Sf h n) 1 =
        ((List.range (351 - h)).map (h + ·)).foldl (fun n h => Sf h n) (C h) := by
      have eN : 351 = h + (351 - h) := by omega
      conv_lhs => rw [eN]
      rw [List.range_add, List.foldl_append]
    have h2 : ((List.range (351 - h)).map (h + ·)).foldl (fun n h => Sf h n) (C h) ≠ 0 := by
      rw [← e]
      change C 351 ≠ 0
      omega
    have := fold_nonzero Sf hS0 hSm _ _ h2
    rw [← e] at this
    change C h ≠ 0 ∧ C h ≤ C 351 at this
    rw [hCN] at this
    exact this
  have hCh : ∀ h < 351, h < C h := by
    intro h hh
    have := (hC (h + 1) hh).1
    rw [hC_succ] at this
    simp only [Sf] at this
    split at this
    · assumption
    · exact absurd rfl this
  let M : Nat → Nat → Nat := fun h j => (List.range j).foldl (fun m j => H h j m) (C h)
  have hM : ∀ h < 351, ∀ j < 351, H h j (M h j) ≠ 0 ∧ C h ≤ M h j := by
    intro h hh j hj
    have hfin : C (h + 1) = (List.range 351).foldl (fun m j => H h j m) (C h) := by
      rw [hC_succ]
      simp only [Sf, if_pos (hCh h hh)]
    have e : (List.range 351).foldl (fun m j => H h j m) (C h) =
        ((List.range (351 - (j + 1))).map ((j + 1) + ·)).foldl (fun m j => H h j m)
          (H h j (M h j)) := by
      have enl : 351 = j + 1 + (351 - (j + 1)) := by omega
      conv_lhs => rw [enl]
      rw [List.range_add, List.foldl_append, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    have hne : ((List.range (351 - (j + 1))).map ((j + 1) + ·)).foldl (fun m j => H h j m)
        (H h j (M h j)) ≠ 0 := by
      rw [← e, ← hfin]
      exact (hC (h + 1) hh).1
    obtain ⟨hne1, -⟩ := fold_nonzero (fun j m => H h j m) (fun j => hH0 h j)
      (fun j m => hHm h j m) _ _ hne
    have hne2 : (List.range j).foldl (fun m j => H h j m) (C h) ≠ 0 := by
      intro e0
      have : H h j (M h j) = 0 := by
        change H h j ((List.range j).foldl (fun m j => H h j m) (C h)) = 0
        rw [e0]
        exact hH0 h j
      exact hne1 this
    exact ⟨hne1, (fold_nonzero (fun j m => H h j m) (fun j => hH0 h j) (fun j m => hHm h j m) _ _
      hne2).2⟩
  have hM_succ : ∀ h j, M h (j + 1) = H h j (M h j) := fun h j => by
    simp only [M, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP : ∀ h ≤ 351, ∀ k, 0 < k → k < C h → fd (X k) 42 511 < k ∧
      (∃ j < 351, fd (X k) 30 4095 = ent lb j) ∧
      ent (R (fd (X (fd (X k) 42 511)) 30 4095)) (fd (X k) 30 4095) = fd (X k) 30 4095 := by
    intro h
    induction h with
    | zero =>
      intro _ k hk0 hk
      have : C 0 = 1 := rfl
      omega
    | succ h ih =>
      intro hh k hk0 hk
      have hQ : ∀ j ≤ 351, ∀ k, 0 < k → k < M h j → fd (X k) 42 511 < k ∧
          (∃ j < 351, fd (X k) 30 4095 = ent lb j) ∧
          ent (R (fd (X (fd (X k) 42 511)) 30 4095)) (fd (X k) 30 4095) = fd (X k) 30 4095 := by
        intro j
        induction j with
        | zero => intro _ k hk0 hk; exact ih (by omega) k hk0 hk
        | succ j ihj =>
          intro hj k hk0 hk
          rw [hM_succ] at hk
          obtain ⟨hne, hpre⟩ := hM h (by omega) j (by omega)
          rcases commHit_spec hne with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨hcom, _, ho, hpa, he⟩
          · rw [show H h j (M h j) = M h j from he] at hk
            exact ihj (by omega) k hk0 hk
          · rw [show H h j (M h j) = M h j from he] at hk
            exact ihj (by omega) k hk0 hk
          · rw [show H h j (M h j) = M h j + 1 from he] at hk
            rcases Nat.lt_or_ge k (M h j) with h1 | h1
            · exact ihj (by omega) k hk0 h1
            · have hk' : k = M h j := by omega
              subst hk'
              have := hCh h (by omega)
              refine ⟨by rw [hpa]; omega, ⟨j, by omega, ho⟩, ?_⟩
              rw [hpa, ho]
              exact hcom
      have hfin : C (h + 1) = M h 351 := by
        rw [hC_succ]
        simp only [Sf, M, if_pos (hCh h (by omega))]
      rw [hfin] at hk
      exact hQ 351 (Nat.le_refl _) k hk0 hk
  intro k hk0 hk
  exact hP 351 (Nat.le_refl _) k hk0 (by rw [hCN]; exact hk)

end CFSG.KS.Fi22LH
