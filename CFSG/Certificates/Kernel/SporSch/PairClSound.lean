module

public import CFSG.Certificates.Kernel.SporSch.PairClDefs
import CFSG.Certificates.Kernel.SporSch.PairClProof
import CFSG.Certificates.Kernel.SporSch.Cnt3Proof
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.PairNative

theorem pairwise_of_strictInc : ∀ {l : List Nat}, strictInc l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: l, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_strictInc h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem nodup_of_strictInc_mergeSort {l : List Nat} (h : strictInc l.mergeSort = true) :
    l.Nodup :=
  ((List.mergeSort_perm _ _).nodup_iff).1 ((pairwise_of_strictInc h).imp Nat.ne_of_lt)

theorem closNF_sound {n w kS nb BP kg c cap nS R H nB B : Nat} {PS PSI LR TR TRI G GI X W C : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs RP : List Nat}
    {gens gensInv : Array (Array Nat)} {rep : List (Array Nat)}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hbs : base.toList = bs)
    (hg : gens.size = kg ∧ gensInv.size = kg ∧
      ∀ l < kg, gens[l]! = unpack n w (G l) ∧ gensInv[l]! = unpack n w (GI l))
    (hrep : rep = RP.map (unpack n w))
    (h : ClosNFOK n w kS nb BP PS PSI LR TR TRI bs kg G GI RP c cap nS R H nB B X W C)
    (hD : ((List.range c).map fun i => nfKey n w LR TR nb bs (nfX nb (X i))).Nodup) :
    closureOK (rawLevels n S base) bs gens gensInv rep
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.2 = true ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.size = c ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.toList.map
          (fun nf => imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf))) =
        (List.range c).map fun i => nfKey n w LR TR nb bs (nfX nb (X i)) :=
  ClP.closNF_proved hb hp hl hbs hg hrep h hD

@[expose] noncomputable def keyOf (cs : List (Nat × (Nat → Nat))) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih i => Prod.rec (motive := fun _ => Nat) (fun c K => nIf(Nat.blt i c, K i, ih (Nat.sub i c))) p)
    cs i

@[expose] noncomputable def keySortAt (cs : List (Nat × (Nat → Nat))) (SO SOI : Nat → Nat) (N i : Nat) :
    Bool :=
  bIf(Nat.blt i N, strictB (SO i) (fun j => bAnd(Nat.blt j N, bAnd(Nat.beq (SOI j) i,
    bIf(Nat.blt (Nat.succ i) N, Nat.blt (keyOf cs j) (keyOf cs (SO (Nat.succ i))), true)))), true)

theorem keyOf_flat : ∀ cs : List (Nat × (Nat → Nat)),
    (List.range (cs.map Prod.fst).sum).map (keyOf cs) = cs.flatMap fun p => (List.range p.1).map p.2
  | [] => rfl
  | (c, K) :: cs => by
    rw [List.map_cons, List.sum_cons, List.range_add, List.map_append, List.map_map,
      List.flatMap_cons, ← keyOf_flat cs]
    congr 1
    · refine List.map_congr_left fun i hi => ?_
      have e : Nat.blt i c = true := by simpa using hi
      change nIf(Nat.blt i c, K i, keyOf cs (Nat.sub i c)) = K i
      rw [e]
    · refine List.map_congr_left fun j _ => ?_
      have e : Nat.blt (c + j) c = false := Bool.eq_false_iff.2 (by rw [Ne, Nat.blt_eq]; omega)
      change nIf(Nat.blt (c + j) c, K (c + j), keyOf cs (Nat.sub (c + j) c)) = keyOf cs j
      rw [e]
      change keyOf cs (c + j - c) = keyOf cs j
      rw [Nat.add_sub_cancel_left]

theorem strictInc_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have h1 := List.rel_of_pairwise_cons h List.mem_cons_self
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, strictInc_of_pairwise (List.Pairwise.of_cons h)⟩

private theorem pairwise_map_range {N : Nat} {f : Nat → Nat} {S : Nat → Nat → Prop}
    (H : ∀ i j, i < j → j < N → S (f i) (f j)) : ((List.range N).map f).Pairwise S := by
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun _ hb hab => H _ _ hab (List.mem_range.1 hb)

theorem keysK_sound {cs : List (Nat × (Nat → Nat))} {SO SOI : Nat → Nat} {N nB R B : Nat}
    (hN : (cs.map Prod.fst).sum = N) (hc : N ≤ nB * R * B)
    (h : ∀ g < nB, ∀ r < R, allBlk (Nat.mul (Nat.add (Nat.mul g R) r) B) (keySortAt cs SO SOI N) B = true) :
    strictInc ((cs.flatMap fun p => (List.range p.1).map p.2).mergeSort) = true := by
  have hall : ∀ i < N, keySortAt cs SO SOI N i = true := by
    intro i hi
    have hB : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · subst h0
        rw [Nat.mul_zero] at hc
        omega
      · exact h0
    have hiB : i / B < nB * R := by
      rw [Nat.div_lt_iff_lt_mul hB]
      exact Nat.lt_of_lt_of_le hi hc
    have hR : 0 < R := by
      rcases Nat.eq_zero_or_pos R with h0 | h0
      · rw [h0, Nat.mul_zero] at hiB
        exact absurd hiB (Nat.not_lt_zero _)
      · exact h0
    have hg : i / B / R < nB := by
      rw [Nat.div_lt_iff_lt_mul hR]
      exact hiB
    have h1 := CFSG.KS.allBlk_spec (h _ hg (i / B % R) (Nat.mod_lt _ hR)) (i % B) (Nat.mod_lt _ hB)
    have e : Nat.add (Nat.mul (Nat.add (Nat.mul (i / B / R) R) (i / B % R)) B) (i % B) = i := by
      change (i / B / R * R + i / B % R) * B + i % B = i
      rw [Nat.mul_comm (i / B / R) R, Nat.div_add_mod, Nat.mul_comm, Nat.div_add_mod]
    rwa [e] at h1
  have hs : ∀ i < N, SO i < N ∧ SOI (SO i) = i ∧
      (i + 1 < N → keyOf cs (SO i) < keyOf cs (SO (i + 1))) := by
    intro i hi
    have h1 := hall i hi
    have e1 : Nat.blt i N = true := by simpa using hi
    unfold keySortAt at h1
    rw [e1] at h1
    rw [CFSG.KS.PackFld.strictB_eqP] at h1
    dsimp only at h1
    rw [bAnd_iff, bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h1
    refine ⟨h1.1, h1.2.1, fun hi1 => ?_⟩
    have e3 : Nat.blt (Nat.succ i) N = true := by simpa using hi1
    have h3 := h1.2.2
    rw [e3] at h3
    simpa using h3
  have hmono : ∀ d i, i + d + 1 < N → keyOf cs (SO i) < keyOf cs (SO (i + d + 1)) := by
    intro d
    induction d with
    | zero => exact fun i hi => (hs i (by omega)).2.2 hi
    | succ d ih =>
      intro i hi
      have e : i + (d + 1) + 1 = i + d + 1 + 1 := by omega
      rw [e]
      exact Nat.lt_trans (ih i (by omega)) ((hs (i + d + 1) (by omega)).2.2 (by omega))
  have hL : ((List.range N).map fun i => keyOf cs (SO i)).Pairwise (· < ·) :=
    pairwise_map_range fun i j hij hj => by
      have e : j = i + (j - i - 1) + 1 := by omega
      rw [e]
      exact hmono _ _ (by omega)
  have hnd : ((List.range N).map SO).Nodup :=
    pairwise_map_range fun i j hij hj he => by
      have := congrArg SOI he
      rw [(hs i (by omega)).2.1, (hs j hj).2.1] at this
      omega
  have hsub : (List.range N).map SO ⊆ List.range N := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hs i (List.mem_range.1 hi)).1
  have hP : List.Perm ((List.range N).map SO) (List.range N) :=
    (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp)
  have hP2 : List.Perm ((List.range N).map fun i => keyOf cs (SO i))
      (cs.flatMap fun p => (List.range p.1).map p.2) := by
    have e : ((List.range N).map fun i => keyOf cs (SO i)) = ((List.range N).map SO).map (keyOf cs) := by
      rw [List.map_map]
      rfl
    rw [← keyOf_flat cs, hN, e]
    exact hP.map _
  have hM := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (cs.flatMap fun p => (List.range p.1).map p.2)
  have e : (cs.flatMap fun p => (List.range p.1).map p.2).mergeSort =
      (List.range N).map fun i => keyOf cs (SO i) :=
    List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
      (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
      (hM.imp fun h => by simpa using h) (hL.imp Nat.le_of_lt)
      ((List.mergeSort_perm _ _).trans hP2.symm)
  rw [e]
  exact strictInc_of_pairwise hL

theorem cnt3_sound {n w kS BP m : Nat} {PS PSI LR TR TRI CS : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs XP : List Nat} {conds : List (List Bool × Nat)}
    (hb : Binds n w PS kS 3 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hbs : base.toList = bs)
    (hX : canonL n w XP = true) (hsz : rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    (h : ∀ k0 < rcnt (LR 0), cnt3 n w LR TR bs m XP conds k0 = CS k0) :
    countW (fun y => ordB bs y m) (blocksOf n (rawLevels n S base) [[0], [1, 2]]) [] =
        sumN (rcnt (LR 0)) (fun k0 => Nat.mod (CS k0) 1048576) ∧
      countW (fun y => ordB bs y m && condsOK bs (XP.map (unpack n w)) y conds)
          (blocksOf n (rawLevels n S base) [[0], [1, 2]]) [] =
        sumN (rcnt (LR 0)) (fun k0 => Nat.div (CS k0) 1048576) :=
  cnt3_proved hb hp hl hbs hX hsz h

end CFSG.KS.SporSch

end
