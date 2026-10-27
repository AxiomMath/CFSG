module

public import Certificates.Data.Kernel.InvTabK
public import CFSG.Quasithin.Background.SmithB45ExcHSRuPIT
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.KC.InvTabK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Quasithin.B45Exc.Tab CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2.Native

theorem subprodsI_eq {n : Nat} (T : InvTab n) :
    ∀ l, T.subprodsI l = subprodsF T.m T.prodAt l
  | [] => rfl
  | y :: l => by
    rw [InvTab.subprodsI, subprodsF, subprodsI_eq T l]

theorem greedyExtI_eq {n : Nat} (T : InvTab n) (l : List Nat) :
    T.greedyExtI l = greedyExtF T.m T.commAt T.prodAt l := by
  unfold InvTab.greedyExtI greedyExtF
  rw [subprodsI_eq]
  have e : InvTab.startI l = startF l := by cases l <;> rfl
  rw [e]

theorem forallGreedyI_eq {n : Nat} (T : InvTab n) (pred : List Nat → Bool) :
    ∀ k l, T.forallGreedyI pred k l = forallGreedyF T.m T.commAt T.prodAt pred k l
  | 0, l => rfl
  | k + 1, l => by
    rw [InvTab.forallGreedyI, forallGreedyF, greedyExtI_eq]
    congr 1
    funext x
    exact forallGreedyI_eq T pred k (x :: l)

theorem letter_unpack {n w : Nat} {regs : List PArr} {L LI : List Nat}
    (hreg : ∀ k, regs.getD k (pId n) =
      (unpack n w (L.getD k (pidn n w)), unpack n w (LI.getD k (pidn n w))))
    (hid : idA n = unpack n w (pidn n w)) (z : Int) :
    pLetter n regs z = (unpack n w (letterPK (pidn n w) L LI z).1,
      unpack n w (letterPK (pidn n w) L LI z).2) := by
  unfold pLetter letterPK
  by_cases h0 : z = 0
  · rw [if_pos h0, if_pos h0, pId, hid]
  · rw [if_neg h0, if_neg h0]
    by_cases hp : 0 < z
    · rw [if_pos hp, if_pos hp, hreg]
    · rw [if_neg hp, if_neg hp, hreg]
      rfl

theorem letter_canon {n w : Nat} {L LI : List Nat}
    (hc : ∀ k, canonK n w (mask w) (n * w) (L.getD k (pidn n w)) = true)
    (hci : ∀ k, canonK n w (mask w) (n * w) (LI.getD k (pidn n w)) = true)
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true) (z : Int) :
    canonK n w (mask w) (n * w) (letterPK (pidn n w) L LI z).1 = true ∧
      canonK n w (mask w) (n * w) (letterPK (pidn n w) L LI z).2 = true := by
  unfold letterPK
  by_cases h0 : z = 0
  · rw [if_pos h0]
    exact ⟨hidc, hidc⟩
  · rw [if_neg h0]
    by_cases hp : 0 < z
    · rw [if_pos hp]
      exact ⟨hc _, hci _⟩
    · rw [if_neg hp]
      exact ⟨hci _, hc _⟩

theorem pWord_unpack {n w : Nat} {regs : List PArr} {L LI : List Nat}
    (hreg : ∀ k, regs.getD k (pId n) =
      (unpack n w (L.getD k (pidn n w)), unpack n w (LI.getD k (pidn n w))))
    (hc : ∀ k, canonK n w (mask w) (n * w) (L.getD k (pidn n w)) = true)
    (hci : ∀ k, canonK n w (mask w) (n * w) (LI.getD k (pidn n w)) = true)
    (hidc : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hid : idA n = unpack n w (pidn n w)) :
    ∀ wd, pWord n regs wd = (unpack n w (wordP1 n w L LI wd), unpack n w (wordP2 n w L LI wd)) ∧
      canonK n w (mask w) (n * w) (wordP1 n w L LI wd) = true ∧
      canonK n w (mask w) (n * w) (wordP2 n w L LI wd) = true
  | [] => by
    refine ⟨?_, hidc, hidc⟩
    rw [pWord, pId, hid]
    rfl
  | z :: wd => by
    obtain ⟨h1, h2, h3⟩ := pWord_unpack hreg hc hci hidc hid wd
    obtain ⟨c1, c2⟩ := letter_canon hc hci hidc z
    refine ⟨?_, canonK_pcomp c1 h2, canonK_pcomp h3 c2⟩
    rw [pWord, h1, letter_unpack hreg hid, pMul]
    simp only
    rw [compA_unpack c1 h2, compA_unpack h3 c2]
    rfl

section Build

variable {n : Nat} (xs : Array (Array Nat)) (pts : List Nat)

@[expose] def keyMulB (a b : Array Nat) : List Nat := pts.map fun p => a[b[p]!]!

theorem build_m : (InvTab.build n xs pts).m = xs.size := rfl

theorem build_xs : (InvTab.build n xs pts).xs = xs := rfl

theorem build_comm {i j : Nat} (hi : i < xs.size) (hj : j < xs.size) :
    ((InvTab.build n xs pts).comm[i]!)[j]! =
      (keyMulB pts xs[i]! xs[j]! == keyMulB pts xs[j]! xs[i]!) := by
  change ((Array.ofFn (n := xs.size) fun i : Fin xs.size => Array.ofFn (n := xs.size)
    fun j : Fin xs.size => keyMulB pts xs[i.val]! xs[j.val]! ==
      keyMulB pts xs[j.val]! xs[i.val]!)[i]!)[j]! = _
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem build_commAt {i j : Nat} (hi : i < xs.size) (hj : j < xs.size) :
    (InvTab.build n xs pts).commAt i j =
      (keyMulB pts xs[i]! xs[j]! == keyMulB pts xs[j]! xs[i]!) := by
  unfold InvTab.commAt
  rw [build_m, if_pos ⟨hi, hj⟩, build_comm xs pts hi hj]

theorem build_prodAt {i j : Nat} (hi : i < xs.size) (hj : j < xs.size) :
    (InvTab.build n xs pts).prodAt i j =
      if (keyMulB pts xs[i]! xs[j]! == keyMulB pts xs[j]! xs[i]!) = true then
        ((List.range xs.size).foldl (fun h i => h.insert (pts.map fun p => (xs[i]!)[p]!) i)
          ((∅ : Std.HashMap (List Nat) Nat).insert (pts.map fun p => (idA n)[p]!) xs.size)).getD
          (keyMulB pts xs[i]! xs[j]!) (xs.size + 1)
      else 0 := by
  unfold InvTab.prodAt
  rw [build_m, if_pos hi, if_pos hj]
  change ((Array.ofFn (n := xs.size) fun i : Fin xs.size => Array.ofFn (n := xs.size)
    fun j : Fin xs.size => if ((InvTab.build n xs pts).comm[i.val]!)[j.val]! = true then
      ((List.range xs.size).foldl (fun h i => h.insert (pts.map fun p => (xs[i]!)[p]!) i)
        ((∅ : Std.HashMap (List Nat) Nat).insert (pts.map fun p => (idA n)[p]!) xs.size)).getD
        (keyMulB pts xs[i.val]! xs[j.val]!) (xs.size + 1) else 0)[i]!)[j]! = _
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  simp only
  rw [build_comm xs pts hi hj]

theorem build_symOK {i j : Nat} (hi : i < xs.size) (hj : j < xs.size) :
    (InvTab.build n xs pts).symOK i j = true := by
  unfold InvTab.symOK
  rw [build_commAt xs pts hi hj, build_commAt xs pts hj hi, build_prodAt xs pts hi hj,
    build_prodAt xs pts hj hi]
  by_cases h : (keyMulB pts xs[i]! xs[j]! == keyMulB pts xs[j]! xs[i]!) = true
  · have e : keyMulB pts xs[i]! xs[j]! = keyMulB pts xs[j]! xs[i]! := beq_iff_eq.1 h
    have h' : (keyMulB pts xs[j]! xs[i]! == keyMulB pts xs[i]! xs[j]!) = true := by
      rw [e]; exact beq_self_eq_true _
    rw [if_pos h, if_pos h', h, h', e]
    simp
  · have h' : ¬ (keyMulB pts xs[j]! xs[i]! == keyMulB pts xs[i]! xs[j]!) = true := by
      intro h2
      exact h (by rw [beq_iff_eq] at h2 ⊢; exact h2.symm)
    rw [if_neg h, if_neg h', Bool.eq_false_iff.2 h, Bool.eq_false_iff.2 h']
    rfl

theorem build_ncAt {i j : Nat} (hi : i < xs.size) (hj : j < xs.size)
    (hc : (InvTab.build n xs pts).commAt i j = false) (hp : ∀ p ∈ pts, p < n) :
    ncAt n pts xs[i]! xs[j]! = true := by
  rw [build_commAt xs pts hi hj] at hc
  have hne : keyMulB pts xs[i]! xs[j]! ≠ keyMulB pts xs[j]! xs[i]! := by
    intro e
    rw [e, beq_self_eq_true] at hc
    exact Bool.noConfusion hc
  unfold ncAt
  rw [List.any_eq_true]
  by_contra hno
  apply hne
  unfold keyMulB
  apply List.map_congr_left
  intro p hpp
  by_contra hd
  exact hno ⟨p, hpp, by simp [hp p hpp, hd]⟩

end Build

theorem getD_foldl_insert_not {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (f : Nat → α)
    (k : α) (d : Nat) : ∀ (L : List Nat) (h0 : Std.HashMap α Nat), (∀ i ∈ L, f i ≠ k) →
    (L.foldl (fun h i => h.insert (f i) i) h0).getD k d = h0.getD k d
  | [], _, _ => rfl
  | i :: L, h0, hL => by
    rw [List.foldl_cons, getD_foldl_insert_not f k d L _ fun j hj => hL j (List.mem_cons_of_mem _ hj),
      Std.HashMap.getD_insert]
    have : (f i == k) = false := by
      rw [beq_eq_false_iff_ne]
      exact hL i List.mem_cons_self
    rw [this]
    rfl

theorem getD_foldl_insert {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (f : Nat → α)
    (d : Nat) : ∀ (L : List Nat) (h0 : Std.HashMap α Nat) (q : Nat), q ∈ L →
    (∀ i ∈ L, f i = f q → i = q) →
    (L.foldl (fun h i => h.insert (f i) i) h0).getD (f q) d = q
  | [], _, _, hq, _ => absurd hq List.not_mem_nil
  | i :: L, h0, q, hq, hL => by
    rw [List.foldl_cons]
    by_cases hqL : q ∈ L
    · exact getD_foldl_insert f d L _ q hqL fun j hj => hL j (List.mem_cons_of_mem _ hj)
    · have hiq : i = q := by
        rcases List.mem_cons.1 hq with h | h
        · exact h.symm
        · exact absurd h hqL
      subst hiq
      rw [getD_foldl_insert_not f (f i) d L _ fun j hj e => hqL (by
        rw [← hL j (List.mem_cons_of_mem _ hj) e]; exact hj), Std.HashMap.getD_insert]
      simp

end CFSG.KC.InvTabK

end
