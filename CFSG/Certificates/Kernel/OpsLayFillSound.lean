module

public import Certificates.Data.Kernel.OpsLayFill
public import Certificates.Data.Kernel.OpsRenL
public import CFSG.RankThree.PartOne.CTP.FusionDefs
public import CFSG.Certificates.Kernel.OpsLayKSnd
import CFSG.Certificates.Kernel.OpsLayFusSound
import CFSG.Certificates.Kernel.OpsRenLSound

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.RankThree.PartOne.CTP.Fus (Spec fusCheck)
open CFSG.KC.OpsLayK.Snd

theorem memB_iff {r : Nat} : ∀ {K : List Nat}, memB r K = true ↔ r ∈ K
  | [] => by simp [memB]
  | i :: K => by
    rw [memB, Bool.or_eq_true, memB_iff, List.mem_cons]
    exact or_congr_left ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl r⟩

theorem lookV_map (c : Lay) (f : Nat → Nat) {r : Nat} :
    ∀ {I : List Nat}, r ∈ I → lookV c r I (I.map f) = f r
  | i :: I, h => by
    simp only [List.map_cons, lookV]
    by_cases e : r = i
    · subst e
      simp [Nat.beq_refl]
    · have hb : Nat.beq r i = false := Bool.eq_false_iff.2 fun h => e (Nat.eq_of_beq_eq_true h)
      rw [hb]
      exact lookV_map c f (List.mem_of_ne_of_mem e h)

theorem fillR_agree (c : Lay) {n : Nat} {T : List Nat} (hT : T.length = n) {I : List Nat} :
    ∀ r ∈ I, getR c (fillR c n I (I.map (getR c T))) r = getR c T r := by
  intro r hr
  unfold getR
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hn : r < n
  · rw [fillR, List.getElem?_map, List.getElem?_range hn]
    simp only [Option.map_some, Option.getD_some]
    exact lookV_map c (getR c T) hr
  · rw [List.getElem?_eq_none (by simp [fillR]; omega), List.getElem?_eq_none (by omega)]

theorem evalWL_congr {c : Lay} {R R' : List Nat} {K : List Nat}
    (hK : ∀ r ∈ K, getR c R r = getR c R' r) :
    ∀ w : Word, wordIn K w = true → evalWL c R w = evalWL c R' w
  | [], _ => rfl
  | (r, e) :: w, h => by
    simp only [wordIn, List.all_cons, Bool.and_eq_true, memB_iff] at h
    simp only [evalWL, hK r h.1, evalWL_congr hK w (by simpa only [wordIn] using h.2)]

theorem factL_congr {c : Lay} {R R' : List Nat} {K : List Nat}
    (hK : ∀ r ∈ K, getR c R r = getR c R' r) (n : Nat) :
    ∀ f : MFact, factIn K f = true → factL c R n f = factL c R' n f
  | .ord r e, h => by
    simp only [factIn, memB_iff] at h
    simp only [factL, hK r h]
  | .conj g u w, h => by
    simp only [factIn, Bool.and_eq_true, memB_iff] at h
    simp only [factL, hK g h.1.1, evalWL_congr hK u h.1.2, evalWL_congr hK w h.2]
  | .ne u w t, h => by
    simp only [factIn, Bool.and_eq_true] at h
    simp only [factL, evalWL_congr hK u h.1, evalWL_congr hK w h.2]
  | .eq u w, h => by
    simp only [factIn, Bool.and_eq_true] at h
    simp only [factL, evalWL_congr hK u h.1, evalWL_congr hK w h.2]

theorem strictN_fill (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem evalWL_eq_evalOnto (c : Lay) (R : List Nat) :
    ∀ w : Word, evalWL c R w = evalOnto c R w c.ONE
  | [] => rfl
  | (r, e) :: w => by
    have ih := evalWL_eq_evalOnto c R w
    unfold evalOnto at ih ⊢
    rw [List.foldr_cons, strictN_fill, ← ih]
    rfl

theorem evalOnto_append (c : Lay) (R : List Nat) (u w : Word) (X : Nat) :
    evalOnto c R (u ++ w) X = evalOnto c R u (evalOnto c R w X) := by
  unfold evalOnto
  rw [List.foldr_append]

theorem factL_eq_of_segs {c : Lay} {R : List Nat} {n : Nat} {u w : Word} {k m : Nat}
    {W : Nat → Nat} (hok : (wordOK n u && wordOK n w) = true) (hlen : w.length ≤ m * k)
    (hlast : W m = c.ONE) (hs : ∀ i < m, wsegL c R w k i (W i) (W (i + 1)) = true)
    (h0 : Nat.beq (evalWL c R u) (W 0) = true) : factL c R n (.eq u w) = true := by
  have key : ∀ j ≤ m, evalOnto c R (w.drop ((m - j) * k)) c.ONE = W (m - j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le hlen, hlast]
      rfl
    | succ j ih =>
      intro hj
      have hi : m - (j + 1) + 1 = m - j := by omega
      have e : w.drop ((m - (j + 1)) * k) =
          (w.drop ((m - (j + 1)) * k)).take k ++ w.drop ((m - j) * k) := by
        rw [← hi, Nat.succ_mul, ← List.drop_drop, List.take_append_drop]
      rw [e, evalOnto_append, ih (by omega)]
      have := hs (m - (j + 1)) (by omega)
      unfold wsegL at this
      rw [hi] at this
      exact Nat.eq_of_beq_eq_true this
  have hw : evalWL c R w = W 0 := by
    rw [evalWL_eq_evalOnto]
    have := key m le_rfl
    rwa [Nat.sub_self, Nat.zero_mul, List.drop_zero] at this
  simp only [factL, Bool.and_eq_true] at hok ⊢
  exact ⟨hok, by rw [hw]; exact h0⟩

theorem fusRen_sound {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : Spec} (hw : D.wf = true) (hprog : progOK n prog = true) (hrA : D.rA < n)
    (hrB : D.rB < n) {outs : List Nat} {cs : List RChunk} {S : Nat → List Nat}
    (hren : renOK outs prog cs = true) (h0 : S 0 = [A, B])
    (hch : ∀ i < cs.length, chunkV c (cs.getD i (0, [], [])) (S i) (S (i + 1)) = true)
    (hin : (D.facts.all (factIn outs) && memB D.rA outs && memB D.rB outs) = true)
    (hf : ∀ j < D.facts.length,
      factL c (fillR c n outs (S cs.length)) n (D.facts.getD j default) = true)
    (he : seedRegsL c (fillR c n outs (S cs.length)) A B D.rA D.rB = true) :
    fusCheck (ops3 d) sA sB n prog D = true := by
  obtain ⟨h2, hlt⟩ := progOK_spec hprog
  have hS := renOK_sound (c := c) (A := A) (B := B) h2 hlt hren h0 hch
  have hT : (runL c prog (initR c A B n)).length = n := runL_initR_length c prog A B n
  have hag : ∀ r ∈ outs,
      getR c (runL c prog (initR c A B n)) r = getR c (fillR c n outs (S cs.length)) r := by
    intro r hr
    rw [← hS, fillR_agree c hT r hr]
  simp only [Bool.and_eq_true, List.all_eq_true, memB_iff] at hin
  obtain ⟨⟨hfin, hA'⟩, hB'⟩ := hin
  have hfacts : D.facts.all (factL c (runL c prog (initR c A B n)) n) = true := by
    rw [List.all_eq_true]
    intro f hfm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hfm
    rw [factL_congr hag n _ (hfin _ hfm)]
    have := hf j hj
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  have hseed : seedRegsL c (runL c prog (initR c A B n)) A B D.rA D.rB = true := by
    unfold seedRegsL at he ⊢
    rw [hag _ hA', hag _ hB']
    exact he
  exact fusCheck_of_seeds (seeds_of_runL (C := ⟨n, prog, D.facts⟩) hc hp hd hA hB hsA hsB hprog
    hrA hrB hfacts hseed) hw

end CFSG.KC.OpsLayK

end
