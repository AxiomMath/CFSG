module

public import CFSG.Sporadic.Th.Max3.RankInputs
public import Certificates.Data.Kernel.ThRank10508.Defs
public import CFSG.Certificates.Kernel.Th.Max3S.LeafFacts
public import CFSG.Certificates.Kernel.Th.Max3S.Words

public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec
open CFSG.Sporadic.Th.Max3.Rank

section Defs

variable (A B : Array V4)

@[expose] def rkRowsS (i : Fin 12) : Array V4 :=
  Native.mulRows (nfAt A B (rkK0 i)) (wordRows (x A B) (y A B) (rkWord i))

@[expose] def commListS (C : List (Fin 512)) (R : Array V4) : List (Fin 512) :=
  C.filter fun k => eqRows (Native.mulRows (nfAt A B k) R) (Native.mulRows R (nfAt A B k))

@[expose] def cqxListS : List (Fin 512) := commListS A B (List.finRange 512) (x A B)

@[expose] def rkDataS : RkData :=
  let C := cqxListS A B
  let R := Array.ofFn (rkRowsS A B)
  ⟨C, R, R.map (commListS A B C)⟩

@[expose] def RkFactsS (d : RkData) : Prop :=
  d.C.length = 16 ∧
    (∀ k ∈ d.C, ∀ l ∈ d.C,
      eqRows (Native.mulRows (nfAt A B k) (nfAt A B l))
        (Native.mulRows (nfAt A B l) (nfAt A B k)) = true) ∧
    (∀ i : Fin 12,
      eqRows (Native.mulRows d.R[i.val]! (x A B)) (Native.mulRows (x A B) d.R[i.val]!) = true) ∧
    (∀ i : Fin 12, d.D[i.val]!.length ≤ 8) ∧
    (∀ i : Fin 12, rkTypeB i = false → ∀ k ∈ d.C,
      eqRows (powRows (Native.mulRows (nfAt A B k) d.R[i.val]!) 2) idRows = false) ∧
    (∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
      rkPerm i * rkPerm j = rkPerm j * rkPerm i → rkPerm j ≠ rkPerm i →
      rkPerm j ≠ rkPerm i * aPerm →
      (d.D[i.val]!.filter fun k => decide (k ∈ d.D[j.val]!)).length ≤ 4)

end Defs

open CFSG.KC.ThRk10508

@[expose] noncomputable def rkC0 (Cl : List ℕ) : List (Fin 512) :=
  (List.finRange 512).filter fun k => memL Cl k.val

@[expose] noncomputable def rkD0 (Cl : List ℕ) (Ds : List (List ℕ)) (i : Fin 12) : List (Fin 512) :=
  (rkC0 Cl).filter fun k => memL (getL Ds i.val) k.val

theorem andB_true {a b : Bool} (h : CFSG.KC.Th.andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem eqBB_eq {a b : Bool} (h : eqBB a b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

theorem ne_of_notB {a b : ℕ} (h : BigS.notB (Nat.beq a b) = true) : a ≠ b := by
  rintro rfl
  rw [Nat.beq_refl] at h
  exact absurd h (by decide)

theorem memL_iff (Ls : List ℕ) (k : ℕ) : memL Ls k = true ↔ k ∈ Ls := by
  induction Ls with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | cons a t ih =>
    have e : memL (a :: t) k = Bool.rec (memL t k) true (Nat.beq a k) := rfl
    rw [e, List.mem_cons]
    cases h : Nat.beq a k
    · have hne : a ≠ k := Nat.ne_of_beq_eq_false h
      rw [ih]
      exact ⟨Or.inr, fun h' => h'.resolve_left fun e => hne e.symm⟩
    · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h).symm, fun _ => rfl⟩

theorem allL_sound {f : ℕ → Bool} : ∀ {Ls : List ℕ}, allL f Ls = true → ∀ a ∈ Ls, f a = true
  | [], _, _, ha => absurd ha List.not_mem_nil
  | b :: t, h, a, ha => by
    have h' := andB_true (b := allL f t) h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h'.1
    · exact allL_sound h'.2 a ha

theorem allN_sound {f : ℕ → Bool} {lo : ℕ} : ∀ {n : ℕ}, allN f lo n = true →
    ∀ j < n, f (lo + j) = true
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, j, hj => by
    have h' := andB_true (a := f (Nat.add lo n)) (b := allN f lo n) h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact allN_sound h'.2 j hj
    · exact h'.1

theorem getN_mem : ∀ (Ns : List ℕ) (j : ℕ), j < Ns.length → getN Ns j ∈ Ns
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | a :: _, 0, _ => List.mem_cons_self
  | _ :: t, j + 1, hj => List.mem_cons_of_mem _ (getN_mem t j (by simpa using hj))

theorem forall_mem_of_getN {f : ℕ → Bool} (Ns : List ℕ)
    (h : ∀ j < Ns.length, f (getN Ns j) = true) : ∀ a ∈ Ns, f a = true := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have e : ∀ (Ms : List ℕ) (i : ℕ) (hi : i < Ms.length), getN Ms i = Ms[i] := by
    intro Ms
    induction Ms with
    | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | cons b t ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)
  rw [← e Ns j hj]
  exact h j hj

theorem cqK_of_chunks {RB : ℕ → ℕ} {c rm : ℕ} {Cl : List ℕ}
    (h : ∀ g < 8, cqChunk RB c rm Cl g = true) : ∀ k < 512, cqK RB c rm Cl k = true := by
  intro k hk
  have := allN_sound (h (k / 64) (by omega)) (k % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.mul 64 (k / 64) + k % 64 = k := Nat.div_add_mod k 64
  rwa [e] at this

theorem ofFn_getElem! {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Array.ofFn f)[i.val]! = f i := by
  rw [getElem!_pos (Array.ofFn f) i.val (by simp)]
  simp

theorem map_ofFn_getElem! {α β : Type} [Inhabited β] {n : ℕ} (g : α → β) (f : Fin n → α)
    (i : Fin n) : ((Array.ofFn f).map g)[i.val]! = g (f i) := by
  rw [getElem!_pos ((Array.ofFn f).map g) i.val (by simp)]
  simp

section Sound

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem comB_eq (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {P Q : ℕ} {X Y : Array V4} (hX : WfRows X) (hY : WfRows Y) (hP : pkMat P = rowsMatrix X)
    (hQ : pkMat Q = rowsMatrix Y) : comB c rm P Q = eqRows (Native.mulRows X Y) (Native.mulRows Y X) := by
  have h1 : pkMat (CFSG.KC.Th.mulB c rm P Q) = rowsMatrix (Native.mulRows X Y) := by
    rw [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  have h2 : pkMat (CFSG.KC.Th.mulB c rm Q P) = rowsMatrix (Native.mulRows Y X) := by
    rw [pkMat_mulB hk, hP, hQ, rowsMatrix_mulRows]
  unfold comB
  cases h : Nat.beq (CFSG.KC.Th.mulB c rm P Q) (CFSG.KC.Th.mulB c rm Q P)
  · exact (eqRows_false_of_pk (inLayout_mulB hk _ _) (inLayout_mulB hk _ _) h1 h2
      (Nat.ne_of_beq_eq_false h)).symm
  · exact (eqRows_true_of_pk (wfRows_mulRows hX hY) (wfRows_mulRows hY hX) h1 h2
      (Nat.eq_of_beq_eq_true h)).symm

end Sound

variable {A B : Array V4}

theorem wf_rkRowsS (hA : WfRows A) (hB : WfRows B) (i : Fin 12) : WfRows (rkRowsS A B i) :=
  wfRows_mulRows (wf_nfAt hA hB _) (wfRows_wordRows (wf_x hA hB) (wf_y hA hB) _)

theorem rkFacts_of (D : CFSG.KC.Th.Gen.Max3Data) (h : CFSG.KC.Th.Gen.max3Chk D = true)
    (hR : RegOK D A B) (hA : WfRows A) (hB : WfRows B)
    (L : ℕ → ℕ) (Ks Es Ws Cl Ts : List ℕ) (Ds : List (List ℕ))
    (hcq : ∀ g < 8, cqChunk D.ThM3_RB D.ThS_c D.ThS_rm Cl g = true)
    (hcc : ∀ j < Cl.length, ccK D.ThM3_RB D.ThS_c D.ThS_rm Cl (getN Cl j) = true)
    (hrow : ∀ i : Fin 12,
      rowI D.ThM3_RB D.ThS_c D.ThS_rm D.ThS_ONE L Ks Es Ws Cl Ds Ts i.val = true)
    (hKs : ∀ i : Fin 12, getN Ks i.val = (rkK0 i).val)
    (hEs : ∀ i : Fin 12, getN Es i.val = encGen (rkWord i))
    (hWs : ∀ i : Fin 12, getN Ws i.val = (rkWord i).length)
    (hTs : ∀ i : Fin 12, rkTypeB i = false → memL Ts i.val = false)
    (h16 : (rkC0 Cl).length = 16)
    (h8 : ∀ i : Fin 12, (rkD0 Cl Ds i).length ≤ 8)
    (h4 : ∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
      rkPerm i * rkPerm j = rkPerm j * rkPerm i → rkPerm j ≠ rkPerm i →
      rkPerm j ≠ rkPerm i * aPerm →
      ((rkD0 Cl Ds i).filter fun k => decide (k ∈ rkD0 Cl Ds j)).length ≤ 4) :
    RkFactsS A B (rkDataS A B) := by
  have hk := consts_leaf h
  have hX : WfRows (x A B) := wf_x hA hB
  have hnf : ∀ k : Fin 512, pkMat (D.ThM3_RB (25 + k.val)) = rowsMatrix (nfAt A B k) := hR.nf
  have hcq' := cqK_of_chunks hcq
  have hC : cqxListS A B = rkC0 Cl := by
    unfold cqxListS commListS rkC0
    refine List.filter_congr fun k _ => ?_
    have e := eqBB_eq (hcq' k.val k.isLt)
    rwa [comB_eq hk (wf_nfAt hA hB k) hX (hnf k) hR.x] at e
  have memC : ∀ k : Fin 512, k ∈ rkC0 Cl → k.val ∈ Cl := fun k hk' =>
    (memL_iff Cl k.val).1 (by simpa using (List.mem_filter.1 hk').2)
  have hrow' : ∀ i : Fin 12, _ := fun i => andB_true (hrow i)
  have hL : ∀ i : Fin 12, pkMat (L i.val) = rowsMatrix (rkRowsS A B i) := by
    intro i
    have e := Nat.eq_of_beq_eq_true (hrow' i).1
    rw [e, hKs, hEs, hWs, pkMat_mulB hk, hnf, pkMat_wordAB_encGen hk hR.x hR.y,
      rkRowsS, rowsMatrix_mulRows]
  have hR' : ∀ i : Fin 12, (rkDataS A B).R[i.val]! = rkRowsS A B i := fun i => ofFn_getElem! _ i
  have hD : ∀ i : Fin 12, (rkDataS A B).D[i.val]! = rkD0 Cl Ds i := by
    intro i
    have e : (rkDataS A B).D[i.val]! = commListS A B (cqxListS A B) (rkRowsS A B i) :=
      map_ofFn_getElem! _ _ i
    rw [e, hC]
    unfold commListS rkD0
    refine List.filter_congr fun k hkC => ?_
    have h3 := (andB_true (andB_true (hrow' i).2).2).1
    have e2 := eqBB_eq (allL_sound h3 k.val (memC k hkC))
    rwa [comB_eq hk (wf_nfAt hA hB k) (wf_rkRowsS hA hB i) (hnf k) (hL i)] at e2
  have hdC : (rkDataS A B).C = rkC0 Cl := by
    rw [← hC]
    simp only [rkDataS]
  unfold RkFactsS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdC, h16]
  · intro k hkC l hlC
    rw [hdC] at hkC hlC
    have h2 := forall_mem_of_getN Cl hcc k.val (memC k hkC)
    have e := allL_sound h2 l.val (memC l hlC)
    rwa [comB_eq hk (wf_nfAt hA hB k) (wf_nfAt hA hB l) (hnf k) (hnf l)] at e
  · intro i
    rw [hR' i]
    have e := (andB_true (hrow' i).2).1
    rwa [comB_eq hk (wf_rkRowsS hA hB i) hX (hL i) hR.x] at e
  · intro i
    rw [hD i]
    exact h8 i
  · intro i hi k hkC
    rw [hdC] at hkC
    rw [hR' i]
    have h4' := (andB_true (andB_true (hrow' i).2).2).2
    rw [hTs i hi] at h4'
    have e := ne_of_notB (allL_sound h4' k.val (memC k hkC))
    refine eqRows_false_of_pk (inLayout_powB hk _ _ _) (inLayout_one hk) ?_ ?_ e
    · rw [pkMat_powB hk _ _ _ (by norm_num), pkMat_mulB hk, hnf, hL, rowsMatrix_powRows,
        rowsMatrix_mulRows]
    · rw [pkMat_one hk, rowsMatrix_idRows]
  · intro i j hi hj hc hne hne'
    rw [hD i, hD j]
    exact h4 i j hi hj hc hne hne'

end CFSG.KC.Th.Max3S

end
