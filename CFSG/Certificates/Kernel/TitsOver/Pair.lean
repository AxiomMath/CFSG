module

public import CFSG.Certificates.Kernel.TitsOver.Base
public import CFSG.Certificates.Kernel.TitsOver.Cover
public import CFSG.LocalAnalysis.StandardType.TitsOvergroupPairSound
public import CFSG.Quasithin.Vol2.KGFactC31ArrChain

public section

namespace CFSG.KS.TitsOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.KS.MaxD2 CFSG.StandardType.TitsOvergroup CFSG.ComponentClassification.PSL3Four
open CFSG.AGLEmbedding.FusD2
open CFSG.Sporadic.Schreier (BaseFaithful)
open Certificates.MaxD2Perm (fpTab fpOK)

theorem tabRep_invTab {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) :
    TabRep (invTab n t) g⁻¹ := by
  have h := CFSG.Quasithin.KGC31.rep_invCand_of_rep (n := n) ht.2
  refine ⟨?_, ?_⟩
  · change (CFSG.Monster.B.Co2.Native.invCand n t).size = n
    rw [CFSG.Quasithin.KGC31.invCand_eq_foldl']
    have key : ∀ (l : List ℕ) (r : Array ℕ),
        (l.foldl (fun r i => r.set! t[i]! i) r).size = r.size := by
      intro l
      induction l with
      | nil => intro r; rfl
      | cons a l ih => intro r; rw [List.foldl_cons, ih]; simp
    rw [key]
    simp
  · exact h

theorem invsOK_invTab {n : ℕ} {A : Array Tab} {L : List (Equiv.Perm (Fin n))}
    (h : ∀ j, TabRep (A.getD j (idTab n)) (L.getD j 1)) :
    invsOK n A (A.map (invTab n)) = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq, Array.size_map, true_and]
  rw [allBelow_iff']
  intro k hk
  have hk' := h k
  rw [show A.getD k (idTab n) = A[k]! by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk, Option.getD_some,
      getElem!_pos A k hk]] at hk'
  have hi := tabRep_invTab hk'
  rw [getElem!_pos (A.map (invTab n)) k (by simpa using hk), Array.getElem_map,
    ← getElem!_pos A k hk]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hi.1, ?_⟩
  exact (hi.comp hk').tab_eq (by rw [inv_mul_cancel]; exact TabRep.idTab)

variable {D : PairData}

section

variable {w kG : Nat} {Gp GIp : Nat → Nat}

theorem wT_bindT (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    {wd : List Int} {r : Nat} (h : wordEqK D.n w (mask w) (pidn D.n w) Gp GIp kG wd r = true) :
    wT D wd = unpack D.n w r := by
  unfold wT giT
  exact wordT_u ⟨hGs, hGb⟩ hGp h

theorem gens_bindT (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    {ws : List (List Int)} {k : Nat} {G : Nat → Nat} (hk : ws.length = k)
    (h : ∀ j < k, wordEqK D.n w (mask w) (pidn D.n w) Gp GIp kG (ws[j]!) (G j) = true ∧
      Cn D.n w (G j)) :
    GensOK D.n w k G (ws.map (wT D)).toArray := by
  refine ⟨by simp [hk], fun j hj => ⟨?_, (h j hj).2⟩⟩
  rw [map_get _ (by rw [hk]; exact hj), wT_bindT hGs hGb hGp (h j hj).1]

theorem inH_of_wordT {S : List (Equiv.Perm (Fin D.n))} (hS : Sound D S)
    (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    {wd : List Int} {r : Nat} (h : wordEqK D.n w (mask w) (pidn D.n w) Gp GIp kG wd r = true)
    (hr : Cn D.n w r) : InH (pairG D S) w r := by
  refine ⟨hr, wordVal S wd,
    wordVal_mem S (pairG D S) (fun _ hg => Subgroup.subset_closure hg) wd, ?_⟩
  rw [← wT_bindT hGs hGb hGp h]
  exact wordT_rep S D.gT (giT D) hS.rep hS.gi wd

theorem checkInv_ofT (hGs : D.gT.size = kG) (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true) :
    checkInv D = true := by
  unfold checkInv
  rw [allBelow_iff']
  intro j hj
  have hj' : j < kG := by rw [← hGs]; exact hj
  have hp := (PK.allN_iff.1 hGp) j hj'
  have hgi : (giT D)[j]! = unpack D.n w (GIp j) := by
    unfold giT
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, ← getElem!_pos D.gT j hj,
      hGb j hj', inv_u hp]
  rw [hgi, hGb j hj', inv_comp hp]
  simp [size_u]

end

section

variable {w cnt : Nat} {T PL : Nat → Nat}

theorem checkP_ofT
    (hE : enumBFS D.n (pGens D) D.pOrder = penumRec D.n w cnt T PL ∧
      enumOK D.n (pGens D) (penumRec D.n w cnt T PL) = true) (hc : cnt = D.pOrder) :
    checkP D = true := by
  unfold checkP pEnum
  rw [hE.1, hE.2, rec_size, hc]
  simp

theorem checkN_ofT
    (hE : enumBFS D.n (nGens D) D.nOrder = penumRec D.n w cnt T PL ∧
      enumOK D.n (nGens D) (penumRec D.n w cnt T PL) = true) (hc : cnt = D.nOrder) :
    checkN D = true := by
  unfold checkN nEnum
  rw [hE.1, hE.2, rec_size, hc]
  simp

end

theorem checkSide_ofT {w : Nat} {scnt : Nat → Nat} {ST SPL : Nat → Nat → Nat}
    (hl : D.sideOrder.length = D.sideW.length)
    (hE : ∀ k < D.sideW.length,
      enumBFS D.n (sideGens D k) (D.sideOrder.getD k 0) = penumRec D.n w (scnt k) (ST k) (SPL k) ∧
      enumOK D.n (sideGens D k) (penumRec D.n w (scnt k) (ST k) (SPL k)) = true ∧
      scnt k = D.sideOrder.getD k 0) :
    checkSide D = true := by
  unfold checkSide
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hl, allBelow_iff'.2 fun k hk => ?_⟩
  obtain ⟨e, hok, hc⟩ := hE k hk
  unfold sideEnum
  rw [e, hok, rec_size, hc]
  simp

theorem found_recT {n w cnt X : Nat} {T PL : Nat → Nat} (hT : ∀ i < cnt, Cn n w (T i))
    (hX : Cn n w X) :
    found (indexOf (penumRec n w cnt T PL).tabs) (penumRec n w cnt T PL).tabs (unpack n w X) =
      true ↔ ∃ i < cnt, T i = X := by
  rw [found_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    exact ⟨i, hi, u_inj (hT i hi) hX e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [rec_size]; exact hi, rec_get hi⟩

theorem checkNormal_ofT {w kP kN pcnt : Nat} {PG NG NGI PT PPL : Nat → Nat}
    (hn : szOK D.n w = true)
    (hEP : pEnum D = penumRec D.n w pcnt PT PPL) (hPc : ∀ i < pcnt, Cn D.n w (PT i))
    (hgP : GensOK D.n w kP PG (pGens D)) (hgN : GensOK D.n w kN NG (nGens D))
    (hNI : ∀ j < kN, permOK D.n w (mask w) (D.n * w) (NG j) (NGI j) = true)
    (hNorm : ∀ j < kN, ∀ i < kP,
      (∃ h, conjInK D.n w pcnt PT (NG j) (NGI j) (PG i) h = true) ∧
      (∃ h, conjInK D.n w pcnt PT (NGI j) (NG j) (PG i) h = true)) :
    checkNormal D = true := by
  have hs : (nGens D).size = kN := hgN.1
  have hsi : (nGensI D).size = kN := by simp [nGensI, hs]
  have hngi : ∀ j < kN, (nGensI D)[j]! = unpack D.n w (NGI j) := fun j hj => by
    unfold nGensI
    rw [getElem!_pos _ j (by simpa [hs] using hj), Array.getElem_map,
      ← getElem!_pos (nGens D) j (by rw [hs]; exact hj), (hgN.2 j hj).1, inv_u (hNI j hj)]
  have hspec : ∀ {g gi x h : Nat}, Cn D.n w g → Cn D.n w gi → Cn D.n w x →
      conjInK D.n w pcnt PT g gi x h = true →
      found (indexOf (penumRec D.n w pcnt PT PPL).tabs) (penumRec D.n w pcnt PT PPL).tabs
        (conjTab D.n (unpack D.n w g) (unpack D.n w gi) (unpack D.n w x)) = true := by
    intro g gi x h hg hgi hx hk
    unfold conjTab
    rw [comp_u hg hx, comp_u (cc hg hx) hgi, found_recT hPc (cc (cc hg hx) hgi)]
    unfold conjInK at hk
    obtain ⟨h1, h2⟩ := band_e hk
    exact ⟨h, Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
  unfold checkNormal normalOK
  rw [hEP]
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold invsOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [hs, hsi], allBelow_iff'.2 fun j hj => ?_⟩
    rw [hs] at hj
    rw [hngi j hj, (hgN.2 j hj).1, inv_comp (hNI j hj)]
    simp [size_u]
  · rw [allBelow_iff']
    intro j hj
    rw [hs] at hj
    rw [allBelow_iff']
    intro i hi
    rw [hgP.1] at hi
    rw [(hgN.2 j hj).1, hngi j hj, (hgP.2 i hi).1]
    have hc := perm_canon (hNI j hj) hn
    have hx := (hgP.2 i hi).2
    obtain ⟨⟨h1, e1⟩, ⟨h2, e2⟩⟩ := hNorm j hj i hi
    simp only [Bool.and_eq_true]
    exact ⟨hspec hc.1 hc.2 hx e1, hspec hc.2 hc.1 hx e2⟩

section

variable {w kG nr : Nat} {Gp GIp REP REPI : Nat → Nat}

theorem repT_bindT (hn : szOK D.n w = true) (hGs : D.gT.size = kG)
    (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    (hnr : nr = D.repW.length + 1) (hR0 : REP 0 = pidn D.n w)
    (hRw : ∀ i < D.repW.length,
      wordEqK D.n w (mask w) (pidn D.n w) Gp GIp kG (D.repW[i]!) (REP (i + 1)) = true) :
    RepB D.n w nr REP (repT D) := by
  have e : repT D = (idTab D.n :: D.repW.map (wT D)).toArray := by simp [repT]
  refine ⟨by simp [repT, hnr], fun i hi => ?_⟩
  rw [e, getElem!_pos _ i (by simp; omega)]
  rcases i with _ | j
  · simp [hR0, id_u hn]
  · have hj : j < D.repW.length := by omega
    simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_map]
    rw [← getElem!_pos D.repW j hj]
    exact wT_bindT hGs hGb hGp (hRw j hj)

theorem repI_bindT (hr : RepB D.n w nr REP (repT D))
    (hRi : ∀ i < nr, permOK D.n w (mask w) (D.n * w) (REP i) (REPI i) = true) :
    RepB D.n w nr REPI (repI D) := by
  refine ⟨by simp [repI, hr.1], fun i hi => ?_⟩
  unfold repI
  rw [getElem!_pos _ i (by simpa [hr.1] using hi), Array.getElem_map,
    ← getElem!_pos (repT D) i (by rw [hr.1]; exact hi), hr.2 i hi, inv_u (hRi i hi)]

end

theorem checkCover_ofT {C : Pk} (H : HypsC C D.fpPts D.nOrder D.gOrder) (hCn : C.n = D.n)
    (hEN : nEnum D = penumRec C.n C.w C.cnt C.NT C.NPL)
    (hr : RepB C.n C.w C.nr C.REP (repT D)) (hri : RepB C.n C.w C.nr C.REPI (repI D))
    (hpts : ∀ x ∈ D.fpPts, x < D.n) :
    checkCover D = true := by
  have h := checkCover_ofC H hr hri (by rw [hCn]; exact hpts)
  unfold checkCover
  dsimp only
  rw [hEN, ← hCn]
  exact h

theorem getD_eq_get {α : Type*} [Inhabited α] {A : Array α} {d : α} {l : Nat} (h : l < A.size) :
    A.getD l d = A[l]! := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some,
    getElem!_pos A l h]

structure PairB (D : PairData) (w nr : Nat) (P PI REP REPI : Nat → Nat) : Prop where
  hn : szOK D.n w = true
  hP2 : D.pW.length = 2
  hgP : ∀ l < 2, (pGens D)[l]! = unpack D.n w (P l) ∧
    permOK D.n w (mask w) (D.n * w) (P l) (PI l) = true
  hr : RepB D.n w nr REP (repT D)
  hri : RepB D.n w nr REPI (repI D)
  hRi : ∀ i < nr, permOK D.n w (mask w) (D.n * w) (REP i) (REPI i) = true
  hnr : nr = D.repW.length + 1

section

variable {S : List (Equiv.Perm (Fin D.n))} {w nr : Nat} {P PI REP REPI : Nat → Nat}

theorem PairB.invs (hb : PairB D w nr P PI REP REPI) : invsOK D.n (repT D) (repI D) = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [hb.hri.1, hb.hr.1], allBelow_iff'.2 fun k hk => ?_⟩
  rw [hb.hr.1] at hk
  rw [hb.hri.2 k hk, hb.hr.2 k hk, inv_comp (hb.hRi k hk)]
  simp [size_u]

theorem rep_getT (hS : Sound D S) {i : Nat} (hi : i < D.repW.length) :
    TabRep ((repT D)[i + 1]!) ((pairReps D S).getD (i + 1) 1) := by
  have h1 := repT_rep hS (i + 1)
  rwa [getD_eq_get (by simp [repT]; omega)] at h1

theorem repi_getT (hS : Sound D S) (hinvs : invsOK D.n (repT D) (repI D) = true) {i : Nat}
    (hi : i < D.repW.length) :
    TabRep ((repI D)[i + 1]!) ((pairReps D S).getD (i + 1) 1)⁻¹ := by
  have h1 := repI_rep hS hinvs (i + 1)
  rwa [getD_eq_get (by simp [repI, repT]; omega)] at h1

theorem pairLetter_eval (hS : Sound D S) (hb : PairB D w nr P PI REP REPI) {i : Nat}
    (hi : i < D.repW.length) :
    (∀ l < 4, ∀ y < D.n, pairLf w (mask w) (P 0) (P 1) (REP (i + 1)) (REPI (i + 1)) l y =
      ((pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).getD l (idTab D.n))[y]!) ∧
    (∀ l < 4, ∀ y < D.n, pairLf w (mask w) (PI 0) (PI 1) (REP (i + 1)) (REPI (i + 1)) l y =
      (((pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).map (invTab D.n)).getD l
        (idTab D.n))[y]!) := by
  have hn := hb.hn
  have hps : (pGens D).size = 2 := by simp [pGens, hb.hP2]
  have hal : (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).size = 4 := by
    simp [pairLetters, hps]
  have hi1 : i + 1 < nr := by rw [hb.hnr]; omega
  have hg := hb.hr.2 (i + 1) hi1
  have hgi := hb.hri.2 (i + 1) hi1
  have hgc := perm_canon (hb.hRi (i + 1) hi1) hn
  have hP : ∀ l < 2, Cn D.n w (P l) ∧ Cn D.n w (PI l) := fun l hl => perm_canon (hb.hgP l hl).2 hn
  have hL : ∀ l < 2, (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).getD l (idTab D.n) =
      unpack D.n w (P l) := fun l hl => by
    rw [pairLetters, getD_append_left _ _ _ (by rw [hps]; exact hl), getD_eq_get (by rw [hps]; exact hl),
      (hb.hgP l hl).1]
  have hLc : ∀ l < 2, (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).getD (l + 2) (idTab D.n) =
      conjTab D.n (unpack D.n w (REP (i + 1))) (unpack D.n w (REPI (i + 1))) (unpack D.n w (P l)) :=
    fun l hl => by
      rw [pairLetters, getD_append_right _ _ _ (by rw [hps]; omega), hps,
        show l + 2 - 2 = l by omega, getD_map_array _ _ _ (by rw [hps]; exact hl),
        getD_eq_get (by rw [hps]; exact hl), (hb.hgP l hl).1, hg, hgi]
  have hconj : ∀ {a : Nat}, Cn D.n w a → ∀ y < D.n,
      (conjTab D.n (unpack D.n w (REP (i + 1))) (unpack D.n w (REPI (i + 1))) (unpack D.n w a))[y]! =
        pg w (mask w) (REP (i + 1)) (pg w (mask w) a (pg w (mask w) (REPI (i + 1)) y)) := by
    intro a ha y hy
    unfold conjTab
    rw [comp_u hgc.1 ha, comp_u (cc hgc.1 ha) hgc.2, get_u hy, pg_pc hn hy,
      pg_pc hn (canon_lt hgc.2 hy)]
  refine ⟨fun l hl y hy => ?_, fun l hl y hy => ?_⟩
  · rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    · rw [hL 0 (by decide), get_u hy]
      rfl
    · rw [hL 1 (by decide), get_u hy]
      rfl
    · rw [hLc 0 (by decide), hconj (hP 0 (by decide)).1 y hy]
      rfl
    · rw [hLc 1 (by decide), hconj (hP 1 (by decide)).1 y hy]
      rfl
  · have hinvs := hb.invs
    have tg := rep_getT hS hi
    have tgi := repi_getT hS hinvs hi
    rw [hg] at tg
    rw [hgi] at tgi
    have tp : ∀ l < 2, TabRep (unpack D.n w (P l)) ((D.pW.map (wordVal S)).getD l 1) :=
      fun l hl => by
        have := pGens_rep hS l
        rwa [getD_eq_get (by rw [hps]; exact hl), (hb.hgP l hl).1] at this
    have tpi : ∀ l < 2, TabRep (unpack D.n w (PI l)) ((D.pW.map (wordVal S)).getD l 1)⁻¹ :=
      fun l hl => by
        rw [← inv_u (hb.hgP l hl).2]
        exact tabRep_invTab (tp l hl)
    have hLi : ∀ l < 2, invTab D.n (conjTab D.n (unpack D.n w (REP (i + 1)))
        (unpack D.n w (REPI (i + 1))) (unpack D.n w (P l))) =
        conjTab D.n (unpack D.n w (REP (i + 1))) (unpack D.n w (REPI (i + 1)))
          (unpack D.n w (PI l)) := fun l hl => by
      refine (tabRep_invTab (tg.conjTab (tp l hl) tgi)).tab_eq ?_
      have e := tg.conjTab (tpi l hl) tgi
      rwa [show ((pairReps D S).getD (i + 1) 1 * ((D.pW.map (wordVal S)).getD l 1) *
          ((pairReps D S).getD (i + 1) 1)⁻¹)⁻¹ = (pairReps D S).getD (i + 1) 1 *
          ((D.pW.map (wordVal S)).getD l 1)⁻¹ * ((pairReps D S).getD (i + 1) 1)⁻¹ by group]
    rw [getD_map_array _ _ _ (by rw [hal]; exact hl)]
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    · rw [hL 0 (by decide), inv_u (hb.hgP 0 (by decide)).2, get_u hy]
      rfl
    · rw [hL 1 (by decide), inv_u (hb.hgP 1 (by decide)).2, get_u hy]
      rfl
    · rw [hLc 0 (by decide), hLi 0 (by decide), hconj (hP 0 (by decide)).2 y hy]
      rfl
    · rw [hLc 1 (by decide), hLi 1 (by decide), hconj (hP 1 (by decide)).2 y hy]
      rfl

theorem pairLetterVals_mem {i : Nat} (hi : i < D.repW.length) :
    ∀ x ∈ pairLetterVals D S ((pairReps D S).getD (i + 1) 1), x ∈ pairG D S := by
  have hg : (pairReps D S).getD (i + 1) 1 ∈ pairG D S := by
    apply pairReps_mem
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [pairReps]; omega),
      Option.getD_some]
    exact List.getElem_mem _
  have hw : ∀ x ∈ pairPVals D S, x ∈ pairG D S := by
    intro x hx
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hx
    exact wordVal_mem S (pairG D S) (fun _ hg => Subgroup.subset_closure hg) wd
  intro x hx
  rw [pairLetterVals] at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hw x hx
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (pairG D S).mul_mem ((pairG D S).mul_mem hg (hw y hy)) ((pairG D S).inv_mem hg)

theorem gT_repT (hS : Sound D S) {j : Nat} (hj : j < D.gT.size) :
    TabRep (D.gT[j]!) (S.getD j 1) ∧ S.getD j 1 ∈ pairG D S := by
  refine ⟨by have := hS.rep j; rwa [getD_eq_get hj] at this, ?_⟩
  apply Subgroup.subset_closure
  change S.getD j 1 ∈ S
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hS.len]; exact hj),
    Option.getD_some]
  exact List.getElem_mem _

theorem checkGen_ofT (hS : Sound D S) {bs : List Nat} {nb : Nat} {B : Nat → Nat}
    (hF : BaseFaithful (pairG D S) bs) (hB : BaseOK D.n nb B bs) (hb : PairB D w nr P PI REP REPI)
    {kG : Nat} {Gp : Nat → Nat} (hGs : D.gT.size = kG)
    (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hlen : D.kind.length = D.repW.length) (hglen : D.genW.length = D.repW.length)
    (hK : ∀ i < D.repW.length, D.kind[i]! = 0 → (D.genW[i]!).length = kG ∧ ∀ j < kG,
      wordBK 4 nb B (pairLf w (mask w) (P 0) (P 1) (REP (i + 1)) (REPI (i + 1)))
        (pairLf w (mask w) (PI 0) (PI 1) (REP (i + 1)) (REPI (i + 1))) ((D.genW[i]!)[j]!)
        (pg w (mask w) (Gp j)) = true) :
    checkGen D = true := by
  unfold checkGen
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hlen, hglen⟩, allBelow_iff'.2 fun i hi => ?_⟩
  rw [Bool.or_eq_true]
  by_cases hk : D.kind[i]! = 0
  · right
    obtain ⟨hl, hw⟩ := hK i hi hk
    have hinvs := hb.invs
    have hAl := pairLetters_rep hS hinvs hi
    have hInv := invsOK_invTab hAl
    have hAli := pairLetters_inv_rep hS hinvs hi hInv
    have hev := pairLetter_eval hS hb hi
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨hl.trans hGs.symm, hInv, allBelow_iff'.2 fun j hj => ?_⟩
    have hj' : j < kG := by rw [← hGs]; exact hj
    obtain ⟨ht, hgm⟩ := gT_repT hS hj
    rw [beq_iff_eq]
    exact wordBK_sound hF hB hAl hAli hev.1 hev.2 (pairLetterVals_mem hi) ht hgm
      (fun s hs => by rw [hGb j hj', get_u (hB.1 s hs)]) (hw j hj')
  · left
    simpa using hk

theorem getD_mem_listT {α : Type*} {L : List α} {d : α} {j : Nat} (h : j < L.length) :
    L.getD j d ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem _

theorem checkSideGen_ofT (hS : Sound D S) {bs : List Nat} {nb : Nat} {B : Nat → Nat}
    (hF : BaseFaithful (pairG D S) bs) (hB : BaseOK D.n nb B bs) (hb : PairB D w nr P PI REP REPI)
    {SG : Nat → Nat → Nat}
    (hSG : ∀ k < D.sideW.length, ∀ j < (sideGens D k).size,
      (sideGens D k)[j]! = unpack D.n w (SG k j))
    {sg : List (List (List Int))} (hsgl : sg.length = D.repW.length)
    (hK : ∀ i < D.repW.length, D.kind[i]! ≠ 0 → D.kind[i]! - 1 < D.sideW.length ∧
      (sg[i]!).length = (sideGens D (D.kind[i]! - 1)).size ∧
      ∀ j < (sideGens D (D.kind[i]! - 1)).size,
        wordBK 4 nb B (pairLf w (mask w) (P 0) (P 1) (REP (i + 1)) (REPI (i + 1)))
          (pairLf w (mask w) (PI 0) (PI 1) (REP (i + 1)) (REPI (i + 1))) ((sg[i]!)[j]!)
          (pg w (mask w) (SG (D.kind[i]! - 1) j)) = true) :
    checkSideGen D sg = true := by
  unfold checkSideGen
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hsgl, allBelow_iff'.2 fun i hi => ?_⟩
  rw [Bool.or_eq_true]
  by_cases hk : D.kind[i]! = 0
  · left
    simpa using hk
  · right
    obtain ⟨hkl, hl, hw⟩ := hK i hi hk
    have hinvs := hb.invs
    have hAl := pairLetters_rep hS hinvs hi
    have hInv := invsOK_invTab hAl
    have hAli := pairLetters_inv_rep hS hinvs hi hInv
    have hev := pairLetter_eval hS hb hi
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨hkl, hl⟩, hInv, allBelow_iff'.2 fun j hj => ?_⟩
    have ht := sideGens_rep hS (D.kind[i]! - 1) j
    rw [getD_eq_get hj] at ht
    have hgm : (((D.sideW.getD (D.kind[i]! - 1) []).map (wordVal S)).getD j 1) ∈ pairG D S := by
      refine pairSide_le_pairG (D.kind[i]! - 1) (Subgroup.subset_closure ?_)
      have hj' : j < ((D.sideW.getD (D.kind[i]! - 1) []).map (wordVal S)).length := by
        simpa [sideGens] using hj
      exact getD_mem_listT hj'
    rw [beq_iff_eq]
    exact wordBK_sound hF hB hAl hAli hev.1 hev.2 (pairLetterVals_mem hi) ht hgm
      (fun s hs => by rw [hSG _ hkl j hj, get_u (hB.1 s hs)]) (hw j hj)

theorem checkSideMem_ofT {scnt : Nat → Nat} {ST SPL : Nat → Nat → Nat}
    (hb : PairB D w nr P PI REP REPI)
    (hE : ∀ k < D.sideW.length, sideEnum D k = penumRec D.n w (scnt k) (ST k) (SPL k))
    (hSc : ∀ k < D.sideW.length, ∀ q < scnt k, Cn D.n w (ST k q))
    (hM : ∀ i < D.repW.length, D.kind[i]! ≠ 0 → D.kind[i]! - 1 < D.sideW.length ∧
      ∃ q < scnt (D.kind[i]! - 1), ST (D.kind[i]! - 1) q = REP (i + 1)) :
    checkSideMem D = true := by
  unfold checkSideMem
  rw [allBelow_iff']
  intro i hi
  rw [Bool.or_eq_true]
  by_cases hk : D.kind[i]! = 0
  · left
    simpa using hk
  · right
    obtain ⟨hkl, q, hq, e⟩ := hM i hi hk
    have hi1 : i + 1 < nr := by rw [hb.hnr]; omega
    dsimp only
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hkl, ?_⟩
    rw [hE _ hkl, hb.hr.2 (i + 1) hi1, found_recT (hSc _ hkl)
      (perm_canon (hb.hRi (i + 1) hi1) hb.hn).1]
    exact ⟨q, hq, e⟩

theorem checkMemW_ofT (hS : Sound D S) {bs : List Nat} {nb : Nat} {B : Nat → Nat}
    (hF : BaseFaithful (pairG D S) bs) (hB : BaseOK D.n nb B bs)
    {kG : Nat} {Gp GIp : Nat → Nat} (hGs : D.gT.size = kG)
    (hGb : ∀ j < kG, D.gT[j]! = unpack D.n w (Gp j))
    (hGp : allN kG (fun j => permOK D.n w (mask w) (D.n * w) (Gp j) (GIp j)) = true)
    {scnt : Nat → Nat} {ST SPL : Nat → Nat → Nat} {memW : List (List (List Int))}
    (hml : memW.length ≤ D.sideW.length)
    (hE : ∀ k < memW.length, sideEnum D k = penumRec D.n w (scnt k) (ST k) (SPL k))
    (hIn : ∀ k < memW.length, ∀ q < scnt k, InH (pairG D S) w (ST k q))
    (hK : ∀ k < memW.length, ∀ wd ∈ memW.getD k [], ∃ q < scnt k,
      wordBK kG nb B (genLf w (mask w) Gp) (genLf w (mask w) GIp) wd (pg w (mask w) (ST k q)) =
        true) :
    checkMemW D memW = true := by
  unfold checkMemW
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hml, allBelow_iff'.2 fun k hk => ?_⟩
  rw [List.all_eq_true]
  intro wd hwd
  obtain ⟨q, hq, hw⟩ := hK k hk wd hwd
  obtain ⟨hc, g, hg, ht⟩ := hIn k hk q hq
  have hLf : ∀ l < kG, ∀ y < D.n, genLf w (mask w) Gp l y = (D.gT.getD l (idTab D.n))[y]! := by
    intro l hl y hy
    rw [getD_eq_get (by rw [hGs]; exact hl), hGb l hl, get_u hy]
    rfl
  have hLi : ∀ l < kG, ∀ y < D.n, genLf w (mask w) GIp l y = ((giT D).getD l (idTab D.n))[y]! := by
    intro l hl y hy
    have hl' : l < D.gT.size := by rw [hGs]; exact hl
    rw [getD_eq_get (by simp [giT]; exact hl'), show (giT D)[l]! = invTab D.n D.gT[l]! by
      unfold giT
      rw [getElem!_pos _ l (by simpa using hl'), Array.getElem_map, ← getElem!_pos D.gT l hl'],
      hGb l hl, inv_u ((PK.allN_iff.1 hGp) l hl), get_u hy]
    rfl
  have e := wordBK_sound hF hB hS.rep hS.gi hLf hLi (fun _ hg => Subgroup.subset_closure hg) ht hg
    (fun s hs => by rw [get_u (hB.1 s hs)]) hw
  change found (indexOf (sideEnum D k).tabs) (sideEnum D k).tabs
    (Certificates.FusD2Perm.wordT D.n D.gT (giT D) wd) = true
  rw [e, hE k hk, found_recT (fun q hq => (hIn k hk q hq).1) hc]
  exact ⟨q, hq, rfl⟩

end

end CFSG.KS.TitsOver

end
