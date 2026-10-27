module

public import CFSG.Certificates.Kernel.MaxD2.Test
public import CFSG.Certificates.Kernel.MaxD2.Disj
public import CFSG.Certificates.Kernel.MaxD2.Pair

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native
open Certificates.MaxD2Perm

structure Pk where
  n : Nat
  w : Nat
  kG : Nat
  Gp : Nat → Nat
  GIp : Nat → Nat
  rcnt : Nat
  RG : Nat → Nat
  RGI : Nat → Nat
  RT : Nat → Nat
  RPL : Nat → Nat
  RPOS : Nat → Nat
  RSRT : Nat → Nat
  RSRI : Nat → Nat
  kN : Nat
  cnt : Nat
  NG : Nat → Nat
  NGI0 : Nat → Nat
  NT : Nat → Nat
  NPL : Nat → Nat
  NPOS : Nat → Nat
  NSRT : Nat → Nat
  NSRI : Nat → Nat
  NGI : Nat → Nat
  nr : Nat
  REP : Nat → Nat
  REPI : Nat → Nat
  np : Nat
  kw : Nat
  PT : Nat → Nat
  FS : Nat → Nat
  KS : Nat → Nat
  RB : Nat → Nat
  H : Nat → Nat
  CN : Nat → Nat
  TP : Nat
  TPI : Nat
  th : Nat
  CH : Nat → Nat
  NH : Nat → Nat
  L : Nat → Nat
  hi : Nat
  cw : Nat
  nl : Nat
  MK : Nat → Nat
  mj : Nat
  mi : Nat
  RB2 : Nat → Nat := fun _ => 0
  H2 : Nat → Nat := fun _ => 0
  PQ : Nat → Nat → Nat := fun _ _ => 0

@[expose] noncomputable def Pk.sg (K : Pk) (i l : Nat) : Nat :=
  nIf(Nat.blt l K.kN, K.NG l, K.REP (Nat.succ i))

@[expose] noncomputable def Pk.sgi (K : Pk) (i l : Nat) : Nat :=
  nIf(Nat.blt l K.kN, K.NGI l, K.REPI (Nat.succ i))

structure HypsM (D : Data) (K : Pk) : Prop where
  hn : szOK K.n K.w = true
  hDn : D.n = K.n
  hGs : D.gT.size = K.kG
  hGb : ∀ j < K.kG, D.gT[j]! = unpack K.n K.w (K.Gp j)
  hGp : allN K.kG (fun j => permOK K.n K.w (mask K.w) (K.n * K.w) (K.Gp j) (K.GIp j)) = true
  hNk : D.nW.length = K.kN
  hNG : ∀ j < K.kN, wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG (D.nW[j]!) (K.NG j) =
    true ∧ Cn K.n K.w (K.NG j)
  hNh : penumHdK (pidn K.n K.w) K.cnt D.nOrder K.NT K.NPL = true
  hNp : ∀ i < K.cnt, penumPtK K.n K.w (mask K.w) (K.n * K.w) false K.NG K.NGI0 K.kN K.cnt K.NT K.NPL
    K.NPOS K.NSRT K.NSRI i = true
  hNc : K.cnt = D.nOrder
  hNI : ∀ j < K.kN, permOK K.n K.w (mask K.w) (K.n * K.w) (K.NG j) (K.NGI j) = true
  hRn : K.nr = D.repW.length + 1
  hR0 : K.REP 0 = pidn K.n K.w
  hRw : ∀ i < D.repW.length,
    wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG (D.repW[i]!) (K.REP (i + 1)) = true
  hRi : ∀ i < K.nr, permOK K.n K.w (mask K.w) (K.n * K.w) (K.REP i) (K.REPI i) = true
  hPts : PtsOK K.n K.np D.fpPts K.PT
  hS : ∀ s < K.cnt, sortK K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS s = true
  hTest : ∀ i, 0 < i → i < K.nr →
    repK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB K.H i = true
  hCnt : ∀ i, 0 < i → i < K.nr → posCnt K.cnt K.H i = K.CN i
  hSum : (List.range K.nr).foldl
    (fun s i => s + D.nOrder * D.nOrder / (if i = 0 then K.cnt else K.CN i)) 0 = D.gOrder
  hL : labK K.n K.w K.kN K.NG K.L = true
  hM : K.n ≤ 64 * K.hi
  hMK : ∀ i < K.nr, K.MK i = mkeyK K.n K.w K.hi K.cw K.nl K.L (K.REP i)
  hMd : ∀ i < K.nr, ∀ j < K.nr, i < j → K.MK i ≠ K.MK j ∨
    pairK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB2 K.H2 (K.PQ i j) i j =
      true
  hGl : D.genW.length = D.repW.length
  hGen : ∀ i < D.repW.length, (D.genW[i]!).length = K.kG ∧ ∀ j < K.kG,
    wordEqK K.n K.w (mask K.w) (pidn K.n K.w) (K.sg i) (K.sgi i) (K.kN + 1) ((D.genW[i]!)[j]!)
      (K.Gp j) = true

structure Hyps (D : Data) (K : Pk) : Prop where
  hn : szOK K.n K.w = true
  hDn : D.n = K.n
  hGs : D.gT.size = K.kG
  hGb : ∀ j < K.kG, D.gT[j]! = unpack K.n K.w (K.Gp j)
  hGp : allN K.kG (fun j => permOK K.n K.w (mask K.w) (K.n * K.w) (K.Gp j) (K.GIp j)) = true
  hRG : ∀ j < 2, wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG ((rWs D)[j]!) (K.RG j) =
    true ∧ Cn K.n K.w (K.RG j)
  hRh : penumHdK (pidn K.n K.w) K.rcnt (D.p ^ 2) K.RT K.RPL = true
  hRp : ∀ i < K.rcnt, penumPtK K.n K.w (mask K.w) (K.n * K.w) false K.RG K.RGI 2 K.rcnt K.RT K.RPL
    K.RPOS K.RSRT K.RSRI i = true
  hRc : K.rcnt = D.p ^ 2
  hNk : D.nW.length = K.kN
  hNG : ∀ j < K.kN, wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG (D.nW[j]!) (K.NG j) =
    true ∧ Cn K.n K.w (K.NG j)
  hNh : penumHdK (pidn K.n K.w) K.cnt D.nOrder K.NT K.NPL = true
  hNp : ∀ i < K.cnt, penumPtK K.n K.w (mask K.w) (K.n * K.w) false K.NG K.NGI0 K.kN K.cnt K.NT K.NPL
    K.NPOS K.NSRT K.NSRI i = true
  hNc : K.cnt = D.nOrder
  hNI : ∀ j < K.kN, permOK K.n K.w (mask K.w) (K.n * K.w) (K.NG j) (K.NGI j) = true
  hNorm : ∀ j < K.kN, ∀ i < 2,
    conjInK K.n K.w K.rcnt K.RT (K.NG j) (K.NGI j) (K.RG i) (r32 K.NH (4 * j + 2 * i)) = true ∧
    conjInK K.n K.w K.rcnt K.RT (K.NGI j) (K.NG j) (K.RG i) (r32 K.NH (4 * j + 2 * i + 1)) = true
  hMj : K.mj < K.kG
  hMi : K.mi < 2
  hMv : notInK K.rcnt K.RT
    (pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (K.Gp K.mj) (K.RG K.mi)) (K.GIp K.mj)) = true
  hTw : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG D.tW K.TP = true
  hTp : permOK K.n K.w (mask K.w) (K.n * K.w) K.TP K.TPI = true
  hTh : K.th < K.cnt
  hTn : K.NT K.th = K.TP
  hTk : torusK K.n K.w D.p K.rcnt D.tm D.tlam D.te K.RT K.TP K.TPI = true
  hC : ∀ k < K.cnt, centK K.n K.w K.rcnt K.NT K.RT (K.RG 0) (K.RG 1) (r32 K.CH k) k = true
  hRn : K.nr = D.repW.length + 1
  hR0 : K.REP 0 = pidn K.n K.w
  hRw : ∀ i < D.repW.length,
    wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG (D.repW[i]!) (K.REP (i + 1)) = true
  hRi : ∀ i < K.nr, permOK K.n K.w (mask K.w) (K.n * K.w) (K.REP i) (K.REPI i) = true
  hPts : PtsOK K.n K.np D.fpPts K.PT
  hS : ∀ s < K.cnt, sortK K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS s = true
  hTest : ∀ i, 0 < i → i < K.nr →
    repK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB K.H i = true
  hCnt : ∀ i, 0 < i → i < K.nr → posCnt K.cnt K.H i = K.CN i
  hSum : (List.range K.nr).foldl
    (fun s i => s + D.nOrder * D.nOrder / (if i = 0 then K.cnt else K.CN i)) 0 = D.gOrder
  hL : labK K.n K.w K.kN K.NG K.L = true
  hM : K.n ≤ 64 * K.hi
  hMK : ∀ i < K.nr, K.MK i = mkeyK K.n K.w K.hi K.cw K.nl K.L (K.REP i)
  hMd : ∀ i < K.nr, ∀ j < K.nr, i < j → K.MK i ≠ K.MK j ∨
    pairK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB2 K.H2 (K.PQ i j) i j =
      true
  hGl : D.genW.length = D.repW.length
  hGen : ∀ i < D.repW.length, (D.genW[i]!).length = K.kG ∧ ∀ j < K.kG,
    wordEqK K.n K.w (mask K.w) (pidn K.n K.w) (K.sg i) (K.sgi i) (K.kN + 1) ((D.genW[i]!)[j]!)
      (K.Gp j) = true

theorem Hyps.toM {D : Data} {K : Pk} (H : Hyps D K) : HypsM D K :=
  ⟨H.hn, H.hDn, H.hGs, H.hGb, H.hGp, H.hNk, H.hNG, H.hNh, H.hNp, H.hNc, H.hNI, H.hRn, H.hR0,
    H.hRw, H.hRi, H.hPts, H.hS, H.hTest, H.hCnt, H.hSum, H.hL, H.hM, H.hMK, H.hMd, H.hGl, H.hGen⟩

theorem wordT_eq_wordA' {n : Nat} {gs gi : Array (Array Nat)} (hs : gi.size = gs.size) :
    ∀ w : List Int, lettersOK gs.size w = true →
      Certificates.FusD2Perm.wordT n gs gi w = wordA n gs gi w
  | [], _ => rfl
  | z :: w, h => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at h
    obtain ⟨⟨hz0, hzk⟩, hw⟩ := h
    have ih := wordT_eq_wordA' (n := n) hs w (by simpa only [lettersOK] using hw)
    change comp n _ (Certificates.FusD2Perm.wordT n gs gi w) = compA n (letterA gs gi z) (wordA n gs gi w)
    rw [ih]
    change compA n _ _ = compA n _ _
    congr 1
    unfold letterA
    by_cases hz : 0 < z
    · rw [ite_eq_left hz, ite_eq_left hz, Array.getD_eq_getD_getElem?,
        getElem!_pos gs (z.toNat - 1) (by omega), Array.getElem?_eq_getElem (by omega)]
      rfl
    · rw [ite_eq_right hz, ite_eq_right hz, Array.getD_eq_getD_getElem?,
        getElem!_pos gi ((-z).toNat - 1) (by omega), Array.getElem?_eq_getElem (by omega)]
      rfl

theorem wordT_u {n w k r : Nat} {S : Array Tab} {PS PSI : Nat → Nat} {wd : List Int}
    (hS : S.size = k ∧ ∀ j < k, S[j]! = unpack n w (PS j))
    (hp : allN k (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (h : wordEqK n w (mask w) (pidn n w) PS PSI k wd r = true) :
    Certificates.FusD2Perm.wordT n S (S.map (invTab n)) wd = unpack n w r := by
  obtain ⟨e, hlo⟩ := wordEqK_sound hS hp h
  rw [wordT_eq_wordA' (by simp) wd (by rw [hS.1]; exact hlo)]
  exact e

section

variable {D : Data} {K : Pk}

theorem wT_u (H : HypsM D K) {wd : List Int} {r : Nat}
    (h : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG wd r = true) :
    wT D wd = unpack K.n K.w r := by
  unfold wT giT
  rw [H.hDn]
  exact wordT_u ⟨H.hGs, H.hGb⟩ H.hGp h

theorem gp_perm (H : HypsM D K) {j : Nat} (hj : j < K.kG) :
    permOK K.n K.w (mask K.w) (K.n * K.w) (K.Gp j) (K.GIp j) = true :=
  (PK.allN_iff.1 H.hGp) j hj

theorem gi_u (H : HypsM D K) {j : Nat} (hj : j < K.kG) : (giT D)[j]! = unpack K.n K.w (K.GIp j) := by
  have hj' : j < D.gT.size := by rw [H.hGs]; exact hj
  unfold giT
  rw [getElem!_pos _ j (by simpa using hj'), Array.getElem_map, ← getElem!_pos D.gT j hj',
    H.hGb j hj, H.hDn, inv_u (gp_perm H hj)]

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {j : Nat}
    (hj : j < l.length) : (l.map f).toArray[j]! = f l[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos l j hj]
  simp

theorem rgens (H : Hyps D K) : GensOK K.n K.w 2 K.RG (rGens D) := by
  refine ⟨by simp [rGens, rWs], fun j hj => ⟨?_, (H.hRG j hj).2⟩⟩
  unfold rGens
  rw [map_get _ (by simpa [rWs] using hj), wT_u H.toM (H.hRG j hj).1]

theorem ngens (H : HypsM D K) : GensOK K.n K.w K.kN K.NG (nGens D) := by
  refine ⟨by simp [nGens, H.hNk], fun j hj => ⟨?_, (H.hNG j hj).2⟩⟩
  unfold nGens
  rw [map_get _ (by rw [H.hNk]; exact hj), wT_u H (H.hNG j hj).1]

theorem rEnum_eq (H : Hyps D K) :
    rEnum D = penumRec K.n K.w K.rcnt K.RT K.RPL ∧
      enumOK K.n (rGens D) (penumRec K.n K.w K.rcnt K.RT K.RPL) = true := by
  unfold rEnum
  rw [H.hDn]
  exact penumK_left_sound H.hn (rgens H) H.hRh H.hRp

theorem nEnum_eq (H : HypsM D K) :
    nEnum D = penumRec K.n K.w K.cnt K.NT K.NPL ∧
      enumOK K.n (nGens D) (penumRec K.n K.w K.cnt K.NT K.NPL) = true := by
  unfold nEnum
  rw [H.hDn]
  exact penumK_left_sound H.hn (ngens H) H.hNh H.hNp

theorem rec_get {n w cnt i : Nat} {T PL : Nat → Nat} (hi : i < cnt) :
    (penumRec n w cnt T PL).tabs[i]! = unpack n w (T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem rec_size (n w cnt : Nat) (T PL : Nat → Nat) : (penumRec n w cnt T PL).tabs.size = cnt := by
  simp [penumRec]

theorem rt_canon (H : Hyps D K) {i : Nat} (hi : i < K.rcnt) : Cn K.n K.w (K.RT i) :=
  (pt_spec (H.hRp i hi)).1

theorem nt_canon (H : HypsM D K) {i : Nat} (hi : i < K.cnt) : Cn K.n K.w (K.NT i) :=
  (pt_spec (H.hNp i hi)).1

theorem foundR (H : Hyps D K) {X : Nat} (hX : Cn K.n K.w X) :
    found (indexOf (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs) (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs
      (unpack K.n K.w X) = true ↔ ∃ i < K.rcnt, K.RT i = X := by
  rw [found_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    exact ⟨i, hi, u_inj (rt_canon H hi) hX e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [rec_size]; exact hi, rec_get hi⟩

theorem foundN (H : HypsM D K) {X : Nat} (hX : Cn K.n K.w X) :
    found (indexOf (penumRec K.n K.w K.cnt K.NT K.NPL).tabs) (penumRec K.n K.w K.cnt K.NT K.NPL).tabs
      (unpack K.n K.w X) = true ↔ ∃ i < K.cnt, K.NT i = X := by
  rw [found_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    exact ⟨i, hi, u_inj (nt_canon H hi) hX e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [rec_size]; exact hi, rec_get hi⟩

theorem checkInv_of (H : HypsM D K) : checkInv D = true := by
  unfold checkInv
  rw [allBelow_iff']
  intro j hj
  have hj' : j < K.kG := by rw [← H.hGs]; exact hj
  rw [gi_u H hj', H.hGb j hj', H.hDn, inv_comp (gp_perm H hj')]
  simp [size_u]

theorem checkR_of (H : Hyps D K) : checkR D = true := by
  obtain ⟨e, hok⟩ := rEnum_eq H
  unfold checkR
  rw [e, H.hDn, hok, rec_size, H.hRc]
  simp

theorem checkN_of (H : HypsM D K) : checkN D = true := by
  obtain ⟨e, hok⟩ := nEnum_eq H
  unfold checkN
  rw [e, H.hDn, hok, rec_size, H.hNc]
  simp

theorem ng_get (H : HypsM D K) {j : Nat} (hj : j < K.kN) : (nGens D)[j]! = unpack K.n K.w (K.NG j) :=
  ((ngens H).2 j hj).1

theorem ngi_get (H : HypsM D K) {j : Nat} (hj : j < K.kN) :
    (nGensI D)[j]! = unpack K.n K.w (K.NGI j) := by
  have hs : (nGens D).size = K.kN := (ngens H).1
  unfold nGensI
  rw [getElem!_pos _ j (by simpa [hs] using hj), Array.getElem_map,
    ← getElem!_pos (nGens D) j (by rw [hs]; exact hj), ng_get H hj, H.hDn, inv_u (H.hNI j hj)]

theorem rg_get (H : Hyps D K) {j : Nat} (hj : j < 2) : (rGens D)[j]! = unpack K.n K.w (K.RG j) :=
  ((rgens H).2 j hj).1

theorem ng_perm (H : HypsM D K) {j : Nat} (hj : j < K.kN) :
    Cn K.n K.w (K.NG j) ∧ Cn K.n K.w (K.NGI j) := perm_canon (H.hNI j hj) H.hn

theorem conjIn_spec (H : Hyps D K) {g gi x h : Nat} (hg : Cn K.n K.w g) (hgi : Cn K.n K.w gi)
    (hx : Cn K.n K.w x) (hk : conjInK K.n K.w K.rcnt K.RT g gi x h = true) :
    found (indexOf (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs) (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs
      (conjTab K.n (unpack K.n K.w g) (unpack K.n K.w gi) (unpack K.n K.w x)) = true := by
  unfold conjTab
  rw [comp_u hg hx, comp_u (cc hg hx) hgi, foundR H (cc (cc hg hx) hgi)]
  unfold conjInK at hk
  obtain ⟨h1, h2⟩ := band_e hk
  exact ⟨h, Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem checkNormal_of (H : Hyps D K) : checkNormal D = true := by
  obtain ⟨e, -⟩ := rEnum_eq H
  unfold checkNormal normalOK
  rw [e, H.hDn]
  have hs : (nGens D).size = K.kN := (ngens H.toM).1
  have hsi : (nGensI D).size = K.kN := by simp [nGensI, hs]
  have hr : (rGens D).size = 2 := (rgens H).1
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold invsOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [hs, hsi], allBelow_iff'.2 fun j hj => ?_⟩
    rw [hs] at hj
    rw [ngi_get H.toM hj, ng_get H.toM hj, inv_comp (H.hNI j hj)]
    simp [size_u]
  · rw [allBelow_iff']
    intro j hj
    rw [hs] at hj
    rw [allBelow_iff']
    intro i hi
    rw [hr] at hi
    rw [ng_get H.toM hj, ngi_get H.toM hj, rg_get H hi]
    have hc := ng_perm H.toM hj
    have hx : Cn K.n K.w (K.RG i) := (H.hRG i hi).2
    simp only [Bool.and_eq_true]
    exact ⟨conjIn_spec H hc.1 hc.2 hx (H.hNorm j hj i hi).1,
      conjIn_spec H hc.2 hc.1 hx (H.hNorm j hj i hi).2⟩

theorem checkMoves_of (H : Hyps D K) : checkMoves D = true := by
  obtain ⟨e, -⟩ := rEnum_eq H
  unfold checkMoves
  simp only []
  rw [e, anyBelow_iff]
  refine ⟨K.mj, by rw [H.hGs]; exact H.hMj, ?_⟩
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, allBelow_iff']
  intro hall
  have hr : (rGens D).size = 2 := (rgens H).1
  have h := hall K.mi (by rw [hr]; exact H.hMi)
  have hgp := perm_canon (gp_perm H.toM H.hMj) H.hn
  have hx : Cn K.n K.w (K.RG K.mi) := (H.hRG K.mi H.hMi).2
  rw [H.hGb _ H.hMj, gi_u H.toM H.hMj, rg_get H H.hMi, H.hDn] at h
  unfold conjTab at h
  rw [comp_u hgp.1 hx, comp_u (cc hgp.1 hx) hgp.2, foundR H (cc (cc hgp.1 hx) hgp.2)] at h
  obtain ⟨r, hr', er⟩ := h
  have hm := (PK.allN_iff.1 H.hMv) r hr'
  rw [er, Nat.beq_refl] at hm
  exact absurd hm (by decide)

theorem checkTorus_of (H : Hyps D K) : checkTorus D = true := by
  obtain ⟨eR, -⟩ := rEnum_eq H
  obtain ⟨eN, -⟩ := nEnum_eq H.toM
  have hT := perm_canon H.hTp H.hn
  have hn := H.hn
  have hk := H.hTk
  unfold torusK at hk
  simp only [PK.strictB_eq] at hk
  obtain ⟨k1, hk⟩ := band_e hk
  obtain ⟨k2, k3⟩ := band_e hk
  have pa := pw_canon hn hT.1
  have pb := pw_canon hn hT.2
  unfold checkTorus
  simp only [eR, eN, H.hDn, wT_u H.toM H.hTw, inv_u H.hTp, rec_size, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [size_u]
  · rw [inv_comp H.hTp]
    exact beq_self_eq_true _
  · rw [foundN H.toM hT.1]
    exact ⟨K.th, H.hTh, H.hTn⟩
  · rw [allBelow_iff']
    intro k hk
    have e := (PK.allN_iff.1 k1) k hk
    have hr := rt_canon H hk
    rw [rec_get hk, powT_u hn hT.1, powT_u hn hT.2, powT_u hn hr, comp_u (pa _) hr,
      comp_u (cc (pa _) hr) (pb _), eq_u (cc (cc (pa _) hr) (pb _)) (pw_canon hn hr _)]
    exact e
  · rw [allBelow_iff']
    intro k hk
    have e := (PK.allN_iff.1 k2) k hk
    have hr := rt_canon H hk
    rw [rec_get hk, powT_u hn hT.1, powT_u hn hT.2, comp_u (pa _) hr, comp_u (cc (pa _) hr) (pb _),
      comp_u (cc (cc (pa _) hr) (pb _)) hr, id_u hn,
      eq_u (cc (cc (cc (pa _) hr) (pb _)) hr) (pidn_canon hn)]
    exact e
  · rw [allBelow_iff']
    intro k hk
    rw [allBelow_iff']
    intro i hi
    have e := (PK.allN_iff.1 ((PK.allN_iff.1 k3) k hk)) i hi
    have hr := rt_canon H hi
    rw [Bool.or_eq_true, rec_get hi, id_u hn, eq_u hr (pidn_canon hn)]
    rcases bor_e e with z | z
    · exact Or.inl z
    · right
      rw [allBelow_iff']
      intro j hj
      have e' := bnot_e ((PK.allN_iff.1 z) j hj)
      rw [powT_u hn hT.1, powT_u hn hT.2, powT_u hn hr, comp_u (pa _) hr,
        comp_u (cc (pa _) hr) (pb _), eq_u (cc (cc (pa _) hr) (pb _)) (pw_canon hn hr _)]
      rw [Bool.not_eq_true']
      exact e'

theorem checkCent_of (H : Hyps D K) : checkCent D = true := by
  obtain ⟨eR, -⟩ := rEnum_eq H
  obtain ⟨eN, -⟩ := nEnum_eq H.toM
  have hn := H.hn
  unfold checkCent
  simp only [eR, eN, H.hDn, rec_size]
  rw [allBelow_iff']
  intro k hk
  have hc := H.hC k hk
  have ha := nt_canon H.toM hk
  have hu : Cn K.n K.w (K.RG 0) := (H.hRG 0 (by decide)).2
  have hv : Cn K.n K.w (K.RG 1) := (H.hRG 1 (by decide)).2
  rw [rec_get hk, rg_get H (by decide : 0 < 2), rg_get H (by decide : 1 < 2),
    comp_u ha hu, comp_u hu ha, comp_u ha hv, comp_u hv ha, eq_u (cc ha hu) (cc hu ha),
    eq_u (cc ha hv) (cc hv ha), Bool.or_eq_true]
  unfold centK at hc
  rw [PK.strictB_eq] at hc
  by_cases h1 : Nat.beq (Nat.land (r32 K.CH k) 1) 1 = true
  · have h := bif_t h1 hc
    rw [PK.strictB_eq] at h
    obtain ⟨hr, he⟩ := band_e h
    right
    rw [foundR H ha]
    exact ⟨_, Nat.blt_eq.mp hr, (Nat.eq_of_beq_eq_true he).symm⟩
  · have h := bif_f (Bool.eq_false_iff.2 h1) hc
    simp only [PK.strictB_eq] at h
    obtain ⟨hp, hd⟩ := band_e h
    have hp' := Nat.blt_eq.mp hp
    have hd' := bnot_e hd
    left
    rw [Bool.not_eq_true', Bool.and_eq_false_iff]
    have key : ∀ g : Nat, Cn K.n K.w g →
        Nat.beq (pg K.w (mask K.w) (K.NT k) (pg K.w (mask K.w) g (Nat.shiftRight (r32 K.CH k) 2)))
          (pg K.w (mask K.w) g (pg K.w (mask K.w) (K.NT k) (Nat.shiftRight (r32 K.CH k) 2))) = false →
        Nat.beq (pcomp K.n K.w (mask K.w) (K.NT k) g) (pcomp K.n K.w (mask K.w) g (K.NT k)) = false :=
      fun g _ e => by
        rw [Bool.eq_false_iff]
        intro e'
        have e2 := congrArg (fun x => pg K.w (mask K.w) x (Nat.shiftRight (r32 K.CH k) 2))
          (Nat.eq_of_beq_eq_true e')
        simp only [pg_pc hn hp'] at e2
        rw [e2, Nat.beq_refl] at e
        exact absurd e (by decide)
    by_cases hs : Nat.beq (Nat.land (Nat.shiftRight (r32 K.CH k) 1) 1) 0 = true
    · left
      rw [hs] at hd'
      exact key _ hu hd'
    · right
      rw [Bool.eq_false_iff.2 hs] at hd'
      exact key _ hv hd'

end

end CFSG.KS.MaxD2

end
