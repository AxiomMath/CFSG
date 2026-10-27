module

public import CFSG.Certificates.Kernel.MaxD2.Max
public import Certificates.Data.MaxD2TI
public import Certificates.Data.OverD2Perm
public import Certificates.Data.Kernel.MaxD2.Closed

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native
open Certificates.MaxD2Perm

structure HypsC (D : Data) (K : Pk) : Prop where
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

structure HypsB (D : Data) (K : Pk) : Prop extends HypsC D K where
  hSum : (List.range K.nr).foldl
    (fun s i => s + D.nOrder * D.nOrder / (if i = 0 then K.cnt else K.CN i)) 0 = D.gOrder
  hL : labK K.n K.w K.kN K.NG K.L = true
  hM : K.n ≤ 64 * K.hi
  hMK : ∀ i < K.nr, K.MK i = mkeyK K.n K.w K.hi K.cw K.nl K.L (K.REP i)
  hMd : ∀ i < K.nr, ∀ j < K.nr, i < j → K.MK i ≠ K.MK j ∨
    pairK K.n K.w K.np K.kw K.cnt K.PT K.NT K.FS K.KS K.REP K.REPI K.RB2 K.H2 (K.PQ i j) i j =
      true

section

variable {D : Data} {K : Pk}

theorem c_wT_u (H : HypsC D K) {wd : List Int} {r : Nat}
    (h : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG wd r = true) :
    wT D wd = unpack K.n K.w r := by
  unfold wT giT
  rw [H.hDn]
  exact wordT_u ⟨H.hGs, H.hGb⟩ H.hGp h

theorem c_gp_perm (H : HypsC D K) {j : Nat} (hj : j < K.kG) :
    permOK K.n K.w (mask K.w) (K.n * K.w) (K.Gp j) (K.GIp j) = true :=
  (PK.allN_iff.1 H.hGp) j hj

theorem c_gi_u (H : HypsC D K) {j : Nat} (hj : j < K.kG) :
    (giT D)[j]! = unpack K.n K.w (K.GIp j) := by
  have hj' : j < D.gT.size := by rw [H.hGs]; exact hj
  unfold giT
  rw [getElem!_pos _ j (by simpa using hj'), Array.getElem_map, ← getElem!_pos D.gT j hj',
    H.hGb j hj, H.hDn, inv_u (c_gp_perm H hj)]

theorem c_ngens (H : HypsC D K) : GensOK K.n K.w K.kN K.NG (nGens D) := by
  refine ⟨by simp [nGens, H.hNk], fun j hj => ⟨?_, (H.hNG j hj).2⟩⟩
  unfold nGens
  rw [map_get _ (by rw [H.hNk]; exact hj), c_wT_u H (H.hNG j hj).1]

theorem c_nEnum_eq (H : HypsC D K) :
    nEnum D = penumRec K.n K.w K.cnt K.NT K.NPL ∧
      enumOK K.n (nGens D) (penumRec K.n K.w K.cnt K.NT K.NPL) = true := by
  unfold nEnum
  rw [H.hDn]
  exact penumK_left_sound H.hn (c_ngens H) H.hNh H.hNp

theorem c_nt_canon (H : HypsC D K) {i : Nat} (hi : i < K.cnt) : Cn K.n K.w (K.NT i) :=
  (pt_spec (H.hNp i hi)).1

theorem c_checkInv_of (H : HypsC D K) : checkInv D = true := by
  unfold checkInv
  rw [allBelow_iff']
  intro j hj
  have hj' : j < K.kG := by rw [← H.hGs]; exact hj
  rw [c_gi_u H hj', H.hGb j hj', H.hDn, inv_comp (c_gp_perm H hj')]
  simp [size_u]

theorem c_checkN_of (H : HypsC D K) : checkN D = true := by
  obtain ⟨e, hok⟩ := c_nEnum_eq H
  unfold checkN
  rw [e, H.hDn, hok, rec_size, H.hNc]
  simp

theorem c_ng_get (H : HypsC D K) {j : Nat} (hj : j < K.kN) :
    (nGens D)[j]! = unpack K.n K.w (K.NG j) :=
  ((c_ngens H).2 j hj).1

theorem c_ngi_get (H : HypsC D K) {j : Nat} (hj : j < K.kN) :
    (nGensI D)[j]! = unpack K.n K.w (K.NGI j) := by
  have hs : (nGens D).size = K.kN := (c_ngens H).1
  unfold nGensI
  rw [getElem!_pos _ j (by simpa [hs] using hj), Array.getElem_map,
    ← getElem!_pos (nGens D) j (by rw [hs]; exact hj), c_ng_get H hj, H.hDn, inv_u (H.hNI j hj)]

theorem c_invsN (H : HypsC D K) : invsOK D.n (nGens D) (nGensI D) = true := by
  have hs : (nGens D).size = K.kN := (c_ngens H).1
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [nGensI], allBelow_iff'.2 fun k hk => ?_⟩
  rw [hs] at hk
  rw [c_ngi_get H hk, c_ng_get H hk, H.hDn, inv_comp (H.hNI k hk)]
  simp [size_u]

theorem c_rep_size (H : HypsC D K) : (repT D).size = K.nr := by
  simp [repT, H.hRn]

theorem c_rep_get (H : HypsC D K) {i : Nat} (hi : i < K.nr) :
    (repT D)[i]! = unpack K.n K.w (K.REP i) := by
  have hs := c_rep_size H
  have e : repT D = (idTab D.n :: D.repW.map (wT D)).toArray := by
    simp [repT]
  rw [e, getElem!_pos _ i (by rw [← e, hs]; exact hi)]
  rcases i with _ | j
  · simp [H.hR0, H.hDn, id_u H.hn]
  · have hj : j < D.repW.length := by rw [H.hRn] at hi; omega
    simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_map]
    rw [← getElem!_pos D.repW j hj]
    exact c_wT_u H (H.hRw j hj)

theorem c_repi_get (H : HypsC D K) {i : Nat} (hi : i < K.nr) :
    (repI D)[i]! = unpack K.n K.w (K.REPI i) := by
  have hs := c_rep_size H
  unfold repI
  rw [getElem!_pos _ i (by simpa [hs] using hi), Array.getElem_map,
    ← getElem!_pos (repT D) i (by rw [hs]; exact hi), c_rep_get H hi, H.hDn, inv_u (H.hRi i hi)]

theorem c_repi_size (H : HypsC D K) : (repI D).size = K.nr := by simp [repI, c_rep_size H]

theorem c_invsRep (H : HypsC D K) : invsOK D.n (repT D) (repI D) = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [c_repi_size H, c_rep_size H], allBelow_iff'.2 fun k hk => ?_⟩
  rw [c_rep_size H] at hk
  rw [c_repi_get H hk, c_rep_get H hk, H.hDn, inv_comp (H.hRi k hk)]
  simp [size_u]

theorem c_nT_get (H : HypsC D K) {i : Nat} (hi : i < K.cnt) :
    (nEnum D).tabs[i]! = unpack K.n K.w (K.NT i) := by
  rw [(c_nEnum_eq H).1, rec_get hi]

theorem c_nT_size (H : HypsC D K) : (nEnum D).tabs.size = K.cnt := by
  rw [(c_nEnum_eq H).1, rec_size]

theorem c_fp_inj (H : HypsC D K) :
    ∀ a < (nEnum D).tabs.size, ∀ b < (nEnum D).tabs.size,
      fpTab D.fpPts (nEnum D).tabs[a]! = fpTab D.fpPts (nEnum D).tabs[b]! → a = b := by
  intro a ha b hb e
  rw [c_nT_size H] at ha hb
  rw [c_nT_get H ha, c_nT_get H hb] at e
  exact sort_keyInj H.hS ha hb (fpK_of_fpTab H.hPts e)

theorem c_memN_iff (H : HypsC D K) {X : Nat} (hX : Cn K.n K.w X) :
    memFp D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts))) ((nEnum D).tabs.map (fpTab D.fpPts))
      (nEnum D).tabs (unpack K.n K.w X) = true ↔ ∃ e < K.cnt, K.NT e = X := by
  rw [memFp_iff (c_fp_inj H), c_nT_size H]
  constructor
  · rintro ⟨m, hm, e⟩
    rw [c_nT_get H hm] at e
    exact ⟨m, hm, u_inj (c_nt_canon H hm) hX e⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, c_nT_get H hm⟩

theorem c_rep_perm (H : HypsC D K) {i : Nat} (hi : i < K.nr) :
    Cn K.n K.w (K.REP i) ∧ Cn K.n K.w (K.REPI i) := perm_canon (H.hRi i hi) H.hn

theorem c_repi0 (H : HypsC D K) (h0 : 0 < K.nr) :
    ∀ j < K.n, pg K.w (mask K.w) (K.REPI 0) j = j := fun j hj => by
  have hq := perm_spec (H.hRi 0 h0)
  rw [H.hR0] at hq
  have := (hq.1 j hj).2
  rwa [pidn_get H.hn hj] at this

theorem c_conjCount_eq (H : HypsC D K) {i : Nat} (hi : i < K.nr) :
    conjCount D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repI D)[i]! (repT D)[i]! =
      if i = 0 then K.cnt else K.CN i := by
  have hn := H.hn
  have hr := c_rep_perm H hi
  unfold conjCount
  rw [c_repi_get H hi, c_rep_get H hi, c_nT_size H, H.hDn]
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl]
    refine (countBelow_eq (g := fun _ => true) fun k hk => ?_).trans (countBelow_true K.cnt)
    have hqid := c_repi0 H hi
    have e : comp K.n (comp K.n (unpack K.n K.w (K.REPI 0)) (nEnum D).tabs[k]!)
        (unpack K.n K.w (K.REP 0)) = unpack K.n K.w (K.NT k) := by
      rw [c_nT_get H hk]
      refine tab_ext (comp_size _ _) (size_u _) fun x hx => ?_
      rw [comp_get hx, H.hR0, get_u hx, pidn_get hn hx, comp_get hx, get_u hx,
        get_u (canon_lt (c_nt_canon H hk) hx), hqid _ (canon_lt (c_nt_canon H hk) hx)]
    rw [e, c_memN_iff H (c_nt_canon H hk)]
    exact ⟨k, hk, rfl⟩
  · rw [if_neg h0, ← H.hCnt i (Nat.pos_of_ne_zero h0) hi]
    unfold posCnt
    rw [PK.foldN_eq, foldr_count]
    refine countBelow_eq fun k hk => ?_
    have ht := H.hTest i (Nat.pos_of_ne_zero h0) hi
    unfold repK at ht
    simp only [PK.strictB_eq] at ht
    obtain ⟨hrb, hts⟩ := band_e ht
    have hk' := (PK.allN_iff.1 hts) k hk
    have hspec := testK_spec hn (fun e he => c_nt_canon H he) H.hS
      (fun t ht => (H.hPts.2 t ht).2) (H.hRi i hi)
      (fun t ht => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 hrb) t ht)) hk hk'
    have ha := c_nt_canon H hk
    rw [c_nT_get H hk, comp_u hr.2 ha, comp_u (cc hr.2 ha) hr.1, Bool.eq_iff_iff,
      c_memN_iff H (cc (cc hr.2 ha) hr.1), hspec, beq_iff_eq]

theorem c_checkTI_of (H : HypsC D K) (hp : ∀ i, 0 < i → i < K.nr → K.CN i % D.p ≠ 0) :
    Certificates.MaxD2TI.checkTI D = true := by
  unfold Certificates.MaxD2TI.checkTI
  refine allBelow_iff'.2 fun i hi => ?_
  have hi1 : i + 1 < K.nr := by rw [H.hRn]; omega
  rw [c_conjCount_eq H hi1, if_neg (Nat.succ_ne_zero i)]
  simpa using hp (i + 1) (Nat.succ_pos i) hi1

theorem c_dcSum_of (H : HypsB D K) :
    dcSum D.n D.nOrder D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = D.gOrder := by
  unfold dcSum
  rw [← H.hSum, c_rep_size H.toHypsC]
  refine foldl_congr_range (fun s i hi => ?_) 0
  rw [c_conjCount_eq H.toHypsC hi]

theorem c_disj_spec (H : HypsB D K) {i j k : Nat} (hi : i < K.nr) (hj : j < K.nr) (hij : i < j)
    (hk : k < K.cnt) : ¬ ∃ m < K.cnt, K.NT m =
      pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (K.REPI i) (K.NT k)) (K.REP j) := by
  have hn := H.hn
  have hLP := enum_facts hn H.hNh H.hNp H.hNI H.hL
  rintro ⟨m, hm', em⟩
  have hj' := perm_spec (H.hRi j hj)
  rcases H.hMd i hi j hj hij with hd | hp
  · have key := mkey_eq hn (hi := K.hi) (cw := K.cw) (nl := K.nl) H.hM (H.hRi i hi)
      (fun y hy => (hj'.1 y hy).1) (hLP k hk) (hLP m hm') (fun y hy => by
        rw [em, pg_pc hn hy, pg_pc hn ((hj'.1 y hy).1)])
    rw [← H.hMK j hj, ← H.hMK i hi] at key
    exact hd key.symm
  · exact pairK_spec hn (fun _ he => c_nt_canon H.toHypsC he) H.hS
      (fun t ht => (H.hPts.2 t ht).2) (fun y hy => (hj'.1 y hy).1) hk hp ⟨m, hm', em⟩

theorem c_dcDisjoint_of (H : HypsB D K) :
    dcDisjoint D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = true := by
  have HC := H.toHypsC
  unfold dcDisjoint
  rw [allBelow_iff']
  intro i hi
  rw [allBelow_iff']
  intro j hj
  rw [c_rep_size HC] at hi hj
  rw [Bool.or_eq_true]
  by_cases hij : i < j
  · right
    rw [allBelow_iff']
    intro k hk
    rw [c_nT_size HC] at hk
    have hri := c_rep_perm HC hi
    have hrj := c_rep_perm HC hj
    have ha := c_nt_canon HC hk
    rw [c_repi_get HC hi, c_rep_get HC hj, c_nT_get HC hk, H.hDn, comp_u hri.2 ha,
      comp_u (cc hri.2 ha) hrj.1, Bool.not_eq_true', Bool.eq_false_iff]
    intro hm
    exact c_disj_spec H hi hj hij hk ((c_memN_iff HC (cc (cc hri.2 ha) hrj.1)).1 hm)
  · left
    simpa using hij

theorem c_word_eq (H : HypsC D K) {S : Array Tab} {k : Nat} {PS PSI : Nat → Nat} {wd : List Int}
    {j : Nat} (hj : j < K.kG) (hS : S.size = k ∧ ∀ l < k, S[l]! = unpack K.n K.w (PS l))
    (hp : allN k (fun l => permOK K.n K.w (mask K.w) (K.n * K.w) (PS l) (PSI l)) = true)
    (h : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) PS PSI k wd (K.Gp j) = true) :
    (Certificates.FusD2Perm.wordT D.n S (S.map (invTab D.n)) wd == D.gT[j]!) = true := by
  rw [H.hDn, wordT_u hS hp h, H.hGb j hj]
  exact beq_self_eq_true _

theorem c_gens1 (H : HypsC D K) {r : Nat} (hr : r < K.nr) :
    (nGens D ++ #[(repT D)[r]!]).size = K.kN + 1 ∧ ∀ l < K.kN + 1,
      (nGens D ++ #[(repT D)[r]!])[l]! =
        unpack K.n K.w (nIf(Nat.blt l K.kN, K.NG l, K.REP r)) := by
  have hs : (nGens D).size = K.kN := (c_ngens H).1
  refine ⟨by simp [hs], fun l hl => ?_⟩
  rw [getElem!_pos _ l (by simp [hs]; omega), PK.nIf_eq]
  by_cases h : l < K.kN
  · rw [Array.getElem_append_left (by rw [hs]; exact h),
      ← getElem!_pos (nGens D) l (by rw [hs]; exact h), c_ng_get H h, if_pos (Nat.blt_eq.mpr h)]
  · have hl' : l = K.kN := by omega
    subst hl'
    rw [if_neg (by simp [Nat.blt_eq]), Array.getElem_append_right (by rw [hs])]
    simp [hs, c_rep_get H hr]

theorem c_gens2 (H : HypsC D K) (h2 : 2 < K.nr) :
    ((nGens D ++ #[(repT D)[1]!]) ++ #[(repT D)[2]!]).size = K.kN + 2 ∧ ∀ l < K.kN + 2,
      ((nGens D ++ #[(repT D)[1]!]) ++ #[(repT D)[2]!])[l]! =
        unpack K.n K.w (nIf(Nat.blt l K.kN, K.NG l,
          nIf(Nat.beq l K.kN, K.REP (nat_lit 1), K.REP (nat_lit 2)))) := by
  have h1 := c_gens1 H (r := 1) (by omega)
  have hs1 := h1.1
  have hs2 : ((nGens D ++ #[(repT D)[1]!]) ++ #[(repT D)[2]!]).size = K.kN + 2 := by
    rw [Array.size_append, hs1]
    rfl
  refine ⟨hs2, fun l hl => ?_⟩
  rw [getElem!_pos _ l (by rw [hs2]; exact hl)]
  by_cases h : l < K.kN + 1
  · rw [Array.getElem_append_left (by rw [hs1]; exact h),
      ← getElem!_pos _ l (by rw [hs1]; exact h), h1.2 l h]
    simp only [PK.nIf_eq, Nat.blt_eq, Nat.beq_eq]
    split_ifs <;> first | rfl | omega
  · have hl' : l = K.kN + 1 := by omega
    subst hl'
    rw [Array.getElem_append_right (by rw [hs1])]
    simp only [PK.nIf_eq, Nat.blt_eq, Nat.beq_eq]
    rw [if_neg (by omega), if_neg (by omega), ← c_rep_get H (i := 2) h2]
    simp only [hs1, Nat.sub_self, List.getElem_toArray, List.getElem_cons_zero]

theorem c_gensI1 {r : Nat} (hr : r < (repT D).size) :
    nGensI D ++ #[(repI D)[r]!] = (nGens D ++ #[(repT D)[r]!]).map (invTab D.n) := by
  rw [Array.map_append]
  congr 1
  unfold repI
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_map, ← getElem!_pos (repT D) r hr]
  simp

structure HypsO (D : Data) (K : Pk) (pairW : List (List Int)) : Prop extends HypsB D K where
  hGa : D.genW.length + 2 = D.repW.length
  hGenA : ∀ i < D.genW.length, (D.genW[i]!).length = K.kG ∧ ∀ j < K.kG,
    wordEqK K.n K.w (mask K.w) (pidn K.n K.w) (K.sg (i + 2)) (K.sgi (i + 2)) (K.kN + 1)
      ((D.genW[i]!)[j]!) (K.Gp j) = true
  hPl : pairW.length = K.kG
  hPw : ∀ j < K.kG, wordEqK K.n K.w (mask K.w) (pidn K.n K.w)
      (fun l => nIf(Nat.blt l K.kN, K.NG l, nIf(Nat.beq l K.kN, K.REP (nat_lit 1), K.REP (nat_lit 2))))
      (fun l => nIf(Nat.blt l K.kN, K.NGI l,
        nIf(Nat.beq l K.kN, K.REPI (nat_lit 1), K.REPI (nat_lit 2))))
      (K.kN + 2) (pairW[j]!) (K.Gp j) = true

theorem c_checkOver_of {pairW : List (List Int)} (H : HypsO D K pairW) :
    Certificates.OverD2Perm.checkOver D pairW = true := by
  have HC := H.toHypsC
  have hs : (nGens D).size = K.kN := (c_ngens HC).1
  have hnr : K.nr = D.genW.length + 3 := by rw [H.hRn, ← H.hGa]
  unfold Certificates.OverD2Perm.checkOver Certificates.OverD2Perm.checkOverMax
  dsimp only
  rw [c_checkInv_of HC, c_checkN_of HC, c_invsN HC, fpOK_of (c_fp_inj HC), c_invsRep HC,
    c_dcSum_of H.toHypsB, c_dcDisjoint_of H.toHypsB]
  simp only [Bool.true_and, beq_self_eq_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold Certificates.OverD2Perm.genAfterOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨H.hGa, allBelow_iff'.2 fun i hi => ?_⟩
    have hr : i + 2 + 1 < K.nr := by omega
    obtain ⟨hl, hw⟩ := H.hGenA i hi
    unfold Certificates.OverD2Perm.genOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [hl, H.hGs], allBelow_iff'.2 fun j hj => ?_⟩
    rw [H.hGs] at hj
    rw [c_gensI1 (by rw [c_rep_size HC]; exact hr)]
    have hperm : allN (K.kN + 1) (fun l => permOK K.n K.w (mask K.w) (K.n * K.w)
        (K.sg (i + 2) l) (K.sgi (i + 2) l)) = true := PK.allN_iff.2 fun l hl => by
      unfold Pk.sg Pk.sgi
      by_cases h : l < K.kN
      · rw [PK.nIf_eq, PK.nIf_eq, if_pos (Nat.blt_eq.mpr h), if_pos (Nat.blt_eq.mpr h)]
        exact H.hNI l h
      · rw [PK.nIf_eq, PK.nIf_eq, if_neg (by simp [Nat.blt_eq]; omega),
          if_neg (by simp [Nat.blt_eq]; omega)]
        exact H.hRi _ hr
    exact c_word_eq HC hj (c_gens1 HC hr) hperm (hw j hj)
  · unfold Certificates.OverD2Perm.pairOK Certificates.OverD2Perm.genOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [H.hPl, H.hGs], allBelow_iff'.2 fun j hj => ?_⟩
    rw [H.hGs] at hj
    have h2 : 2 < K.nr := by omega
    have hgi : (nGensI D ++ #[(repI D)[1]!]) ++ #[(repI D)[2]!] =
        ((nGens D ++ #[(repT D)[1]!]) ++ #[(repT D)[2]!]).map (invTab D.n) := by
      rw [Array.map_append, c_gensI1 (by rw [c_rep_size HC]; omega)]
      congr 1
      unfold repI
      rw [getElem!_pos _ 2 (by simp [c_rep_size HC]; omega), Array.getElem_map,
        ← getElem!_pos (repT D) 2 (by rw [c_rep_size HC]; omega)]
      simp
    rw [hgi]
    have hperm : allN (K.kN + 2) (fun l => permOK K.n K.w (mask K.w) (K.n * K.w)
        (nIf(Nat.blt l K.kN, K.NG l, nIf(Nat.beq l K.kN, K.REP (nat_lit 1), K.REP (nat_lit 2))))
        (nIf(Nat.blt l K.kN, K.NGI l,
          nIf(Nat.beq l K.kN, K.REPI (nat_lit 1), K.REPI (nat_lit 2))))) = true :=
      PK.allN_iff.2 fun l hl => by
        simp only [PK.nIf_eq, Nat.blt_eq, Nat.beq_eq]
        split_ifs with h h'
        · exact H.hNI l h
        · exact H.hRi 1 (by omega)
        · exact H.hRi 2 h2
    exact c_word_eq HC hj (c_gens2 HC h2) hperm (H.hPw j hj)

theorem c_rep_notin (H : HypsB D K) {i : Nat} (h0 : 0 < i) (hi : i < K.nr) :
    ¬ ∃ e < K.cnt, K.NT e = K.REP i := by
  have HC := H.toHypsC
  have hn := H.hn
  have hh := H.hNh
  unfold penumHdK at hh
  simp only [PK.bAnd_eq, Bool.and_eq_true] at hh
  have hc0 : 0 < K.cnt := Nat.blt_eq.mp hh.1
  have hT0 : K.NT 0 = pidn K.n K.w := Nat.eq_of_beq_eq_true hh.2.2.1
  have hr := c_rep_perm HC hi
  have h00 := c_rep_perm HC (i := 0) (by omega)
  have hc := cc (cc h00.2 (c_nt_canon HC hc0)) hr.1
  have e : pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (K.REPI 0) (K.NT 0)) (K.REP i) =
      K.REP i := by
    refine u_inj hc hr.1 (tab_ext (size_u _) (size_u _) fun x hx => ?_)
    have hx' := canon_lt hr.1 hx
    rw [get_u hx, get_u hx, pg_pc hn hx, pg_pc hn hx', hT0, pidn_get hn hx',
      c_repi0 HC (by omega) _ hx']
  rintro ⟨m, hm, em⟩
  exact c_disj_spec H (i := 0) (by omega) hi h0 hc0 ⟨m, hm, by rw [e, em]⟩

theorem c_closedOK_of (H : HypsB D K) {i c : Nat} {X : Nat → Nat} (h0 : 0 < i) (hi : i < K.nr)
    (hc : K.CN i = c)
    (hX : ∀ k < K.cnt, closK K.n K.w K.cnt K.NT (K.REP i) (K.REPI i) k (X k) = true) :
    Certificates.OverD2Perm.closedOK D i c = true := by
  have HC := H.toHypsC
  have hn := H.hn
  have hr := c_rep_perm HC hi
  unfold Certificates.OverD2Perm.closedOK
  dsimp only
  have hcnt := c_conjCount_eq HC hi
  rw [if_neg (by omega), hc] at hcnt
  rw [fpOK_of (c_fp_inj HC), c_invsRep HC, hcnt, c_rep_get HC hi, c_repi_get HC hi]
  have hnot : memFp D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (unpack K.n K.w (K.REP i)) = false := by
    rw [Bool.eq_false_iff]
    intro hm
    exact c_rep_notin H h0 hi ((c_memN_iff HC hr.1).1 hm)
  rw [hnot]
  simp only [decide_eq_true_eq, beq_self_eq_true, Bool.not_false, Bool.and_true, Bool.true_and,
    Bool.and_eq_true]
  refine ⟨⟨h0, by rw [H.hRn] at hi; omega⟩, allBelow_iff'.2 fun k hk => ?_⟩
  rw [c_nT_size HC] at hk
  have ha := c_nt_canon HC hk
  have hy := cc (cc hr.1 ha) hr.1
  rw [c_nT_get HC hk, H.hDn, comp_u hr.1 ha, comp_u (cc hr.1 ha) hr.1, Bool.or_eq_true]
  have ht := hX k hk
  unfold closK at ht
  rw [PK.strictB_eq] at ht
  by_cases h1 : Nat.beq (Nat.land (X k) 1) 1 = true
  · have ht' := bif_t h1 ht
    rw [PK.strictB_eq] at ht'
    obtain ⟨he, hq⟩ := band_e ht'
    left
    exact (c_memN_iff HC hy).2 ⟨_, Nat.blt_eq.mp he, Nat.eq_of_beq_eq_true hq⟩
  · have ht' := bif_f (Bool.eq_false_iff.2 h1) ht
    rw [PK.strictB_eq, PK.strictB_eq] at ht'
    obtain ⟨hl, ht'⟩ := band_e ht'
    obtain ⟨he, hq⟩ := band_e ht'
    have hl' := Nat.blt_eq.mp hl
    right
    rw [anyBelow_iff]
    refine ⟨_, by rw [c_nT_size HC]; exact hl', ?_⟩
    have hb := c_nt_canon HC hl'
    rw [getElem!_pos _ _ (by rw [Array.size_map, c_nT_size HC]; exact hl'), Array.getElem_map,
      ← getElem!_pos _ _ (by rw [c_nT_size HC]; exact hl'), c_nT_get HC hl', comp_u hr.2 hb,
      comp_u (cc hr.2 hb) hy]
    exact (c_memN_iff HC (cc (cc hr.2 hb) hy)).2 ⟨_, Nat.blt_eq.mp he, Nat.eq_of_beq_eq_true hq⟩

theorem c_checkClosedPair_of (H : HypsB D K) {c : Nat} {X1 X2 : Nat → Nat} (h2 : 2 < K.nr)
    (hc1 : K.CN 1 = c) (hc2 : K.CN 2 = c)
    (hX1 : ∀ k < K.cnt, closK K.n K.w K.cnt K.NT (K.REP 1) (K.REPI 1) k (X1 k) = true)
    (hX2 : ∀ k < K.cnt, closK K.n K.w K.cnt K.NT (K.REP 2) (K.REPI 2) k (X2 k) = true) :
    Certificates.OverD2Perm.checkClosedPair D c = true := by
  unfold Certificates.OverD2Perm.checkClosedPair
  rw [c_checkInv_of H.toHypsC, c_checkN_of H.toHypsC,
    c_closedOK_of H (by decide) (by omega) hc1 hX1, c_closedOK_of H (by decide) h2 hc2 hX2]
  rfl

end

end CFSG.KS.MaxD2

end
