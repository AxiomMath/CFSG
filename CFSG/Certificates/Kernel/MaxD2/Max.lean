module

public import CFSG.Certificates.Kernel.MaxD2.Sound
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native
open Certificates.MaxD2Perm

theorem foldr_count (f : Nat → Nat) (l : List Nat) :
    l.foldr (fun k s => Nat.add s (Nat.land (f k) 1)) 0 =
      (l.filter fun k => Nat.land (f k) 1 == 1).length := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    have h2 : Nat.land (f k) 1 < 2 := by
      change f k &&& 1 < 2
      rw [Nat.and_one_is_mod]
      omega
    by_cases e : Nat.land (f k) 1 = 1
    · rw [if_pos (by simpa using e), List.length_cons, e]
    · rw [if_neg (by simpa using e), show Nat.land (f k) 1 = 0 by omega]
      rfl

theorem countBelow_true (m : Nat) : countBelow m (fun _ => true) = m := by
  simp [countBelow]

section

variable {D : Data} {K : Pk}

theorem rep_size (H : HypsM D K) : (repT D).size = K.nr := by
  simp [repT, H.hRn]

theorem rep_get (H : HypsM D K) {i : Nat} (hi : i < K.nr) : (repT D)[i]! = unpack K.n K.w (K.REP i) := by
  have hs := rep_size H
  have e : repT D = (idTab D.n :: D.repW.map (wT D)).toArray := by
    simp [repT]
  rw [e, getElem!_pos _ i (by rw [← e, hs]; exact hi)]
  rcases i with _ | j
  · simp [H.hR0, H.hDn, id_u H.hn]
  · have hj : j < D.repW.length := by rw [H.hRn] at hi; omega
    simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_map]
    rw [← getElem!_pos D.repW j hj]
    exact wT_u H (H.hRw j hj)

theorem repi_get (H : HypsM D K) {i : Nat} (hi : i < K.nr) :
    (repI D)[i]! = unpack K.n K.w (K.REPI i) := by
  have hs := rep_size H
  unfold repI
  rw [getElem!_pos _ i (by simpa [hs] using hi), Array.getElem_map,
    ← getElem!_pos (repT D) i (by rw [hs]; exact hi), rep_get H hi, H.hDn, inv_u (H.hRi i hi)]

theorem repi_size (H : HypsM D K) : (repI D).size = K.nr := by simp [repI, rep_size H]

theorem nT_get (H : HypsM D K) {i : Nat} (hi : i < K.cnt) :
    (nEnum D).tabs[i]! = unpack K.n K.w (K.NT i) := by
  rw [(nEnum_eq H).1, rec_get hi]

theorem nT_size (H : HypsM D K) : (nEnum D).tabs.size = K.cnt := by
  rw [(nEnum_eq H).1, rec_size]

theorem fp_inj (H : HypsM D K) :
    ∀ a < (nEnum D).tabs.size, ∀ b < (nEnum D).tabs.size,
      fpTab D.fpPts (nEnum D).tabs[a]! = fpTab D.fpPts (nEnum D).tabs[b]! → a = b := by
  intro a ha b hb e
  rw [nT_size H] at ha hb
  rw [nT_get H ha, nT_get H hb] at e
  exact sort_keyInj H.hS ha hb (fpK_of_fpTab H.hPts e)

theorem memN_iff (H : HypsM D K) {X : Nat} (hX : Cn K.n K.w X) :
    memFp D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts))) ((nEnum D).tabs.map (fpTab D.fpPts))
      (nEnum D).tabs (unpack K.n K.w X) = true ↔ ∃ e < K.cnt, K.NT e = X := by
  rw [memFp_iff (fp_inj H), nT_size H]
  constructor
  · rintro ⟨m, hm, e⟩
    rw [nT_get H hm] at e
    exact ⟨m, hm, u_inj (nt_canon H hm) hX e⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, nT_get H hm⟩

theorem rep_perm (H : HypsM D K) {i : Nat} (hi : i < K.nr) :
    Cn K.n K.w (K.REP i) ∧ Cn K.n K.w (K.REPI i) := perm_canon (H.hRi i hi) H.hn

theorem conjCount_eq (H : HypsM D K) {i : Nat} (hi : i < K.nr) :
    conjCount D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repI D)[i]! (repT D)[i]! =
      if i = 0 then K.cnt else K.CN i := by
  have hn := H.hn
  have hr := rep_perm H hi
  unfold conjCount
  rw [repi_get H hi, rep_get H hi, nT_size H, H.hDn]
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl]
    refine (countBelow_eq (g := fun _ => true) fun k hk => ?_).trans (countBelow_true K.cnt)
    have hq := perm_spec (H.hRi 0 hi)
    rw [H.hR0] at hq
    have hqid : ∀ j < K.n, pg K.w (mask K.w) (K.REPI 0) j = j := fun j hj => by
      have := (hq.1 j hj).2
      rwa [pidn_get hn hj] at this
    have e : comp K.n (comp K.n (unpack K.n K.w (K.REPI 0)) (nEnum D).tabs[k]!)
        (unpack K.n K.w (K.REP 0)) = unpack K.n K.w (K.NT k) := by
      rw [nT_get H hk]
      refine tab_ext (comp_size _ _) (size_u _) fun x hx => ?_
      rw [comp_get hx, H.hR0, get_u hx, pidn_get hn hx, comp_get hx, get_u hx,
        get_u (canon_lt (nt_canon H hk) hx), hqid _ (canon_lt (nt_canon H hk) hx)]
    rw [e, memN_iff H (nt_canon H hk)]
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
    have hspec := testK_spec hn (fun e he => nt_canon H he) H.hS (fun t ht => (H.hPts.2 t ht).2)
      (H.hRi i hi) (fun t ht => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 hrb) t ht)) hk hk'
    have ha := nt_canon H hk
    rw [nT_get H hk, comp_u hr.2 ha, comp_u (cc hr.2 ha) hr.1, Bool.eq_iff_iff,
      memN_iff H (cc (cc hr.2 ha) hr.1), hspec, beq_iff_eq]

theorem foldl_congr_range {f g : Nat → Nat → Nat} {m : Nat} (h : ∀ s, ∀ i < m, f s i = g s i)
    (s : Nat) : (List.range m).foldl f s = (List.range m).foldl g s :=
  List.foldl_ext f g s fun a b hb => h a b (List.mem_range.1 hb)

theorem dcSum_of (H : HypsM D K) :
    dcSum D.n D.nOrder D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = D.gOrder := by
  unfold dcSum
  rw [← H.hSum, rep_size H]
  refine foldl_congr_range (fun s i hi => ?_) 0
  rw [conjCount_eq H hi]

theorem dcDisjoint_of (H : HypsM D K) :
    dcDisjoint D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = true := by
  have hn := H.hn
  have hLP := enum_facts hn H.hNh H.hNp H.hNI H.hL
  unfold dcDisjoint
  rw [allBelow_iff']
  intro i hi
  rw [allBelow_iff']
  intro j hj
  rw [rep_size H] at hi hj
  rw [Bool.or_eq_true]
  by_cases hij : i < j
  · right
    rw [allBelow_iff']
    intro k hk
    rw [nT_size H] at hk
    have hri := rep_perm H hi
    have hrj := rep_perm H hj
    have ha := nt_canon H hk
    rw [repi_get H hi, rep_get H hj, nT_get H hk, H.hDn, comp_u hri.2 ha, comp_u (cc hri.2 ha) hrj.1,
      Bool.not_eq_true', Bool.eq_false_iff]
    intro hm
    obtain ⟨m, hm', em⟩ := (memN_iff H (cc (cc hri.2 ha) hrj.1)).1 hm
    have hj' := perm_spec (H.hRi j hj)
    rcases H.hMd i hi j hj hij with hd | hp
    · have key := mkey_eq hn (hi := K.hi) (cw := K.cw) (nl := K.nl) H.hM (H.hRi i hi)
        (fun y hy => (hj'.1 y hy).1) (hLP k hk) (hLP m hm') (fun y hy => by
          rw [em, pg_pc hn hy, pg_pc hn ((hj'.1 y hy).1)])
      rw [← H.hMK j hj, ← H.hMK i hi] at key
      exact hd key.symm
    · exact pairK_spec hn (fun e he => nt_canon H he) H.hS (fun t ht => (H.hPts.2 t ht).2)
        (fun y hy => (hj'.1 y hy).1) hk hp ⟨m, hm', em⟩
  · left
    simpa using hij

theorem gens_append (H : HypsM D K) {i : Nat} (hi : i < D.repW.length) :
    (nGens D ++ #[(repT D)[i + 1]!]).size = K.kN + 1 ∧ ∀ l < K.kN + 1,
      (nGens D ++ #[(repT D)[i + 1]!])[l]! = unpack K.n K.w (K.sg i l) := by
  have hs : (nGens D).size = K.kN := (ngens H).1
  have hi1 : i + 1 < K.nr := by rw [H.hRn]; omega
  refine ⟨by simp [hs], fun l hl => ?_⟩
  unfold Pk.sg
  rw [getElem!_pos _ l (by simp [hs]; omega)]
  by_cases h : l < K.kN
  · rw [Array.getElem_append_left (by rw [hs]; exact h), ← getElem!_pos (nGens D) l (by rw [hs]; exact h),
      ng_get H h, PK.nIf_eq, if_pos (Nat.blt_eq.mpr h)]
  · have hl' : l = K.kN := by omega
    subst hl'
    rw [PK.nIf_eq, if_neg (by simp [Nat.blt_eq]), Array.getElem_append_right (by rw [hs])]
    simp [hs, rep_get H hi1]

theorem dcGenerate_of (H : HypsM D K) : dcGenerate D (repT D) (repI D) = true := by
  have hs : (nGens D).size = K.kN := (ngens H).1
  unfold dcGenerate
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨H.hGl, allBelow_iff'.2 fun i hi => ?_⟩
  have hi1 : i + 1 < K.nr := by rw [H.hRn]; omega
  obtain ⟨hl, hw⟩ := H.hGen i hi
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [hl, H.hGs], allBelow_iff'.2 fun j hj => ?_⟩
  rw [H.hGs] at hj
  have hgi : nGensI D ++ #[(repI D)[i + 1]!] =
      (nGens D ++ #[(repT D)[i + 1]!]).map (invTab D.n) := by
    rw [Array.map_append]
    congr 1
    unfold repI
    rw [getElem!_pos _ (i + 1) (by simp [rep_size H]; exact hi1), Array.getElem_map,
      ← getElem!_pos (repT D) (i + 1) (by rw [rep_size H]; exact hi1)]
    simp
  have hperm : allN (K.kN + 1) (fun l => permOK K.n K.w (mask K.w) (K.n * K.w) (K.sg i l)
      (K.sgi i l)) = true := PK.allN_iff.2 fun l hl => by
    unfold Pk.sg Pk.sgi
    by_cases h : l < K.kN
    · rw [PK.nIf_eq, PK.nIf_eq, if_pos (Nat.blt_eq.mpr h), if_pos (Nat.blt_eq.mpr h)]
      exact H.hNI l h
    · rw [PK.nIf_eq, PK.nIf_eq, if_neg (by simp [Nat.blt_eq]; omega),
        if_neg (by simp [Nat.blt_eq]; omega)]
      exact H.hRi _ hi1
  rw [hgi, H.hDn, wordT_u (gens_append H hi) hperm (hw j hj), H.hGb j hj]
  exact beq_self_eq_true _

theorem checkMax_of (H : HypsM D K) : checkMax D = true := by
  unfold checkMax
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨fpOK_of (fp_inj H), ?_⟩, dcSum_of H⟩, dcDisjoint_of H⟩, dcGenerate_of H⟩
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [repi_size H, rep_size H], allBelow_iff'.2 fun k hk => ?_⟩
  rw [rep_size H] at hk
  rw [repi_get H hk, rep_get H hk, H.hDn, inv_comp (H.hRi k hk)]
  simp [size_u]

theorem check_of (H : Hyps D K) : check D = true := by
  unfold check
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨checkInv_of H.toM, checkR_of H⟩, checkN_of H.toM⟩, checkNormal_of H⟩,
    checkMoves_of H⟩, checkTorus_of H⟩, checkCent_of H⟩, checkMax_of H.toM⟩

end

end CFSG.KS.MaxD2

end
