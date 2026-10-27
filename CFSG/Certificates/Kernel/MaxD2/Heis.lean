module

public import CFSG.Certificates.Kernel.MaxD2.DcCount

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis
open CFSG.ComponentClassification.PSL3Four (exists_getElem!_of_mem getElem!_mem)

theorem anyZ_iff {nz : Nat} {RT ZP : Nat → Nat} {f : Nat → Bool} :
    anyZ nz RT ZP f = true ↔ ∃ j < nz, f (RT (ZP j)) = true := by
  unfold anyZ
  cases h : allN nz (fun j => bIf(f (RT (ZP j)), false, true))
  · refine ⟨fun _ => ?_, fun _ => rfl⟩
    by_contra hne
    have hall : allN nz (fun j => bIf(f (RT (ZP j)), false, true)) = true :=
      PK.allN_iff.2 fun j hj => by
        cases e : f (RT (ZP j))
        · rfl
        · exact absurd ⟨j, hj, e⟩ hne
    rw [h] at hall
    exact absurd hall (by decide)
  · refine ⟨fun e => absurd e (by decide), fun ⟨j, hj, e⟩ => ?_⟩
    have := (PK.allN_iff.1 h) j hj
    rw [e] at this
    exact absurd this (by decide)

theorem zK_spec {n w rcnt nz U V : Nat} {RT ZP ZX : Nat → Nat}
    (h : zK n w rcnt nz RT ZP ZX U V = true) :
    (∀ r < rcnt, commUVK n w U V (RT r) = true → 0 < ZX r ∧ ZX r ≤ nz ∧ ZP (ZX r - 1) = r) ∧
      ∀ j < nz, ZP j < rcnt ∧ ZX (ZP j) = j + 1 ∧ commUVK n w U V (RT (ZP j)) = true := by
  unfold zK at h
  obtain ⟨h1, h2⟩ := band_e h
  have p1 : ∀ r < rcnt, commUVK n w U V (RT r) = true →
      0 < ZX r ∧ ZX r ≤ nz ∧ ZP (ZX r - 1) = r := fun r hr hc => by
    have e := (PK.allN_iff.1 h1) r hr
    rw [PK.strictB_eq] at e
    have e' := bif_t hc e
    obtain ⟨a, e'⟩ := band_e e'
    obtain ⟨b, c⟩ := band_e e'
    exact ⟨Nat.blt_eq.mp a, Nat.ble_eq.mp b, Nat.eq_of_beq_eq_true c⟩
  refine ⟨p1, fun j hj => ?_⟩
  have e := (PK.allN_iff.1 h2) j hj
  rw [PK.strictB_eq] at e
  obtain ⟨a, b⟩ := band_e e
  have hr := Nat.blt_eq.mp a
  have hx : ZX (ZP j) = j + 1 := Nat.eq_of_beq_eq_true b
  refine ⟨hr, hx, ?_⟩
  cases hc : commUVK n w U V (RT (ZP j))
  · have e2 := (PK.allN_iff.1 h1) (ZP j) hr
    rw [PK.strictB_eq] at e2
    have e3 := Nat.eq_of_beq_eq_true (bif_f hc e2)
    omega
  · rfl

theorem commK_spec {n w rcnt nz k l : Nat} {RT ZP CZ : Nat → Nat}
    (h : commK n w rcnt nz RT ZP CZ k l = true) :
    (∃ a < nz, pcomp n w (mask w) (RT k) (RT l) =
      pcomp n w (mask w) (RT (ZP a)) (pcomp n w (mask w) (RT l) (RT k))) ∧
    ∃ b < nz, pcomp n w (mask w) (RT l) (RT k) =
      pcomp n w (mask w) (RT (ZP b)) (pcomp n w (mask w) (RT k) (RT l)) := by
  unfold commK at h
  simp only [PK.strictB_eq] at h
  obtain ⟨a, h⟩ := band_e h
  obtain ⟨b, h⟩ := band_e h
  obtain ⟨c, d⟩ := band_e h
  exact ⟨⟨_, Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true c⟩, ⟨_, Nat.blt_eq.mp b, Nat.eq_of_beq_eq_true d⟩⟩

theorem comm_u {n w U V x : Nat} (hU : Cn n w U) (hV : Cn n w V) (hx : Cn n w x) :
    commutesUV n (unpack n w U) (unpack n w V) (unpack n w x) = commUVK n w U V x := by
  unfold commutesUV commUVK
  rw [comp_u hx hU, comp_u hU hx, comp_u hx hV, comp_u hV hx, eq_u (cc hx hU) (cc hU hx),
    eq_u (cc hx hV) (cc hV hx), PK.bAnd_eq]

section

variable {D : Data} {K : Pk}

theorem cc_dcGenerate_of (H : HypsC D K) (hGl : D.genW.length = D.repW.length)
    (hGen : ∀ i < D.repW.length, (D.genW[i]!).length = K.kG ∧ ∀ j < K.kG,
      wordEqK K.n K.w (mask K.w) (pidn K.n K.w) (K.sg i) (K.sgi i) (K.kN + 1) ((D.genW[i]!)[j]!)
        (K.Gp j) = true) :
    dcGenerate D (repT D) (repI D) = true := by
  unfold dcGenerate
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hGl, allBelow_iff'.2 fun i hi => ?_⟩
  have hi1 : i + 1 < K.nr := by rw [H.hRn]; omega
  obtain ⟨hl, hw⟩ := hGen i hi
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by rw [hl, H.hGs], allBelow_iff'.2 fun j hj => ?_⟩
  rw [H.hGs] at hj
  rw [c_gensI1 (by rw [c_rep_size H]; exact hi1)]
  have hperm : allN (K.kN + 1) (fun l => permOK K.n K.w (mask K.w) (K.n * K.w) (K.sg i l)
      (K.sgi i l)) = true := PK.allN_iff.2 fun l hl => by
    unfold Pk.sg Pk.sgi
    by_cases h : l < K.kN
    · rw [PK.nIf_eq, PK.nIf_eq, if_pos (Nat.blt_eq.mpr h), if_pos (Nat.blt_eq.mpr h)]
      exact H.hNI l h
    · rw [PK.nIf_eq, PK.nIf_eq, if_neg (by simp [Nat.blt_eq]; omega),
        if_neg (by simp [Nat.blt_eq]; omega)]
      exact H.hRi _ hi1
  exact c_word_eq H hj (c_gens1 H hi1) hperm (hw j hj)

theorem cc_checkMax_of (H : HypsBC D K) (hGl : D.genW.length = D.repW.length)
    (hGen : ∀ i < D.repW.length, (D.genW[i]!).length = K.kG ∧ ∀ j < K.kG,
      wordEqK K.n K.w (mask K.w) (pidn K.n K.w) (K.sg i) (K.sgi i) (K.kN + 1) ((D.genW[i]!)[j]!)
        (K.Gp j) = true) :
    checkMax D = true := by
  have HC := H.toHypsC
  unfold checkMax
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨fpOK_of (c_fp_inj HC), c_invsRep HC⟩, by rw [cc_dcSum_of H]; exact beq_self_eq_true _⟩,
    cc_dcDisjoint_of H⟩, cc_dcGenerate_of HC hGl hGen⟩

end

structure HypsH (D : Data) (K : Pk) (ZP ZX CZ : Nat → Nat) : Prop extends HypsBC D K where
  hRG : ∀ j < 2, wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG ((rWs D)[j]!) (K.RG j) =
    true ∧ Cn K.n K.w (K.RG j)
  hRh : penumHdK (pidn K.n K.w) K.rcnt (D.p ^ 3) K.RT K.RPL = true
  hRp : ∀ i < K.rcnt, penumPtK K.n K.w (mask K.w) (K.n * K.w) false K.RG K.RGI 2 K.rcnt K.RT K.RPL
    K.RPOS K.RSRT K.RSRI i = true
  hRc : K.rcnt = D.p ^ 3
  hNorm : ∀ j < K.kN, ∀ i < 2,
    conjInK K.n K.w K.rcnt K.RT (K.NG j) (K.NGI j) (K.RG i) (r32 K.NH (4 * j + 2 * i)) = true ∧
    conjInK K.n K.w K.rcnt K.RT (K.NGI j) (K.NG j) (K.RG i) (r32 K.NH (4 * j + 2 * i + 1)) = true
  hMj : K.mj < K.kG
  hMi : K.mi < 2
  hMv : notInK K.rcnt K.RT
    (pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (K.Gp K.mj) (K.RG K.mi)) (K.GIp K.mj)) = true
  hZ : zK K.n K.w K.rcnt D.p K.RT ZP ZX (K.RG 0) (K.RG 1) = true
  hUV : bIf(Nat.beq (pcomp K.n K.w (mask K.w) (K.RG 0) (K.RG 1))
    (pcomp K.n K.w (mask K.w) (K.RG 1) (K.RG 0)), false, true) = true
  hExp : allN K.rcnt (fun k => Nat.beq (pw K.n K.w (K.RT k) D.p) (pidn K.n K.w)) = true
  hComm : ∀ k < K.rcnt, ∀ l < k + 1, commK K.n K.w K.rcnt D.p K.RT ZP CZ k l = true
  hTw : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG D.tW K.TP = true
  hTp : permOK K.n K.w (mask K.w) (K.n * K.w) K.TP K.TPI = true
  hTh : K.th < K.cnt
  hTn : K.NT K.th = K.TP
  hTk : torusHK K.n K.w D.p K.rcnt D.p D.tm D.tlam D.te K.RT ZP (K.RG 0) (K.RG 1) K.TP K.TPI = true
  hC : ∀ k < K.cnt, centK K.n K.w K.rcnt K.NT K.RT (K.RG 0) (K.RG 1) (r32 K.CH k) k = true
  hGl : D.genW.length = D.repW.length
  hGen : ∀ i < D.repW.length, (D.genW[i]!).length = K.kG ∧ ∀ j < K.kG,
    wordEqK K.n K.w (mask K.w) (pidn K.n K.w) (K.sg i) (K.sgi i) (K.kN + 1) ((D.genW[i]!)[j]!)
      (K.Gp j) = true

section

variable {D : Data} {K : Pk} {ZP ZX CZ : Nat → Nat}

theorem h_rgens (H : HypsH D K ZP ZX CZ) : GensOK K.n K.w 2 K.RG (rGens D) := by
  refine ⟨by simp [rGens, rWs], fun j hj => ⟨?_, (H.hRG j hj).2⟩⟩
  unfold rGens
  rw [map_get _ (by simpa [rWs] using hj), c_wT_u H.toHypsC (H.hRG j hj).1]

theorem h_rEnum_eq (H : HypsH D K ZP ZX CZ) :
    hrEnum D = penumRec K.n K.w K.rcnt K.RT K.RPL ∧
      enumOK K.n (rGens D) (penumRec K.n K.w K.rcnt K.RT K.RPL) = true := by
  unfold hrEnum
  rw [H.hDn]
  exact penumK_left_sound H.hn (h_rgens H) H.hRh H.hRp

theorem h_rt_canon (H : HypsH D K ZP ZX CZ) {i : Nat} (hi : i < K.rcnt) : Cn K.n K.w (K.RT i) :=
  (pt_spec (H.hRp i hi)).1

theorem h_rg_get (H : HypsH D K ZP ZX CZ) {j : Nat} (hj : j < 2) :
    (rGens D)[j]! = unpack K.n K.w (K.RG j) :=
  ((h_rgens H).2 j hj).1

theorem h_rg_canon (H : HypsH D K ZP ZX CZ) {j : Nat} (hj : j < 2) : Cn K.n K.w (K.RG j) :=
  (H.hRG j hj).2

theorem h_foundR (H : HypsH D K ZP ZX CZ) {X : Nat} (hX : Cn K.n K.w X) :
    found (indexOf (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs) (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs
      (unpack K.n K.w X) = true ↔ ∃ i < K.rcnt, K.RT i = X := by
  rw [found_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    exact ⟨i, hi, u_inj (h_rt_canon H hi) hX e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [rec_size]; exact hi, rec_get hi⟩

theorem c_foundN (H : HypsC D K) {X : Nat} (hX : Cn K.n K.w X) :
    found (indexOf (penumRec K.n K.w K.cnt K.NT K.NPL).tabs) (penumRec K.n K.w K.cnt K.NT K.NPL).tabs
      (unpack K.n K.w X) = true ↔ ∃ i < K.cnt, K.NT i = X := by
  rw [found_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    exact ⟨i, hi, u_inj (c_nt_canon H hi) hX e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [rec_size]; exact hi, rec_get hi⟩

theorem h_zT_eq (H : HypsH D K ZP ZX CZ) :
    zTabs D = (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs.filter
      (commutesUV K.n (unpack K.n K.w (K.RG 0)) (unpack K.n K.w (K.RG 1))) := by
  unfold zTabs
  rw [(h_rEnum_eq H).1, h_rg_get H (by decide : 0 < 2), h_rg_get H (by decide : 1 < 2), H.hDn]

theorem h_mem_zT (H : HypsH D K ZP ZX CZ) {x : Tab} :
    x ∈ (zTabs D).toList ↔ ∃ j < D.p, x = unpack K.n K.w (K.RT (ZP j)) := by
  obtain ⟨z1, z2⟩ := zK_spec H.hZ
  have hu := h_rg_canon H (by decide : 0 < 2)
  have hv := h_rg_canon H (by decide : 1 < 2)
  rw [h_zT_eq H, Array.toList_filter, List.mem_filter]
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨r, hr, rfl⟩ := exists_getElem!_of_mem hx
    rw [rec_size] at hr
    rw [rec_get hr, comm_u hu hv (h_rt_canon H hr)] at hc
    obtain ⟨a, b, c⟩ := z1 r hr hc
    refine ⟨ZX r - 1, by omega, ?_⟩
    rw [rec_get hr, c]
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨a, -, c⟩ := z2 j hj
    have hm := getElem!_mem (T := (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs)
      (k := ZP j) (by rw [rec_size]; exact a)
    rw [rec_get a] at hm
    exact ⟨hm, by rw [comm_u hu hv (h_rt_canon H a)]; exact c⟩

theorem h_zT_any (H : HypsH D K ZP ZX CZ) (f : Tab → Bool) :
    anyBelow (zTabs D).size (fun j => f (zTabs D)[j]!) = true ↔
      ∃ j < D.p, f (unpack K.n K.w (K.RT (ZP j))) = true := by
  rw [anyBelow_iff]
  constructor
  · rintro ⟨j, hj, e⟩
    obtain ⟨j', hj', e'⟩ := (h_mem_zT H).1 (getElem!_mem hj)
    exact ⟨j', hj', by rw [← e']; exact e⟩
  · rintro ⟨j, hj, e⟩
    obtain ⟨k, hk, e'⟩ := exists_getElem!_of_mem ((h_mem_zT H).2 ⟨j, hj, rfl⟩)
    exact ⟨k, hk, by rw [e']; exact e⟩

theorem h_zT_all (H : HypsH D K ZP ZX CZ) (f : Tab → Bool) :
    allBelow (zTabs D).size (fun j => f (zTabs D)[j]!) = true ↔
      ∀ j < D.p, f (unpack K.n K.w (K.RT (ZP j))) = true := by
  rw [allBelow_iff']
  constructor
  · intro h j hj
    obtain ⟨k, hk, e'⟩ := exists_getElem!_of_mem ((h_mem_zT H).2 ⟨j, hj, rfl⟩)
    rw [← e']
    exact h k hk
  · intro h k hk
    obtain ⟨j', hj', e'⟩ := (h_mem_zT H).1 (getElem!_mem hk)
    rw [e']
    exact h j' hj'

theorem h_zT_size (H : HypsH D K ZP ZX CZ) : (zTabs D).size = D.p := by
  obtain ⟨z1, z2⟩ := zK_spec H.hZ
  have hu := h_rg_canon H (by decide : 0 < 2)
  have hv := h_rg_canon H (by decide : 1 < 2)
  rw [h_zT_eq H, ← Array.length_toList, Array.toList_filter, ← countBelow_tabs, rec_size,
    countBelow_eq (g := fun r => commUVK K.n K.w (K.RG 0) (K.RG 1) (K.RT r)) fun r hr => by
      rw [rec_get hr, comm_u hu hv (h_rt_canon H hr)],
    CFSG.ComponentClassification.PSL3Four.countBelow_eq]
  rw [← Finset.card_range D.p]
  refine Finset.card_nbij' (fun r => ZX r - 1) ZP (fun r hr => ?_) (fun j hj => ?_)
    (fun r hr => ?_) (fun j hj => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr ⊢
    have := z1 r hr.1 hr.2
    omega
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨a, -, c⟩ := z2 j hj
    exact ⟨a, c⟩
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
    exact (z1 r hr.1 hr.2).2.2
  · simp only [Finset.mem_coe, Finset.mem_range] at hj
    change ZX (ZP j) - 1 = j
    rw [(z2 j hj).2.1]
    omega

theorem checkHR_of (H : HypsH D K ZP ZX CZ) : checkHR D = true := by
  obtain ⟨e, hok⟩ := h_rEnum_eq H
  unfold checkHR
  rw [e, H.hDn, hok, rec_size, H.hRc]
  simp

theorem h_conjIn_spec (H : HypsH D K ZP ZX CZ) {g gi x h : Nat} (hg : Cn K.n K.w g)
    (hgi : Cn K.n K.w gi) (hx : Cn K.n K.w x) (hk : conjInK K.n K.w K.rcnt K.RT g gi x h = true) :
    found (indexOf (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs) (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs
      (conjTab K.n (unpack K.n K.w g) (unpack K.n K.w gi) (unpack K.n K.w x)) = true := by
  unfold conjTab
  rw [comp_u hg hx, comp_u (cc hg hx) hgi, h_foundR H (cc (cc hg hx) hgi)]
  unfold conjInK at hk
  obtain ⟨h1, h2⟩ := band_e hk
  exact ⟨h, Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem checkHNormal_of (H : HypsH D K ZP ZX CZ) : checkHNormal D = true := by
  obtain ⟨e, -⟩ := h_rEnum_eq H
  unfold checkHNormal normalOK
  rw [e, H.hDn]
  have hs : (nGens D).size = K.kN := (c_ngens H.toHypsC).1
  have hr : (rGens D).size = 2 := (h_rgens H).1
  simp only [Bool.and_eq_true]
  refine ⟨by rw [← H.hDn]; exact c_invsN H.toHypsC, ?_⟩
  rw [allBelow_iff']
  intro j hj
  rw [hs] at hj
  rw [allBelow_iff']
  intro i hi
  rw [hr] at hi
  rw [c_ng_get H.toHypsC hj, c_ngi_get H.toHypsC hj, h_rg_get H hi]
  have hc := perm_canon (H.hNI j hj) H.hn
  have hx := h_rg_canon H hi
  simp only [Bool.and_eq_true]
  exact ⟨h_conjIn_spec H hc.1 hc.2 hx (H.hNorm j hj i hi).1,
    h_conjIn_spec H hc.2 hc.1 hx (H.hNorm j hj i hi).2⟩

theorem checkHMoves_of (H : HypsH D K ZP ZX CZ) : checkHMoves D = true := by
  obtain ⟨e, -⟩ := h_rEnum_eq H
  unfold checkHMoves
  simp only []
  rw [e, anyBelow_iff]
  refine ⟨K.mj, by rw [H.hGs]; exact H.hMj, ?_⟩
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, allBelow_iff']
  intro hall
  have hr : (rGens D).size = 2 := (h_rgens H).1
  have h := hall K.mi (by rw [hr]; exact H.hMi)
  have hgp := perm_canon (c_gp_perm H.toHypsC H.hMj) H.hn
  have hx := h_rg_canon H H.hMi
  rw [H.hGb _ H.hMj, c_gi_u H.toHypsC H.hMj, h_rg_get H H.hMi, H.hDn] at h
  unfold conjTab at h
  rw [comp_u hgp.1 hx, comp_u (cc hgp.1 hx) hgp.2, h_foundR H (cc (cc hgp.1 hx) hgp.2)] at h
  obtain ⟨r, hr', er⟩ := h
  have hm := (PK.allN_iff.1 H.hMv) r hr'
  rw [er, Nat.beq_refl] at hm
  exact absurd hm (by decide)

theorem checkHZ_of (H : HypsH D K ZP ZX CZ) : checkHZ D = true := by
  unfold checkHZ
  rw [h_zT_size H]
  exact beq_self_eq_true _

theorem checkHExp_of (H : HypsH D K ZP ZX CZ) : checkHExp D = true := by
  obtain ⟨e, -⟩ := h_rEnum_eq H
  have hn := H.hn
  unfold checkHExp
  simp only [e, H.hDn, rec_size]
  rw [allBelow_iff']
  intro k hk
  have hr := h_rt_canon H hk
  rw [rec_get hk, powT_u hn hr, id_u hn, eq_u (pw_canon hn hr _) (pidn_canon hn)]
  exact (PK.allN_iff.1 H.hExp) k hk

theorem checkHComm_of (H : HypsH D K ZP ZX CZ) : checkHComm D = true := by
  obtain ⟨e, -⟩ := h_rEnum_eq H
  have hu := h_rg_canon H (by decide : 0 < 2)
  have hv := h_rg_canon H (by decide : 1 < 2)
  unfold checkHComm
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [h_rg_get H (by decide : 0 < 2), h_rg_get H (by decide : 1 < 2), H.hDn, comp_u hu hv,
      comp_u hv hu, bne, eq_u (cc hu hv) (cc hv hu)]
    have h := H.hUV
    cases c : Nat.beq (pcomp K.n K.w (mask K.w) (K.RG 0) (K.RG 1))
      (pcomp K.n K.w (mask K.w) (K.RG 1) (K.RG 0))
    · rfl
    · rw [c] at h
      exact absurd h (by decide)
  · rw [allBelow_iff']
    intro k hk
    rw [allBelow_iff']
    intro l hl
    rw [e, rec_size] at hk hl
    have hk' := h_rt_canon H hk
    have hl' := h_rt_canon H hl
    rw [e, rec_get hk, rec_get hl, H.hDn, comp_u hk' hl', comp_u hl' hk']
    refine (h_zT_any H (fun z => unpack K.n K.w (pcomp K.n K.w (mask K.w) (K.RT k) (K.RT l)) ==
      comp K.n z (unpack K.n K.w (pcomp K.n K.w (mask K.w) (K.RT l) (K.RT k))))).2 ?_
    have key : ∃ a < D.p, pcomp K.n K.w (mask K.w) (K.RT k) (K.RT l) =
        pcomp K.n K.w (mask K.w) (K.RT (ZP a)) (pcomp K.n K.w (mask K.w) (K.RT l) (K.RT k)) := by
      by_cases hlk : l < k + 1
      · exact (commK_spec (H.hComm k hk l hlk)).1
      · exact (commK_spec (H.hComm l hl k (by omega))).2
    obtain ⟨a, ha, ea⟩ := key
    obtain ⟨hza, -, -⟩ := (zK_spec H.hZ).2 a ha
    have hz := h_rt_canon H hza
    refine ⟨a, ha, ?_⟩
    rw [comp_u hz (cc hl' hk'), eq_u (cc hk' hl') (cc hz (cc hl' hk')), ea, Nat.beq_refl]

theorem checkHTorus_of (H : HypsH D K ZP ZX CZ) : checkHTorus D = true := by
  obtain ⟨eR, -⟩ := h_rEnum_eq H
  obtain ⟨eN, -⟩ := c_nEnum_eq H.toHypsC
  have hT := perm_canon H.hTp H.hn
  have hn := H.hn
  have hu := h_rg_canon H (by decide : 0 < 2)
  have hv := h_rg_canon H (by decide : 1 < 2)
  have hk := H.hTk
  unfold torusHK at hk
  simp only [PK.strictB_eq] at hk
  obtain ⟨k1, hk⟩ := band_e hk
  obtain ⟨k2, k3⟩ := band_e hk
  have pa := pw_canon hn hT.1
  have pb := pw_canon hn hT.2
  unfold checkHTorus
  simp only [Bool.and_eq_true]
  rw [eN, c_wT_u H.toHypsC H.hTw, H.hDn, inv_u H.hTp]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [size_u]
  · rw [inv_comp H.hTp]
    exact beq_self_eq_true _
  · rw [c_foundN H.toHypsC hT.1]
    exact ⟨K.th, H.hTh, H.hTn⟩
  · rw [allBelow_iff']
    intro k hk
    rw [eR, rec_size] at hk
    have e := (PK.allN_iff.1 k1) k hk
    have hr := h_rt_canon H hk
    rw [eR, rec_get hk, powT_u hn hT.1, powT_u hn hT.2, powT_u hn hr, comp_u (pa _) hr,
      comp_u (cc (pa _) hr) (pb _)]
    refine (h_zT_any H (fun z => unpack K.n K.w (pcomp K.n K.w (mask K.w)
      (pcomp K.n K.w (mask K.w) (pw K.n K.w K.TP D.tm) (K.RT k)) (pw K.n K.w K.TPI D.tm)) ==
        comp K.n (unpack K.n K.w (pw K.n K.w (K.RT k) D.tlam)) z)).2 ?_
    obtain ⟨j, hj, ej⟩ := anyZ_iff.1 e
    refine ⟨j, hj, ?_⟩
    have hz := h_rt_canon H ((zK_spec H.hZ).2 j hj).1
    rw [comp_u (pw_canon hn hr _) hz, eq_u (cc (cc (pa _) hr) (pb _)) (cc (pw_canon hn hr _) hz)]
    exact ej
  · rw [allBelow_iff']
    intro k hk
    rw [eR, rec_size] at hk
    have e := (PK.allN_iff.1 k2) k hk
    have hr := h_rt_canon H hk
    rw [eR, rec_get hk, powT_u hn hT.1, powT_u hn hT.2, comp_u (pa _) hr,
      comp_u (cc (pa _) hr) (pb _), comp_u (cc (cc (pa _) hr) (pb _)) hr]
    refine (h_zT_any H (fun z => unpack K.n K.w (pcomp K.n K.w (mask K.w)
      (pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (pw K.n K.w K.TP D.te) (K.RT k))
        (pw K.n K.w K.TPI D.te)) (K.RT k)) == z)).2 ?_
    obtain ⟨j, hj, ej⟩ := anyZ_iff.1 e
    refine ⟨j, hj, ?_⟩
    have hz := h_rt_canon H ((zK_spec H.hZ).2 j hj).1
    rw [eq_u (cc (cc (cc (pa _) hr) (pb _)) hr) hz]
    exact ej
  · rw [allBelow_iff']
    intro k hk
    rw [allBelow_iff']
    intro i hi
    rw [eR, rec_size] at hi
    have e := (PK.allN_iff.1 ((PK.allN_iff.1 k3) k hk)) i hi
    have hr := h_rt_canon H hi
    rw [Bool.or_eq_true]
    by_cases hc : commUVK K.n K.w (K.RG 0) (K.RG 1) (K.RT i) = true
    · left
      rw [Array.contains_iff_mem, ← Array.mem_toList_iff, h_mem_zT H, eR, rec_get hi]
      obtain ⟨a, b, c⟩ := (zK_spec H.hZ).1 i hi hc
      exact ⟨ZX i - 1, by omega, by rw [c]⟩
    · right
      have e' := bif_f (Bool.eq_false_iff.2 hc) e
      rw [allBelow_iff']
      intro j hj
      have e2 := (PK.allN_iff.1 e') j hj
      rw [eR, rec_get hi, powT_u hn hT.1, powT_u hn hT.2, powT_u hn hr, comp_u (pa _) hr,
        comp_u (cc (pa _) hr) (pb _)]
      refine (h_zT_all H (fun z => !(unpack K.n K.w (pcomp K.n K.w (mask K.w)
        (pcomp K.n K.w (mask K.w) (pw K.n K.w K.TP (k + 1)) (K.RT i)) (pw K.n K.w K.TPI (k + 1))) ==
          comp K.n (unpack K.n K.w (pw K.n K.w (K.RT i) j)) z))).2 fun l hl => ?_
      have e3 := bnot_e ((PK.allN_iff.1 e2) l hl)
      have hz := h_rt_canon H ((zK_spec H.hZ).2 l hl).1
      rw [comp_u (pw_canon hn hr _) hz, eq_u (cc (cc (pa _) hr) (pb _)) (cc (pw_canon hn hr _) hz),
        Bool.not_eq_true']
      exact e3

theorem checkHCent_of (H : HypsH D K ZP ZX CZ) : checkHCent D = true := by
  obtain ⟨eR, -⟩ := h_rEnum_eq H
  obtain ⟨eN, -⟩ := c_nEnum_eq H.toHypsC
  have hn := H.hn
  unfold checkHCent commutesUV
  simp only [eR, eN, H.hDn, rec_size]
  rw [allBelow_iff']
  intro k hk
  have hc := H.hC k hk
  have ha := c_nt_canon H.toHypsC hk
  have hu := h_rg_canon H (by decide : 0 < 2)
  have hv := h_rg_canon H (by decide : 1 < 2)
  rw [rec_get hk, h_rg_get H (by decide : 0 < 2), h_rg_get H (by decide : 1 < 2),
    comp_u ha hu, comp_u hu ha, comp_u ha hv, comp_u hv ha, eq_u (cc ha hu) (cc hu ha),
    eq_u (cc ha hv) (cc hv ha), Bool.or_eq_true]
  unfold centK at hc
  rw [PK.strictB_eq] at hc
  by_cases h1 : Nat.beq (Nat.land (r32 K.CH k) 1) 1 = true
  · have h := bif_t h1 hc
    rw [PK.strictB_eq] at h
    obtain ⟨hr, he⟩ := band_e h
    right
    rw [h_foundR H ha]
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

theorem checkHeis_of (H : HypsH D K ZP ZX CZ) : checkHeis D = true := by
  unfold checkHeis
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c_checkInv_of H.toHypsC, checkHR_of H⟩, c_checkN_of H.toHypsC⟩,
    checkHNormal_of H⟩, checkHMoves_of H⟩, checkHZ_of H⟩, checkHExp_of H⟩, checkHComm_of H⟩,
    checkHTorus_of H⟩, checkHCent_of H⟩, cc_checkMax_of H.toHypsBC H.hGl H.hGen⟩

end

end CFSG.KS.MaxD2

end
