module

public import CFSG.Certificates.Kernel.MaxD2.Heis

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis
open CFSG.ComponentClassification.PSL3Four (exists_getElem!_of_mem getElem!_mem)

structure HypsHE (D : Data) (K : Pk) (ZP ZX CZ : Nat → Nat) : Prop where
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
  hRG : ∀ j < 2, wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG ((rWs D)[j]!) (K.RG j) =
    true ∧ Cn K.n K.w (K.RG j)
  hRh : penumHdK (pidn K.n K.w) K.rcnt (D.p ^ 3) K.RT K.RPL = true
  hRp : ∀ i < K.rcnt, penumPtK K.n K.w (mask K.w) (K.n * K.w) false K.RG K.RGI 2 K.rcnt K.RT K.RPL
    K.RPOS K.RSRT K.RSRI i = true
  hRc : K.rcnt = D.p ^ 3
  hNorm : ∀ j < K.kN, ∀ i < 2,
    conjInK K.n K.w K.rcnt K.RT (K.NG j) (K.NGI j) (K.RG i) (r32 K.NH (4 * j + 2 * i)) = true ∧
    conjInK K.n K.w K.rcnt K.RT (K.NGI j) (K.NG j) (K.RG i) (r32 K.NH (4 * j + 2 * i + 1)) = true
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

section

variable {D : Data} {K : Pk} {ZP ZX CZ : Nat → Nat}

theorem he_wT_u (H : HypsHE D K ZP ZX CZ) {wd : List Int} {r : Nat}
    (h : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG wd r = true) :
    wT D wd = unpack K.n K.w r := by
  unfold wT giT
  rw [H.hDn]
  exact wordT_u ⟨H.hGs, H.hGb⟩ H.hGp h

theorem he_gp_perm (H : HypsHE D K ZP ZX CZ) {j : Nat} (hj : j < K.kG) :
    permOK K.n K.w (mask K.w) (K.n * K.w) (K.Gp j) (K.GIp j) = true :=
  (PK.allN_iff.1 H.hGp) j hj

theorem he_gi_u (H : HypsHE D K ZP ZX CZ) {j : Nat} (hj : j < K.kG) :
    (giT D)[j]! = unpack K.n K.w (K.GIp j) := by
  have hj' : j < D.gT.size := by rw [H.hGs]; exact hj
  unfold giT
  rw [getElem!_pos _ j (by simpa using hj'), Array.getElem_map, ← getElem!_pos D.gT j hj',
    H.hGb j hj, H.hDn, inv_u (he_gp_perm H hj)]

theorem he_ngens (H : HypsHE D K ZP ZX CZ) : GensOK K.n K.w K.kN K.NG (nGens D) := by
  refine ⟨by simp [nGens, H.hNk], fun j hj => ⟨?_, (H.hNG j hj).2⟩⟩
  unfold nGens
  rw [map_get _ (by rw [H.hNk]; exact hj), he_wT_u H (H.hNG j hj).1]

theorem he_nEnum_eq (H : HypsHE D K ZP ZX CZ) :
    nEnum D = penumRec K.n K.w K.cnt K.NT K.NPL ∧
      enumOK K.n (nGens D) (penumRec K.n K.w K.cnt K.NT K.NPL) = true := by
  unfold nEnum
  rw [H.hDn]
  exact penumK_left_sound H.hn (he_ngens H) H.hNh H.hNp

theorem he_nt_canon (H : HypsHE D K ZP ZX CZ) {i : Nat} (hi : i < K.cnt) : Cn K.n K.w (K.NT i) :=
  (pt_spec (H.hNp i hi)).1

theorem checkInv_ofE (H : HypsHE D K ZP ZX CZ) : checkInv D = true := by
  unfold checkInv
  rw [allBelow_iff']
  intro j hj
  have hj' : j < K.kG := by rw [← H.hGs]; exact hj
  rw [he_gi_u H hj', H.hGb j hj', H.hDn, inv_comp (he_gp_perm H hj')]
  simp [size_u]

theorem checkN_ofE (H : HypsHE D K ZP ZX CZ) : checkN D = true := by
  obtain ⟨e, hok⟩ := he_nEnum_eq H
  unfold checkN
  rw [e, H.hDn, hok, rec_size, H.hNc]
  simp

theorem he_ng_get (H : HypsHE D K ZP ZX CZ) {j : Nat} (hj : j < K.kN) :
    (nGens D)[j]! = unpack K.n K.w (K.NG j) :=
  ((he_ngens H).2 j hj).1

theorem he_ngi_get (H : HypsHE D K ZP ZX CZ) {j : Nat} (hj : j < K.kN) :
    (nGensI D)[j]! = unpack K.n K.w (K.NGI j) := by
  have hs : (nGens D).size = K.kN := (he_ngens H).1
  unfold nGensI
  rw [getElem!_pos _ j (by simpa [hs] using hj), Array.getElem_map,
    ← getElem!_pos (nGens D) j (by rw [hs]; exact hj), he_ng_get H hj, H.hDn, inv_u (H.hNI j hj)]

theorem he_invsN (H : HypsHE D K ZP ZX CZ) : invsOK D.n (nGens D) (nGensI D) = true := by
  have hs : (nGens D).size = K.kN := (he_ngens H).1
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [nGensI], allBelow_iff'.2 fun k hk => ?_⟩
  rw [hs] at hk
  rw [he_ngi_get H hk, he_ng_get H hk, H.hDn, inv_comp (H.hNI k hk)]
  simp [size_u]

theorem he_foundN (H : HypsHE D K ZP ZX CZ) {X : Nat} (hX : Cn K.n K.w X) :
    found (indexOf (penumRec K.n K.w K.cnt K.NT K.NPL).tabs) (penumRec K.n K.w K.cnt K.NT K.NPL).tabs
      (unpack K.n K.w X) = true ↔ ∃ i < K.cnt, K.NT i = X := by
  rw [found_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    exact ⟨i, hi, u_inj (he_nt_canon H hi) hX e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [rec_size]; exact hi, rec_get hi⟩

theorem he_rgens (H : HypsHE D K ZP ZX CZ) : GensOK K.n K.w 2 K.RG (rGens D) := by
  refine ⟨by simp [rGens, rWs], fun j hj => ⟨?_, (H.hRG j hj).2⟩⟩
  unfold rGens
  rw [map_get _ (by simpa [rWs] using hj), he_wT_u H (H.hRG j hj).1]

theorem he_rEnum_eq (H : HypsHE D K ZP ZX CZ) :
    hrEnum D = penumRec K.n K.w K.rcnt K.RT K.RPL ∧
      enumOK K.n (rGens D) (penumRec K.n K.w K.rcnt K.RT K.RPL) = true := by
  unfold hrEnum
  rw [H.hDn]
  exact penumK_left_sound H.hn (he_rgens H) H.hRh H.hRp

theorem he_rt_canon (H : HypsHE D K ZP ZX CZ) {i : Nat} (hi : i < K.rcnt) : Cn K.n K.w (K.RT i) :=
  (pt_spec (H.hRp i hi)).1

theorem he_rg_get (H : HypsHE D K ZP ZX CZ) {j : Nat} (hj : j < 2) :
    (rGens D)[j]! = unpack K.n K.w (K.RG j) :=
  ((he_rgens H).2 j hj).1

theorem he_rg_canon (H : HypsHE D K ZP ZX CZ) {j : Nat} (hj : j < 2) : Cn K.n K.w (K.RG j) :=
  (H.hRG j hj).2

theorem he_foundR (H : HypsHE D K ZP ZX CZ) {X : Nat} (hX : Cn K.n K.w X) :
    found (indexOf (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs) (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs
      (unpack K.n K.w X) = true ↔ ∃ i < K.rcnt, K.RT i = X := by
  rw [found_iff]
  constructor
  · rintro ⟨i, hi, e⟩
    rw [rec_size] at hi
    rw [rec_get hi] at e
    exact ⟨i, hi, u_inj (he_rt_canon H hi) hX e⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [rec_size]; exact hi, rec_get hi⟩

theorem he_zT_eq (H : HypsHE D K ZP ZX CZ) :
    zTabs D = (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs.filter
      (commutesUV K.n (unpack K.n K.w (K.RG 0)) (unpack K.n K.w (K.RG 1))) := by
  unfold zTabs
  rw [(he_rEnum_eq H).1, he_rg_get H (by decide : 0 < 2), he_rg_get H (by decide : 1 < 2), H.hDn]

theorem he_mem_zT (H : HypsHE D K ZP ZX CZ) {x : Tab} :
    x ∈ (zTabs D).toList ↔ ∃ j < D.p, x = unpack K.n K.w (K.RT (ZP j)) := by
  obtain ⟨z1, z2⟩ := zK_spec H.hZ
  have hu := he_rg_canon H (by decide : 0 < 2)
  have hv := he_rg_canon H (by decide : 1 < 2)
  rw [he_zT_eq H, Array.toList_filter, List.mem_filter]
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨r, hr, rfl⟩ := exists_getElem!_of_mem hx
    rw [rec_size] at hr
    rw [rec_get hr, comm_u hu hv (he_rt_canon H hr)] at hc
    obtain ⟨a, b, c⟩ := z1 r hr hc
    refine ⟨ZX r - 1, by omega, ?_⟩
    rw [rec_get hr, c]
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨a, -, c⟩ := z2 j hj
    have hm := getElem!_mem (T := (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs)
      (k := ZP j) (by rw [rec_size]; exact a)
    rw [rec_get a] at hm
    exact ⟨hm, by rw [comm_u hu hv (he_rt_canon H a)]; exact c⟩

theorem he_zT_any (H : HypsHE D K ZP ZX CZ) (f : Tab → Bool) :
    anyBelow (zTabs D).size (fun j => f (zTabs D)[j]!) = true ↔
      ∃ j < D.p, f (unpack K.n K.w (K.RT (ZP j))) = true := by
  rw [anyBelow_iff]
  constructor
  · rintro ⟨j, hj, e⟩
    obtain ⟨j', hj', e'⟩ := (he_mem_zT H).1 (getElem!_mem hj)
    exact ⟨j', hj', by rw [← e']; exact e⟩
  · rintro ⟨j, hj, e⟩
    obtain ⟨k, hk, e'⟩ := exists_getElem!_of_mem ((he_mem_zT H).2 ⟨j, hj, rfl⟩)
    exact ⟨k, hk, by rw [e']; exact e⟩

theorem he_zT_all (H : HypsHE D K ZP ZX CZ) (f : Tab → Bool) :
    allBelow (zTabs D).size (fun j => f (zTabs D)[j]!) = true ↔
      ∀ j < D.p, f (unpack K.n K.w (K.RT (ZP j))) = true := by
  rw [allBelow_iff']
  constructor
  · intro h j hj
    obtain ⟨k, hk, e'⟩ := exists_getElem!_of_mem ((he_mem_zT H).2 ⟨j, hj, rfl⟩)
    rw [← e']
    exact h k hk
  · intro h k hk
    obtain ⟨j', hj', e'⟩ := (he_mem_zT H).1 (getElem!_mem hk)
    rw [e']
    exact h j' hj'

theorem he_zT_size (H : HypsHE D K ZP ZX CZ) : (zTabs D).size = D.p := by
  obtain ⟨z1, z2⟩ := zK_spec H.hZ
  have hu := he_rg_canon H (by decide : 0 < 2)
  have hv := he_rg_canon H (by decide : 1 < 2)
  rw [he_zT_eq H, ← Array.length_toList, Array.toList_filter, ← countBelow_tabs, rec_size,
    countBelow_eq (g := fun r => commUVK K.n K.w (K.RG 0) (K.RG 1) (K.RT r)) fun r hr => by
      rw [rec_get hr, comm_u hu hv (he_rt_canon H hr)],
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

theorem checkHR_ofE (H : HypsHE D K ZP ZX CZ) : checkHR D = true := by
  obtain ⟨e, hok⟩ := he_rEnum_eq H
  unfold checkHR
  rw [e, H.hDn, hok, rec_size, H.hRc]
  simp

theorem he_conjIn_spec (H : HypsHE D K ZP ZX CZ) {g gi x h : Nat} (hg : Cn K.n K.w g)
    (hgi : Cn K.n K.w gi) (hx : Cn K.n K.w x) (hk : conjInK K.n K.w K.rcnt K.RT g gi x h = true) :
    found (indexOf (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs) (penumRec K.n K.w K.rcnt K.RT K.RPL).tabs
      (conjTab K.n (unpack K.n K.w g) (unpack K.n K.w gi) (unpack K.n K.w x)) = true := by
  unfold conjTab
  rw [comp_u hg hx, comp_u (cc hg hx) hgi, he_foundR H (cc (cc hg hx) hgi)]
  unfold conjInK at hk
  obtain ⟨h1, h2⟩ := band_e hk
  exact ⟨h, Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem checkHNormal_ofE (H : HypsHE D K ZP ZX CZ) : checkHNormal D = true := by
  obtain ⟨e, -⟩ := he_rEnum_eq H
  unfold checkHNormal normalOK
  rw [e, H.hDn]
  have hs : (nGens D).size = K.kN := (he_ngens H).1
  have hr : (rGens D).size = 2 := (he_rgens H).1
  simp only [Bool.and_eq_true]
  refine ⟨by rw [← H.hDn]; exact he_invsN H, ?_⟩
  rw [allBelow_iff']
  intro j hj
  rw [hs] at hj
  rw [allBelow_iff']
  intro i hi
  rw [hr] at hi
  rw [he_ng_get H hj, he_ngi_get H hj, he_rg_get H hi]
  have hc := perm_canon (H.hNI j hj) H.hn
  have hx := he_rg_canon H hi
  simp only [Bool.and_eq_true]
  exact ⟨he_conjIn_spec H hc.1 hc.2 hx (H.hNorm j hj i hi).1,
    he_conjIn_spec H hc.2 hc.1 hx (H.hNorm j hj i hi).2⟩

theorem checkHZ_ofE (H : HypsHE D K ZP ZX CZ) : checkHZ D = true := by
  unfold checkHZ
  rw [he_zT_size H]
  exact beq_self_eq_true _

theorem checkHExp_ofE (H : HypsHE D K ZP ZX CZ) : checkHExp D = true := by
  obtain ⟨e, -⟩ := he_rEnum_eq H
  have hn := H.hn
  unfold checkHExp
  simp only [e, H.hDn, rec_size]
  rw [allBelow_iff']
  intro k hk
  have hr := he_rt_canon H hk
  rw [rec_get hk, powT_u hn hr, id_u hn, eq_u (pw_canon hn hr _) (pidn_canon hn)]
  exact (PK.allN_iff.1 H.hExp) k hk

theorem checkHComm_ofE (H : HypsHE D K ZP ZX CZ) : checkHComm D = true := by
  obtain ⟨e, -⟩ := he_rEnum_eq H
  have hu := he_rg_canon H (by decide : 0 < 2)
  have hv := he_rg_canon H (by decide : 1 < 2)
  unfold checkHComm
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [he_rg_get H (by decide : 0 < 2), he_rg_get H (by decide : 1 < 2), H.hDn, comp_u hu hv,
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
    have hk' := he_rt_canon H hk
    have hl' := he_rt_canon H hl
    rw [e, rec_get hk, rec_get hl, H.hDn, comp_u hk' hl', comp_u hl' hk']
    refine (he_zT_any H (fun z => unpack K.n K.w (pcomp K.n K.w (mask K.w) (K.RT k) (K.RT l)) ==
      comp K.n z (unpack K.n K.w (pcomp K.n K.w (mask K.w) (K.RT l) (K.RT k))))).2 ?_
    have key : ∃ a < D.p, pcomp K.n K.w (mask K.w) (K.RT k) (K.RT l) =
        pcomp K.n K.w (mask K.w) (K.RT (ZP a)) (pcomp K.n K.w (mask K.w) (K.RT l) (K.RT k)) := by
      by_cases hlk : l < k + 1
      · exact (commK_spec (H.hComm k hk l hlk)).1
      · exact (commK_spec (H.hComm l hl k (by omega))).2
    obtain ⟨a, ha, ea⟩ := key
    obtain ⟨hza, -, -⟩ := (zK_spec H.hZ).2 a ha
    have hz := he_rt_canon H hza
    refine ⟨a, ha, ?_⟩
    rw [comp_u hz (cc hl' hk'), eq_u (cc hk' hl') (cc hz (cc hl' hk')), ea, Nat.beq_refl]

theorem checkHTorus_ofE (H : HypsHE D K ZP ZX CZ) : checkHTorus D = true := by
  obtain ⟨eR, -⟩ := he_rEnum_eq H
  obtain ⟨eN, -⟩ := he_nEnum_eq H
  have hT := perm_canon H.hTp H.hn
  have hn := H.hn
  have hu := he_rg_canon H (by decide : 0 < 2)
  have hv := he_rg_canon H (by decide : 1 < 2)
  have hk := H.hTk
  unfold torusHK at hk
  simp only [PK.strictB_eq] at hk
  obtain ⟨k1, hk⟩ := band_e hk
  obtain ⟨k2, k3⟩ := band_e hk
  have pa := pw_canon hn hT.1
  have pb := pw_canon hn hT.2
  unfold checkHTorus
  simp only [Bool.and_eq_true]
  rw [eN, he_wT_u H H.hTw, H.hDn, inv_u H.hTp]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [size_u]
  · rw [inv_comp H.hTp]
    exact beq_self_eq_true _
  · rw [he_foundN H hT.1]
    exact ⟨K.th, H.hTh, H.hTn⟩
  · rw [allBelow_iff']
    intro k hk
    rw [eR, rec_size] at hk
    have e := (PK.allN_iff.1 k1) k hk
    have hr := he_rt_canon H hk
    rw [eR, rec_get hk, powT_u hn hT.1, powT_u hn hT.2, powT_u hn hr, comp_u (pa _) hr,
      comp_u (cc (pa _) hr) (pb _)]
    refine (he_zT_any H (fun z => unpack K.n K.w (pcomp K.n K.w (mask K.w)
      (pcomp K.n K.w (mask K.w) (pw K.n K.w K.TP D.tm) (K.RT k)) (pw K.n K.w K.TPI D.tm)) ==
        comp K.n (unpack K.n K.w (pw K.n K.w (K.RT k) D.tlam)) z)).2 ?_
    obtain ⟨j, hj, ej⟩ := anyZ_iff.1 e
    refine ⟨j, hj, ?_⟩
    have hz := he_rt_canon H ((zK_spec H.hZ).2 j hj).1
    rw [comp_u (pw_canon hn hr _) hz, eq_u (cc (cc (pa _) hr) (pb _)) (cc (pw_canon hn hr _) hz)]
    exact ej
  · rw [allBelow_iff']
    intro k hk
    rw [eR, rec_size] at hk
    have e := (PK.allN_iff.1 k2) k hk
    have hr := he_rt_canon H hk
    rw [eR, rec_get hk, powT_u hn hT.1, powT_u hn hT.2, comp_u (pa _) hr,
      comp_u (cc (pa _) hr) (pb _), comp_u (cc (cc (pa _) hr) (pb _)) hr]
    refine (he_zT_any H (fun z => unpack K.n K.w (pcomp K.n K.w (mask K.w)
      (pcomp K.n K.w (mask K.w) (pcomp K.n K.w (mask K.w) (pw K.n K.w K.TP D.te) (K.RT k))
        (pw K.n K.w K.TPI D.te)) (K.RT k)) == z)).2 ?_
    obtain ⟨j, hj, ej⟩ := anyZ_iff.1 e
    refine ⟨j, hj, ?_⟩
    have hz := he_rt_canon H ((zK_spec H.hZ).2 j hj).1
    rw [eq_u (cc (cc (cc (pa _) hr) (pb _)) hr) hz]
    exact ej
  · rw [allBelow_iff']
    intro k hk
    rw [allBelow_iff']
    intro i hi
    rw [eR, rec_size] at hi
    have e := (PK.allN_iff.1 ((PK.allN_iff.1 k3) k hk)) i hi
    have hr := he_rt_canon H hi
    rw [Bool.or_eq_true]
    by_cases hc : commUVK K.n K.w (K.RG 0) (K.RG 1) (K.RT i) = true
    · left
      rw [Array.contains_iff_mem, ← Array.mem_toList_iff, he_mem_zT H, eR, rec_get hi]
      obtain ⟨a, b, c⟩ := (zK_spec H.hZ).1 i hi hc
      exact ⟨ZX i - 1, by omega, by rw [c]⟩
    · right
      have e' := bif_f (Bool.eq_false_iff.2 hc) e
      rw [allBelow_iff']
      intro j hj
      have e2 := (PK.allN_iff.1 e') j hj
      rw [eR, rec_get hi, powT_u hn hT.1, powT_u hn hT.2, powT_u hn hr, comp_u (pa _) hr,
        comp_u (cc (pa _) hr) (pb _)]
      refine (he_zT_all H (fun z => !(unpack K.n K.w (pcomp K.n K.w (mask K.w)
        (pcomp K.n K.w (mask K.w) (pw K.n K.w K.TP (k + 1)) (K.RT i)) (pw K.n K.w K.TPI (k + 1))) ==
          comp K.n (unpack K.n K.w (pw K.n K.w (K.RT i) j)) z))).2 fun l hl => ?_
      have e3 := bnot_e ((PK.allN_iff.1 e2) l hl)
      have hz := he_rt_canon H ((zK_spec H.hZ).2 l hl).1
      rw [comp_u (pw_canon hn hr _) hz, eq_u (cc (cc (pa _) hr) (pb _)) (cc (pw_canon hn hr _) hz),
        Bool.not_eq_true']
      exact e3

theorem checkHCent_ofE (H : HypsHE D K ZP ZX CZ) : checkHCent D = true := by
  obtain ⟨eR, -⟩ := he_rEnum_eq H
  obtain ⟨eN, -⟩ := he_nEnum_eq H
  have hn := H.hn
  unfold checkHCent commutesUV
  simp only [eR, eN, H.hDn, rec_size]
  rw [allBelow_iff']
  intro k hk
  have hc := H.hC k hk
  have ha := he_nt_canon H hk
  have hu := he_rg_canon H (by decide : 0 < 2)
  have hv := he_rg_canon H (by decide : 1 < 2)
  rw [rec_get hk, he_rg_get H (by decide : 0 < 2), he_rg_get H (by decide : 1 < 2),
    comp_u ha hu, comp_u hu ha, comp_u ha hv, comp_u hv ha, eq_u (cc ha hu) (cc hu ha),
    eq_u (cc ha hv) (cc hv ha), Bool.or_eq_true]
  unfold centK at hc
  rw [PK.strictB_eq] at hc
  by_cases h1 : Nat.beq (Nat.land (r32 K.CH k) 1) 1 = true
  · have h := bif_t h1 hc
    rw [PK.strictB_eq] at h
    obtain ⟨hr, he⟩ := band_e h
    right
    rw [he_foundR H ha]
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

theorem heisEqParts_of (H : HypsHE D K ZP ZX CZ) :
    checkInv D = true ∧ checkHR D = true ∧ checkN D = true ∧ checkHNormal D = true ∧
      checkHZ D = true ∧ checkHExp D = true ∧ checkHComm D = true ∧ checkHTorus D = true ∧
      checkHCent D = true :=
  ⟨checkInv_ofE H, checkHR_ofE H, checkN_ofE H, checkHNormal_ofE H, checkHZ_ofE H,
    checkHExp_ofE H, checkHComm_ofE H, checkHTorus_ofE H, checkHCent_ofE H⟩

end

end CFSG.KS.MaxD2

end
