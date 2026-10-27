
module

public import CFSG.Certificates.Kernel.HeFixKSnd.Basic
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Spor.PEnumSound

public section

namespace CFSG.KC.HeFixKSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.KC.HeFixK
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.SmallOddCore
open CFSG.KLie.CT (fget)

theorem cen_cntR (f : Nat → Bool) (N : Nat) :
    cntR f (nat_lit 0) N = ((List.range N).filter f).length := by
  induction N with
  | zero => rfl
  | succ k ih =>
    have e : (nat_lit 0 + k : Nat) = k := Nat.zero_add k
    rw [cntR_succ, ih, e, List.range_succ, List.filter_append, List.length_append]
    cases hfk : f k <;> simp [hfk]

theorem cen_comm_eq (a b : Nat) :
    CFSG.KC.HexaK.comm 32 6 a b =
      Nat.beq (pcomp 32 6 (mask 6) a b) (pcomp 32 6 (mask 6) b a) := by
  simp only [CFSG.KC.HexaK.comm, CFSG.KC.HexaK.mul, CFSG.KC.BfsPin.strictB_app]

theorem cen_commAll_eq (gT : Array CFSG.PSL3Four.Native.Tab) (t : CFSG.PSL3Four.Native.Tab) :
    commAll 32 gT t = (List.range gT.size).all
      (fun i => CFSG.PSL3Four.Native.comp 32 t gT[i]! == CFSG.PSL3Four.Native.comp 32 gT[i]! t) :=
  rfl

theorem cen_pt {gT : Array CFSG.PSL3Four.Native.Tab} {cT : Nat} {GT : Nat → Nat}
    (hs : gT.size = cT) (hb : ∀ k < cT, gT[k]! = unpack 32 6 (GT k))
    (hG : ∀ k < cT, PP 32 6 (GT k)) {t : Nat} (ht : PP 32 6 t) :
    commAll 32 gT (unpack 32 6 t) =
      CFSG.KC.Enum.allN cT fun k => CFSG.KC.HexaK.comm 32 6 t (GT k) := by
  rw [cen_commAll_eq, hs, allN_eq']
  apply all_congr_mem
  intro k hk
  have hk' : k < cT := List.mem_range.mp hk
  rw [hb k hk', comp_unpack_PP ht (hG k hk'), comp_unpack_PP (hG k hk') ht,
    beq_unpack_PP (ht.mul (hG k hk')) ((hG k hk').mul ht), cen_comm_eq]

theorem cen_count {gT : Array Tab} {cT NT : Nat} {GT TT : Nat → Nat} (hs : gT.size = cT)
    (hb : ∀ k < cT, gT[k]! = unpack 32 6 (GT k)) (hG : ∀ k < cT, PP 32 6 (GT k))
    (hT : ∀ i < NT, PP 32 6 (TT i)) (h : cenK NT TT cT GT = 2) :
    ((Array.ofFn (n := NT) fun i => unpack 32 6 (TT i.val)).toList.filter
      (commAll 32 gT)).length = 2 := by
  unfold cenK at h
  rw [cen_cntR] at h
  have hkey : (List.range NT).filter (commAll 32 gT ∘ fun i => unpack 32 6 (TT i)) =
      (List.range NT).filter (fun i =>
        CFSG.KC.Enum.strictB (TT i) fun x =>
          CFSG.KC.Enum.allN cT fun k => CFSG.KC.HexaK.comm 32 6 x (GT k)) := by
    apply List.filter_congr
    intro i hi
    have hi' : i < NT := List.mem_range.mp hi
    show commAll 32 gT (unpack 32 6 (TT i)) =
      CFSG.KC.Enum.strictB (TT i) fun x =>
        CFSG.KC.Enum.allN cT fun k => CFSG.KC.HexaK.comm 32 6 x (GT k)
    rw [cen_pt hs hb hG (hT i hi'), CFSG.KC.BfsPin.strictB_app]
  rw [pts_toList (fun i => unpack 32 6 (TT i)), List.filter_map, List.length_map, hkey]
  exact h

theorem eK_tabs {gE : Array Tab} {cE : Nat} {GE : Nat → Nat} (hs : gE.size = cE)
    (hb : ∀ k < cE, gE[k]! = unpack 32 6 (GE k)) (hG : ∀ k < cE, PP 32 6 (GE k))
    (h : eK cE GE = true) :
    (∀ i < cE, ∀ j < cE, comp 32 gE[i]! gE[j]! = comp 32 gE[j]! gE[i]!) ∧
      ∀ i < cE, comp 32 gE[i]! gE[i]! = idTab 32 := by
  unfold CFSG.KC.HeFixK.eK at h
  simp only [CFSG.KC.HexaK.andB_eq, Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun i hi j hj => ?_, fun i hi => ?_⟩
  · have hc2 : Nat.beq (CFSG.KC.HexaK.mul 32 6 (GE i) (GE j))
        (CFSG.KC.HexaK.mul 32 6 (GE j) (GE i)) = true := by
      have hc := CFSG.KS.allN_spec (CFSG.KS.allN_spec hA i hi) j hj
      simp only [CFSG.KC.HexaK.comm, CFSG.KC.HexaK.strictB_eq'] at hc
      exact hc
    have e : CFSG.KC.HexaK.mul 32 6 (GE i) (GE j) = CFSG.KC.HexaK.mul 32 6 (GE j) (GE i) :=
      Nat.eq_of_beq_eq_true hc2
    have k1 : comp 32 (unpack 32 6 (GE i)) (unpack 32 6 (GE j)) =
        unpack 32 6 (CFSG.KC.HexaK.mul 32 6 (GE i) (GE j)) :=
      comp_unpack_PP (hG i hi) (hG j hj)
    have k2 : comp 32 (unpack 32 6 (GE j)) (unpack 32 6 (GE i)) =
        unpack 32 6 (CFSG.KC.HexaK.mul 32 6 (GE j) (GE i)) :=
      comp_unpack_PP (hG j hj) (hG i hi)
    rw [hb i hi, hb j hj, k1, k2, e]
  · have hs2 : Nat.beq (CFSG.KC.HexaK.mul 32 6 (GE i) (GE i)) (pidn 32 6) = true := by
      have h1 := CFSG.KS.allN_spec hB i hi
      simp only [CFSG.KC.HexaK.strictB_eq'] at h1
      exact h1
    have e2 : CFSG.KC.HexaK.mul 32 6 (GE i) (GE i) = pidn 32 6 := Nat.eq_of_beq_eq_true hs2
    have k3 : comp 32 (unpack 32 6 (GE i)) (unpack 32 6 (GE i)) =
        unpack 32 6 (CFSG.KC.HexaK.mul 32 6 (GE i) (GE i)) :=
      comp_unpack_PP (hG i hi) (hG i hi)
    rw [hb i hi, k3, e2]
    exact (idTab_unpack_PP (hG i hi).sz).symm

theorem norm_getElem_map (f : Tab → Tab) (g : Array Tab) {k : Nat} (hk : k < g.size) :
    (g.map f)[k]! = f g[k]! := by
  rw [getElem!_pos (g.map f) k (by simpa using hk), getElem!_pos g k hk]
  simp

theorem norm_ofFn_getElem {NE : Nat} (f : Fin NE → Tab) {k : Nat} (hk : k < NE) :
    (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos (Array.ofFn f) k (by simpa using hk), Array.getElem_ofFn]

theorem norm_inv_getElem {gT : Array Tab} {cT : Nat} {GT : Nat → Nat}
    (hsT : gT.size = cT) (hbT : ∀ k < cT, gT[k]! = unpack 32 6 (GT k))
    (hGT : ∀ k < cT, PP 32 6 (GT k)) {k : Nat} (hk : k < cT) :
    (gT.map (invTab 32))[k]! = unpack 32 6 (pinvS 32 6 (mask 6) (GT k)) := by
  rw [norm_getElem_map (invTab 32) gT (show k < gT.size by omega), hbT k hk,
    CFSG.KC.HeFixKSnd.invTab_unpack_PP (hGT k hk)]

theorem norm_inL_exists {NE : Nat} {TE : Nat → Nat} {x : Nat}
    (hx : CFSG.KC.HexaK.inL NE TE x = true) : ∃ j < NE, TE j = x := by
  unfold CFSG.KC.HexaK.inL at hx
  rw [CFSG.KC.HexaK.strictB_eq', CFSG.KC.BfsPin.anyN_eq, List.any_eq_true] at hx
  obtain ⟨j, hj, hb⟩ := hx
  exact ⟨j, List.mem_range.1 hj, (Nat.eq_of_beq_eq_true hb).symm⟩

theorem norm_found_of_inL {NE : Nat} {TE : Nat → Nat} {x : Nat}
    (hx : CFSG.KC.HexaK.inL NE TE x = true) :
    CFSG.PSL3Four.Native.found
      (CFSG.PSL3Four.Native.indexOf (Array.ofFn (n := NE) fun i => unpack 32 6 (TE i.val)))
      (Array.ofFn (n := NE) fun i => unpack 32 6 (TE i.val)) (unpack 32 6 x) = true := by
  rw [CFSG.KS.PEnum.found_indexOf_iff]
  obtain ⟨j, hj, he⟩ := norm_inL_exists hx
  refine ⟨j, by simpa using hj, ?_⟩
  rw [norm_ofFn_getElem _ hj]
  exact congrArg (unpack 32 6) he

theorem norm_normK_spec {cT cE NE : Nat} {GT GE TE : Nat → Nat}
    (h : normK cT GT NE TE cE GE = true) {j i : Nat} (hj : j < cT) (hi : i < cE) :
    CFSG.KC.HexaK.inL NE TE (CFSG.KC.HexaK.conj 32 6 (GT j) (GE i)) = true ∧
      CFSG.KC.HexaK.inL NE TE (CFSG.KC.HexaK.conjInv 32 6 (GT j) (GE i)) = true := by
  unfold normK at h
  have h1 := CFSG.KS.allN_spec h j hj
  have h2 := CFSG.KS.allN_spec h1 i hi
  rw [CFSG.KC.HexaK.andB_eq, Bool.and_eq_true] at h2
  exact h2

theorem norm_invsOK {gT : Array Tab} {cT : Nat} {GT : Nat → Nat}
    (hsT : gT.size = cT) (hbT : ∀ k < cT, gT[k]! = unpack 32 6 (GT k))
    (hGT : ∀ k < cT, PP 32 6 (GT k)) :
    CFSG.PSL3Four.Native.invsOK 32 gT (gT.map (invTab 32)) = true := by
  unfold CFSG.PSL3Four.Native.invsOK
  rw [Bool.and_eq_true]
  refine ⟨by simp, ?_⟩
  simp only [CFSG.PSL3Four.Native.allBelow, List.all_eq_true, List.mem_range, Bool.and_eq_true]
  intro k hk
  have hk' : k < cT := by omega
  rw [norm_inv_getElem hsT hbT hGT hk', hbT k hk', CFSG.KC.HeFixKSnd.size_unpack,
    CFSG.KC.HeFixKSnd.comp_inv_left_PP (hGT k hk')]
  simp

theorem norm_tabs {gT gE : Array Tab} {cT cE NE : Nat} {GT GE TE : Nat → Nat}
    (hsT : gT.size = cT) (hbT : ∀ k < cT, gT[k]! = unpack 32 6 (GT k))
    (hGT : ∀ k < cT, PP 32 6 (GT k))
    (hsE : gE.size = cE) (hbE : ∀ k < cE, gE[k]! = unpack 32 6 (GE k))
    (hGE : ∀ k < cE, PP 32 6 (GE k)) (hTE : ∀ i < NE, PP 32 6 (TE i))
    (h : normK cT GT NE TE cE GE = true) :
    normalOK 32 (Array.ofFn (n := NE) fun i => unpack 32 6 (TE i.val)) gT
      (gT.map (invTab 32)) gE = true := by
  unfold normalOK
  dsimp only
  rw [Bool.and_eq_true]
  refine ⟨norm_invsOK hsT hbT hGT, ?_⟩
  simp only [CFSG.PSL3Four.Native.allBelow, List.all_eq_true, List.mem_range, Bool.and_eq_true]
  intro j hj i hi
  have hjT : j < cT := by omega
  have hiE : i < cE := by omega
  obtain ⟨hc1, hc2⟩ := norm_normK_spec h hjT hiE
  constructor
  · rw [hbT j hjT, norm_inv_getElem hsT hbT hGT hjT, hbE i hiE,
      CFSG.KC.HeFixKSnd.conjTab_unpack_PP (hGT j hjT) (hGE i hiE)]
    exact norm_found_of_inL hc1
  · rw [norm_inv_getElem hsT hbT hGT hjT, hbT j hjT, hbE i hiE,
      CFSG.KC.HeFixKSnd.conjInvTab_unpack_PP (hGT j hjT) (hGE i hiE)]
    exact norm_found_of_inL hc2

end CFSG.KC.HeFixKSnd

end
