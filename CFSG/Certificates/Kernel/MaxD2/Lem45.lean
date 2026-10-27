module

public import CFSG.Certificates.Kernel.MaxD2.Heis
public import Certificates.Data.Kernel.MaxD2.Lem45
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45Data
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

section

variable {n w rcnt kN : Nat} {NG NGI RT IX : Nat → Nat}

theorem treeK_cons (p g : Nat) (tr : List (Nat × Nat)) (k : Nat) :
    treeK n w rcnt kN NG NGI RT IX ((p, g) :: tr) k =
      bAnd(stepK n w rcnt kN NG NGI RT IX k p g, treeK n w rcnt kN NG NGI RT IX tr (Nat.succ k)) := by
  simp only [treeK, PK.strictB_eq]

theorem treeK_spec : ∀ (tr : List (Nat × Nat)) (k : Nat),
    treeK n w rcnt kN NG NGI RT IX tr k = true →
      ∀ i < tr.length, stepK n w rcnt kN NG NGI RT IX (k + i) (tr[i]!).1 (tr[i]!).2 = true
  | [], _, _ => fun i hi => absurd hi (by simp)
  | (p, g) :: tr, k, h => by
    rw [treeK_cons] at h
    obtain ⟨h1, h2⟩ := band_e h
    intro i hi
    cases i with
    | zero => simpa using h1
    | succ i =>
      have e := treeK_spec tr (Nat.succ k) h2 i (by simpa using hi)
      rw [show Nat.succ k + i = k + (i + 1) by omega] at e
      simpa using e

theorem stepK_spec {k p g : Nat} (h : stepK n w rcnt kN NG NGI RT IX k p g = true) :
    p < k + 1 ∧ g < 2 * kN ∧ IX (k + 1) < rcnt ∧
      RT (IX (k + 1)) = pcomp n w (mask w)
        (pcomp n w (mask w) (gSel kN NG NGI g) (RT (IX p))) (giSel kN NG NGI g) := by
  unfold stepK at h
  obtain ⟨h1, h⟩ := band_e h
  obtain ⟨h2, h⟩ := band_e h
  obtain ⟨h3, h4⟩ := band_e h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4⟩

theorem gSel_lt {g : Nat} (h : g < kN) :
    gSel kN NG NGI g = NG g ∧ giSel kN NG NGI g = NGI g := by
  have e : Nat.blt g kN = true := Nat.blt_eq.mpr h
  unfold gSel giSel
  rw [e]
  exact ⟨rfl, rfl⟩

theorem gSel_ge {g : Nat} (h : ¬ g < kN) :
    gSel kN NG NGI g = NGI (g - kN) ∧ giSel kN NG NGI g = NG (g - kN) := by
  have e : Nat.blt g kN = false := by
    cases e' : Nat.blt g kN
    · rfl
    · exact absurd (Nat.blt_eq.mp e') h
  unfold gSel giSel
  rw [e]
  exact ⟨rfl, rfl⟩

theorem covK_spec {nz m : Nat} {ZP ZX CV : Nat → Nat} {i : Nat}
    (h : covK nz m ZP ZX IX CV i = true) :
    (ZX i - 1 < nz ∧ ZP (ZX i - 1) = i) ∨ (CV i < m ∧ IX (CV i) = i) := by
  unfold covK at h
  cases hc : bAnd(Nat.blt 0 (ZX i), bAnd(Nat.ble (ZX i) nz, Nat.beq (ZP (Nat.sub (ZX i) 1)) i))
  · obtain ⟨h1, h2⟩ := band_e (bif_f hc h)
    exact Or.inr ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
  · obtain ⟨h1, h⟩ := band_e hc
    obtain ⟨h2, h3⟩ := band_e h
    have a := Nat.blt_eq.mp h1
    have b := Nat.ble_eq.mp h2
    exact Or.inl ⟨by omega, Nat.eq_of_beq_eq_true h3⟩

end

theorem push_get! {A : Array Tab} {x : Tab} {k : Nat} (hk : k < A.size + 1) :
    (A.push x)[k]! = if k < A.size then A[k]! else x := by
  split_ifs with h
  · rw [getElem!_pos (A.push x) k (by simp; omega), Array.getElem_push_lt h,
      ← getElem!_pos A k h]
  · have e : k = A.size := by omega
    subst e
    rw [getElem!_pos (A.push x) A.size (by simp), Array.getElem_push_eq]

theorem any_beq_of_mem {A : Array Tab} {x : Tab} (h : x ∈ A.toList) : A.any (· == x) = true := by
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 h)
  rw [Array.any_eq_true]
  exact ⟨i, hi, by rw [e]; exact beq_self_eq_true x⟩

section

variable {n w : Nat}

theorem wc_u (hn : szOK n w = true) {U W : Nat} (hU : Cn n w U) (hW : Cn n w W) (k : Nat) :
    comp n (comp n (Certificates.FusD2Perm.powT n (unpack n w U) k) (unpack n w W))
      (Certificates.FusD2Perm.powT n (unpack n w U) (5 - k)) = unpack n w (wcK n w U W k) := by
  rw [powT_u hn hU, powT_u hn hU, comp_u (pw_canon hn hU k) hW,
    comp_u (cc (pw_canon hn hU k) hW) (pw_canon hn hU (5 - k))]
  rfl

theorem wc_canon (hn : szOK n w = true) {U W : Nat} (hU : Cn n w U) (hW : Cn n w W) (k : Nat) :
    Cn n w (wcK n w U W k) :=
  cc (cc (pw_canon hn hU k) hW) (pw_canon hn hU (Nat.sub 5 k))

end

section

variable {D : Data} {K : Pk} {ZP ZX CZ : Nat → Nat}

theorem orbitStep_u (H : HypsH D K ZP ZX CZ) {IX : Nat → Nat} {A : Array Tab} {m p g : Nat}
    (hs : A.size = m + 1) (hA : ∀ k < m + 1, IX k < K.rcnt ∧ A[k]! = unpack K.n K.w (K.RT (IX k)))
    (hst : stepK K.n K.w K.rcnt K.kN K.NG K.NGI K.RT IX m p g = true) :
    (McLLem45.orbitStep D A (p, g)).size = m + 2 ∧ ∀ k < m + 2, IX k < K.rcnt ∧
      (McLLem45.orbitStep D A (p, g))[k]! = unpack K.n K.w (K.RT (IX k)) := by
  obtain ⟨hp, hg, hix, heq⟩ := stepK_spec hst
  have HC := H.toHypsC
  have hng : (nGens D).size = K.kN := (c_ngens HC).1
  obtain ⟨hpr, hpA⟩ := hA p hp
  have hx := h_rt_canon H hpr
  have hc : conjTab D.n
      (if g < (nGens D).size then (nGens D)[g]! else (nGensI D)[g - (nGens D).size]!)
      (if g < (nGens D).size then (nGensI D)[g]! else (nGens D)[g - (nGens D).size]!) A[p]! =
      unpack K.n K.w (K.RT (IX (m + 1))) := by
    rw [hng, hpA, H.hDn, heq]
    unfold conjTab
    by_cases hgl : g < K.kN
    · obtain ⟨e1, e2⟩ := gSel_lt (NG := K.NG) (NGI := K.NGI) hgl
      have c1 : Cn K.n K.w (K.NG g) := (H.hNG g hgl).2
      have c2 : Cn K.n K.w (K.NGI g) := (perm_canon (H.hNI g hgl) H.hn).2
      rw [if_pos hgl, if_pos hgl, c_ng_get HC hgl, c_ngi_get HC hgl, e1, e2, comp_u c1 hx,
        comp_u (cc c1 hx) c2]
    · have hj : g - K.kN < K.kN := by omega
      obtain ⟨e1, e2⟩ := gSel_ge (NG := K.NG) (NGI := K.NGI) hgl
      have c1 : Cn K.n K.w (K.NGI (g - K.kN)) := (perm_canon (H.hNI _ hj) H.hn).2
      have c2 : Cn K.n K.w (K.NG (g - K.kN)) := (H.hNG _ hj).2
      rw [if_neg hgl, if_neg hgl, c_ngi_get HC hj, c_ng_get HC hj, e1, e2, comp_u c1 hx,
        comp_u (cc c1 hx) c2]
  have e : McLLem45.orbitStep D A (p, g) = A.push (conjTab D.n
      (if g < (nGens D).size then (nGens D)[g]! else (nGensI D)[g - (nGens D).size]!)
      (if g < (nGens D).size then (nGensI D)[g]! else (nGens D)[g - (nGens D).size]!) A[p]!) :=
    rfl
  rw [e, hc]
  refine ⟨by simp [hs], fun k hk => ?_⟩
  rw [push_get! (by omega), hs]
  by_cases hkm : k < m + 1
  · rw [if_pos hkm]
    exact hA k hkm
  · rw [if_neg hkm]
    have ek : k = m + 1 := by omega
    subst ek
    exact ⟨hix, rfl⟩

theorem orbit_fold (H : HypsH D K ZP ZX CZ) {IX : Nat → Nat} :
    ∀ (tr : List (Nat × Nat)) (A : Array Tab) (m : Nat), A.size = m + 1 →
      (∀ k < m + 1, IX k < K.rcnt ∧ A[k]! = unpack K.n K.w (K.RT (IX k))) →
      treeK K.n K.w K.rcnt K.kN K.NG K.NGI K.RT IX tr m = true →
      (tr.foldl (McLLem45.orbitStep D) A).size = m + 1 + tr.length ∧
      ∀ k < m + 1 + tr.length, IX k < K.rcnt ∧
        (tr.foldl (McLLem45.orbitStep D) A)[k]! = unpack K.n K.w (K.RT (IX k))
  | [], A, m, hs, hA, _ => ⟨by simp [hs], fun k hk => hA k (by simpa using hk)⟩
  | (p, g) :: tr, A, m, hs, hA, h => by
    rw [treeK_cons] at h
    obtain ⟨hst, htr⟩ := band_e h
    obtain ⟨hs', hA'⟩ := orbitStep_u H hs hA hst
    rw [List.foldl_cons, List.length_cons]
    have r := orbit_fold H tr (McLLem45.orbitStep D A (p, g)) (m + 1) hs' hA' htr
    rw [show m + 1 + (tr.length + 1) = m + 1 + 1 + tr.length by omega]
    exact r

theorem lem45_check_of (H : HypsH D K ZP ZX CZ) {wd : List Int} {tr : List (Nat × Nat)}
    {W nz m : Nat} {IX CV : Nat → Nat}
    (hW : wordEqK K.n K.w (mask K.w) (pidn K.n K.w) K.Gp K.GIp K.kG wd W = true)
    (hWc : Cn K.n K.w W)
    (hU5 : Nat.beq (pw K.n K.w (K.RG 0) 5) (pidn K.n K.w) = true)
    (hWW : Nat.beq (pcomp K.n K.w (mask K.w) W W) (pidn K.n K.w) = true)
    (hWC : ∀ k < 5, ∀ l < 5, Nat.beq
      (pcomp K.n K.w (mask K.w) (wcK K.n K.w (K.RG 0) W k) (wcK K.n K.w (K.RG 0) W l))
      (pcomp K.n K.w (mask K.w) (wcK K.n K.w (K.RG 0) W l) (wcK K.n K.w (K.RG 0) W k)) = true)
    (hNe : Nat.beq (wcK K.n K.w (K.RG 0) W 1) (wcK K.n K.w (K.RG 0) W 0) = false)
    (hI0 : IX 0 < K.rcnt) (hI0' : K.RT (IX 0) = K.RG 0)
    (hT : treeK K.n K.w K.rcnt K.kN K.NG K.NGI K.RT IX tr 0 = true)
    (hnz : nz = D.p) (hm : m = tr.length + 1)
    (hC : ∀ i < K.rcnt, covK nz m ZP ZX IX CV i = true) :
    McLLem45.check D wd tr = true := by
  have HC := H.toHypsC
  have hn := H.hn
  have hc0 : Cn K.n K.w (K.RG 0) := (H.hRG 0 (by decide)).2
  have hc1 : Cn K.n K.w (K.RG 1) := (H.hRG 1 (by decide)).2
  have hu : wT D D.uW = unpack K.n K.w (K.RG 0) := by
    have := c_wT_u HC (H.hRG 0 (by decide)).1
    simpa [rWs] using this
  have hv : wT D D.vW = unpack K.n K.w (K.RG 1) := by
    have := c_wT_u HC (H.hRG 1 (by decide)).1
    simpa [rWs] using this
  have hw : wT D wd = unpack K.n K.w W := c_wT_u HC hW
  have hL := orbit_fold H tr #[wT D D.uW] 0 rfl (fun k hk => by
      have e : k = 0 := by omega
      subst e
      refine ⟨hI0, ?_⟩
      rw [hI0', ← hu]
      rfl) (by simpa using hT)
  have hLs : (McLLem45.orbitList D tr).size = 0 + 1 + tr.length := hL.1
  have hLg : ∀ k < 0 + 1 + tr.length, IX k < K.rcnt ∧
      (McLLem45.orbitList D tr)[k]! = unpack K.n K.w (K.RT (IX k)) := hL.2
  have hTB : ∀ k < tr.length, (tr[k]!).1 < k + 1 ∧ (tr[k]!).2 < 2 * K.kN := fun k hk => by
    obtain ⟨a, b, -⟩ := stepK_spec (treeK_spec tr 0 hT k hk)
    exact ⟨by simpa using a, b⟩
  simp only [McLLem45.check, McLLem45.wConj, hu, hv, hw, H.hDn, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [powT_u hn hc0, id_u hn, eq_u (pw_canon hn hc0 5) (pidn_canon hn)]
    exact hU5
  · rw [comp_u hc0 hc1, comp_u hc1 hc0, eq_u (cc hc0 hc1) (cc hc1 hc0)]
    have h := H.hUV
    revert h
    cases Nat.beq (pcomp K.n K.w (mask K.w) (K.RG 0) (K.RG 1))
      (pcomp K.n K.w (mask K.w) (K.RG 1) (K.RG 0))
    · intro _
      rfl
    · intro h
      exact absurd h (by decide)
  · rw [comp_u hWc hWc, id_u hn, eq_u (cc hWc hWc) (pidn_canon hn)]
    exact hWW
  · rw [allBelow_iff']
    intro k hk
    rw [allBelow_iff']
    intro l hl
    rw [wc_u hn hc0 hWc, wc_u hn hc0 hWc, comp_u (wc_canon hn hc0 hWc k) (wc_canon hn hc0 hWc l),
      comp_u (wc_canon hn hc0 hWc l) (wc_canon hn hc0 hWc k),
      eq_u (cc (wc_canon hn hc0 hWc k) (wc_canon hn hc0 hWc l))
        (cc (wc_canon hn hc0 hWc l) (wc_canon hn hc0 hWc k))]
    exact hWC k hk l hl
  · rw [wc_u hn hc0 hWc, wc_u hn hc0 hWc, eq_u (wc_canon hn hc0 hWc 1) (wc_canon hn hc0 hWc 0),
      hNe]
    rfl
  · unfold McLLem45.treeOK
    rw [allBelow_iff', (c_ngens HC).1]
    intro k hk
    obtain ⟨a, b⟩ := hTB k hk
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨a, b⟩
  · rw [(h_rEnum_eq H).1, rec_size, allBelow_iff']
    intro i hi
    rw [rec_get hi, Bool.or_eq_true]
    rcases covK_spec (hC i hi) with ⟨hj, hz⟩ | ⟨hk, hx⟩
    · left
      refine any_beq_of_mem ((h_mem_zT H).2 ⟨ZX i - 1, by rw [← hnz]; exact hj, ?_⟩)
      rw [hz]
    · right
      have hk' : CV i < 0 + 1 + tr.length := by omega
      obtain ⟨-, e⟩ := hLg (CV i) hk'
      rw [hx] at e
      rw [← e]
      refine any_beq_of_mem ?_
      rw [getElem!_pos _ _ (by rw [hLs]; exact hk')]
      exact Array.getElem_mem_toList _

end

end CFSG.KS.MaxD2
