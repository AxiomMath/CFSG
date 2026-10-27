module

public import CFSG.Certificates.Kernel.J4.MLevelMain
public import Certificates.Data.Kernel.J4MFix

public section

namespace CFSG.KJ4.MLevel

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.R CFSG.KJ4.Mat CFSG.KJ4.Models CFSG.KC.Loop
open CFSG.Certificates.DceWord (lvE wv)
open CFSG.Certificates.J4Words (jv invJ jv_inv)
open CFSG.Certificates.J4KShape (rv)
open scoped Matrix

theorem allIn_from {a b : ℕ} {f : ℕ → Bool} (h : allIn a b f = true) {i : ℕ} (hai : a ≤ i)
    (hi : i < b) : f i = true := by
  refine CFSG.Certificates.J4KShape.rngAll_spec _ h i hai hi ?_
  change i < a + 64 * ((b - a) >>> 6 + 1)
  rw [Nat.shiftRight_eq_div_pow]
  have h64 : (2 : ℕ) ^ 6 = 64 := rfl
  rw [h64]
  omega

theorem mfix_parts {k : KD} {d : MD} (h : j4MFix k d = true) :
    d.nH ≤ 65536 ∧ d.nSG ≤ 65536 ∧ d.nW ≤ 65536 ∧ (∀ w < d.nW, wR (d.WT w) < 12) ∧
    (∀ a, d.nH ≤ a → a < 65536 → d.HT a = 0) ∧ (∀ e, d.nSG ≤ e → e < 65536 → d.SG e = 0) ∧
    (∀ w, d.nW ≤ w → w < 65536 → d.WT w = 0) ∧ (∀ g < k.NF, ojAt k.FT k.OT g = true) := by
  obtain ⟨h1, h⟩ := andB_eq_true.1 h
  obtain ⟨h2, h⟩ := andB_eq_true.1 h
  obtain ⟨h3, h⟩ := andB_eq_true.1 h
  obtain ⟨h4, h⟩ := andB_eq_true.1 h
  obtain ⟨h5, h⟩ := andB_eq_true.1 h
  obtain ⟨h6, h⟩ := andB_eq_true.1 h
  obtain ⟨h7, h8⟩ := andB_eq_true.1 h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3,
    fun w hw => blt_eq_true.1 (allIn_spec h4 hw),
    fun a ha hb => beq_eq_true.1 (allIn_from h5 ha hb),
    fun e ha hb => beq_eq_true.1 (allIn_from h6 ha hb),
    fun w ha hb => beq_eq_true.1 (allIn_from h7 ha hb), fun g hg => allIn_spec h8 hg⟩

theorem oj_of_mfix {k : KD} {d : MD} (h : j4MFix k d = true) :
    ∀ g < k.NF, 0 < fJ (k.FT g) → oJ (k.OT (fJ (k.FT g) - 1)) = fJ (k.FT g) := by
  intro g hg hJ
  have hq := (mfix_parts h).2.2.2.2.2.2.2 g hg
  unfold ojAt at hq
  rw [letB_eq] at hq
  rcases orB_eq_true.1 hq with hq | hq
  · rw [beq_eq_true.1 hq] at hJ
    exact absurd hJ (Nat.lt_irrefl 0)
  · exact beq_eq_true.1 hq

theorem hOJ_of_mfix {k : KD} {d : MD} (h : j4MFix k d = true) :
    ∀ g < k.NF, 0 < fJ (k.FT g) → k.OT (fJ (k.FT g) - 1) ≠ 0 := by
  intro g hg hJ h0
  have e := oj_of_mfix h g hg hJ
  rw [h0] at e
  have e0 : oJ 0 = 0 := by decide
  omega

@[expose] def tr16 (T : ℕ → ℕ) (a : ℕ) : ℕ := if a < 65536 then T a else 0

@[expose] def dCut (d : MD) : MD := { d with HT := tr16 d.HT, SG := tr16 d.SG, WT := tr16 d.WT }

theorem tr16_of {T : ℕ → ℕ} {a : ℕ} (h : a < 65536) : tr16 T a = T a := by
  simp only [tr16, h, ↓reduceIte]

theorem tr16_zero {T : ℕ → ℕ} {n : ℕ} (h : ∀ a, n ≤ a → a < 65536 → T a = 0) :
    ∀ a, n ≤ a → tr16 T a = 0 := by
  intro a ha
  unfold tr16
  split_ifs with hb
  · exact h a ha hb
  · rfl

theorem land_lt (x : ℕ) : Nat.land x 65535 < 65536 := by
  have h : x &&& 65535 ≤ 65535 := Nat.and_le_right
  exact Nat.lt_succ_of_le h

theorem tr16_f16 (T : ℕ → ℕ) (p o : ℕ) : tr16 T (f16 p o) = T (f16 p o) := tr16_of (land_lt _)

theorem tr16_oH (T : ℕ → ℕ) (O : ℕ) : tr16 T (oH O) = T (oH O) := tr16_of (land_lt _)

theorem stSm_cut (d : MD) (p D0 st0 : ℕ) (a b w : ℕ) :
    stSm d.FT (tr16 d.HT) (tr16 d.WT) d.ND d.NOM (f16 p a) (f16 p b) D0 (f16 p w) st0 =
      stSm d.FT d.HT d.WT d.ND d.NOM (f16 p a) (f16 p b) D0 (f16 p w) st0 := by
  unfold stSm hdrIn
  rw [tr16_f16, tr16_f16, tr16_f16]

theorem jAx_cut (d : MD) (m : Bool) (p st0 : ℕ) (a b : ℕ) :
    jAx d.FT (tr16 d.HT) m d.ND d.NOM (f16 p a) (f16 p b) st0 =
      jAx d.FT d.HT m d.ND d.NOM (f16 p a) (f16 p b) st0 := by
  unfold jAx
  rw [tr16_f16, tr16_f16]

theorem mNs_cut (d : MD) (p o : ℕ) (s : St4) : mNs (tr16 d.SG) (f16 p o) s = mNs d.SG (f16 p o) s := by
  unfold mNs
  rw [tr16_f16]

theorem mStep_cut (d : MD) (k : KD) : mStep (dCut d) k = mStep d k := by
  funext tr c p q
  unfold mStep
  dsimp only [dCut]
  simp only [stSm_cut, jAx_cut, mNs_cut]

theorem runM_cut (d : MD) (k : KD) (l : List ℕ) (x : ℕ) : runM (dCut d) k l x = runM d k l x := by
  unfold runM chunkM
  rw [mStep_cut]

theorem runT_cut (d : MD) (k : KD) (l : List ℕ) (x : ℕ) : runT (dCut d) k l x = runT d k l x := by
  unfold runT chunkM
  rw [mStep_cut]

section Env

variable {d : MD} {k : KD} {G : Type} [Group G] {φ : Nhat k.LET →* G} {x y t : G}

theorem env_cut (hS : kSetup k = true) (hM : mSetup d k = true) (hF : j4MFix k d = true)
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hStab : ∀ g : Nhat k.LET, (fun v => v ᵥ* ((g : GLm) : Mat12)) '' ptVecs k.TH = ptVecs k.TH →
      φ g * t = t * φ g) : Env (dCut d) φ x y t k.TH := by
  obtain ⟨-, hx, hy, -, -, -, -⟩ := kSetup_parts hS
  obtain ⟨-, hT, -⟩ := kSetup_more hS
  obtain ⟨hH, hO, hSG, -, -, -, -, hND, -⟩ := mSetup_parts hM
  obtain ⟨bH, bSG, -, -, zH, zSG, -⟩ := mfix_parts hF
  have hdr := hdr_mem hx hy hφx hφy hH
  have hdr' : ∀ i < (dCut d).nH, InN k.LET (hMat ((dCut d).HT i)) := fun i hi => by
    change InN k.LET (hMat (tr16 d.HT i))
    rw [tr16_of (by change i < d.nH at hi; omega)]
    exact (hdr i hi).1
  have hz : ∀ a, (dCut d).nH ≤ a → (dCut d).HT a = 0 := tr16_zero zH
  have hO' : ∀ j < (dCut d).NOM, omAtm (dCut d).HT (dCut d).OT k.TH j = true := fun j hj => by
    change omOKm (tr16 d.HT) k.TH j (d.OT j) = true
    unfold omOKm
    rw [tr16_oH]
    exact hO j hj
  have hSG' : ∀ e < (dCut d).nSG, segAt (dCut d).SG k.LET e = true := fun e he => by
    change segOK k.LET (tr16 d.SG e) = true
    rw [tr16_of (by change e < d.nSG at he; omega)]
    exact hSG e he
  exact { nd := hND, th := hT, ht := ht
          stab := fun m ⟨g, hg⟩ hmap => by
            rw [← hg] at hmap
            rw [ev_eq φ g hg]
            exact hStab g hmap
          hdr := hdr'
          hdr0 := hz
          om := om_mem hT hdr' hz hO'
          seg := seg_mem hx hy hφx hφy hSG' (tr16_zero zSG) }

theorem rel12_of (hS : kSetup k = true) (hRg : kRange k = true)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) (r : ℕ) (hr : r < 12) :
    wW (k.RT r) < 256 ^ wN (k.RT r) ∧ wv (jv x y t 1) (wW (k.RT r)) (wN (k.RT r)) = 1 := by
  obtain ⟨-, -, -, -, -, hrel, -⟩ := kSetup_parts hS
  have h := hrel r hr
  change andB _ _ = true at h
  obtain ⟨hf, -⟩ := andB_eq_true.1 h
  refine ⟨CFSG.Certificates.J4KShape.wFits_spec hf, ?_⟩
  rw [← wv_lvE_of (CFSG.Certificates.J4KShape.letsBelow_spec _ (kRange_lets hRg r hr))]
  exact hR r hr

theorem env2_cut (hS : kSetup k = true) (hRg : kRange k = true) (hM : mSetup d k = true)
    (hF : j4MFix k d = true)
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1) : Env2 (dCut d) k.LET x y t := by
  obtain ⟨-, hx, hy, -, -, -, -⟩ := kSetup_parts hS
  obtain ⟨hI, -, -⟩ := kSetup_more hS
  obtain ⟨hH, -, -, hW, -, -, hnd0, -, hnf⟩ := mSetup_parts hM
  obtain ⟨bH, -, bW, hwr, -, -, zW, -⟩ := mfix_parts hF
  have hdr := hdr_mem hx hy hφx hφy hH
  refine { hdrI := fun i hi => ?_, words := fun w => ?_, nd0 := hnd0, nf := hnf }
  · change InN k.LET (hInv (tr16 d.HT i))
    rw [tr16_of (by change i < d.nH at hi; omega)]
    exact (hdr i hi).2
  · change wW (tr16 d.WT w) < 256 ^ wN (tr16 d.WT w) ∧
      wv (fv x y t) (wW (tr16 d.WT w)) (wN (tr16 d.WT w)) = 1
    rcases Nat.lt_or_ge w d.nW with hw | hw
    · rw [tr16_of (by omega)]
      have h := hW w hw
      unfold wordAt wordOK at h
      rw [letB_eq] at h
      obtain ⟨hf, hc⟩ := andB_eq_true.1 h
      refine ⟨CFSG.Certificates.J4KShape.wFits_spec hf, ?_⟩
      rw [hI] at hc
      have hr := rel12_of hS hRg hR _ (hwr w hw)
      exact CFSG.Certificates.J4Words.chkWord_val (jv x y t 1) hr.1 hr.2
        (fun q _ _ => (jv_inv x y t 1 ht _).2) hc
    · rw [tr16_zero zW w hw]
      have e : wN 0 = 0 := by decide
      refine ⟨by decide, ?_⟩
      rw [e, wv_zero]

end Env

theorem mlevel_sound_fix {G : Type} [Group G] {k : KD} {d : MD} {MW MT : List ℕ}
    (hS : kSetup k = true) (hRg : kRange k = true) (hM : mSetup d k = true)
    (hMW : runM d k MW (mkC 0 1) = mkC d.NF d.ND) (hMT : runT d k MT 0 = 89)
    (hF : j4MFix k d = true)
    (φ : Nhat k.LET →* G) (x y t : G)
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1)
    (hStab : ∀ g : Nhat k.LET, (fun v => v ᵥ* ((g : GLm) : Mat12)) '' ptVecs k.TH = ptVecs k.TH →
      φ g * t = t * φ g) :
    ∀ r < 89, rv (jv x y t (zv x y t)) (k.RZT r) = 1 := by
  have E := env_cut (d := d) hS hM hF hφx hφy ht hStab
  have E2 := env2_cut (d := d) hS hRg hM hF hφx hφy ht hR
  have hMW' : runM (dCut d) k MW (mkC 0 1) = mkC (dCut d).NF (dCut d).ND := (runM_cut d k MW _).trans hMW
  have hMT' : runT (dCut d) k MT 0 = 89 := (runT_cut d k MT 0).trans hMT
  obtain ⟨hI, -, -⟩ := kSetup_more hS
  obtain ⟨-, -, -, -, hZW, hL, -⟩ := mSetup_parts hM
  have htw : ∀ i < 89, wW ((dCut d).TW i) < 256 ^ wN ((dCut d).TW i) := fun i hi => by
    have h := hL i hi
    unfold linkAt at h
    rw [letB_eq, letB_eq] at h
    exact CFSG.Certificates.J4KShape.wFits_spec (andB_eq_true.1 h).1
  obtain ⟨w, hw0, hw⟩ := facts_hold (facts_run E E2 hMW')
  have hT := traces_run E E2.nd0 E2.nf hw hw0 htw hMT'
  intro r hr
  have h := hL r hr
  unfold linkAt at h
  rw [letB_eq, letB_eq] at h
  obtain ⟨-, -, hc⟩ := (andB_eq_true.1 h).imp_right andB_eq_true.1
  rw [hZW, hI] at hc
  have key := CFSG.Certificates.J4Words.chkSubstRed_val (jv x y t 1)
    (fun c _ => (jv_inv x y t 1 ht c).2) zw_fit (CFSG.Certificates.J4Words.wInv_lt _ _ _) hc
  have hZi : wv (lvE (jv x y t 1)) (wInv invJ (wW (zWord invJ)) (wN (zWord invJ))) (wN (zWord invJ)) =
      (wv (lvE (jv x y t 1)) (wW (zWord invJ)) (wN (zWord invJ)))⁻¹ :=
    CFSG.Certificates.J4Words.wv_wInv _ invJ _ _ fun q hq => by
      have h5 := zw_lets q hq
      obtain ⟨hl, hv⟩ := jv_inv x y t 1 ht (wLet (wW (zWord invJ)) q)
      have hne1 : lInv invJ (wLet (wW (zWord invJ)) q) ≠ 255 := by omega
      have hne2 : wLet (wW (zWord invJ)) q ≠ 255 := by omega
      simp only [lvE, hne1, hne2, ↓reduceIte]
      exact hv
  have hgoal : rv (jv x y t (zv x y t)) (k.RZT r) =
      wv (lvE (CFSG.Certificates.J4Words.zsub (jv x y t 1)
        (wv (lvE (jv x y t 1)) (wW (zWord invJ)) (wN (zWord invJ)))
        (wv (lvE (jv x y t 1)) (wInv invJ (wW (zWord invJ)) (wN (zWord invJ))) (wN (zWord invJ)))))
        (wW (k.RZT r)) (wN (k.RZT r)) := by
    rw [hZi, zsub_eq]
    rfl
  exact hgoal.trans (key.trans (hT r hr))

theorem mlevel_psi_fix {G : Type} [Group G] {k : KD} {d : MD} {MW MT : List ℕ}
    (hS : kSetup k = true) (hRg : kRange k = true) (hM : mSetup d k = true)
    (hMW : runM d k MW (mkC 0 1) = mkC d.NF d.ND) (hMT : runT d k MT 0 = 89)
    (hF : j4MFix k d = true)
    (φ : Nhat k.LET →* G) (x y t : G)
    (hφx : ∀ g : Nhat k.LET, (g : GLm) = xh k.LET → φ g = x)
    (hφy : ∀ g : Nhat k.LET, (g : GLm) = yh k.LET → φ g = y) (ht : t * t = 1)
    (hR : ∀ r < 12, rv (jv x y t 1) (k.RT r) = 1)
    (hStab : ∀ g : Nhat k.LET, (fun v => v ᵥ* ((g : GLm) : Mat12)) '' ptVecs k.TH = ptVecs k.TH →
      φ g * t = t * φ g) :
    rv (jv x y t (zv x y t)) (psiWord invJ k.PAW k.PBW) = 1 := by
  have h := mlevel_sound_fix hS hRg hM hMW hMT hF φ x y t hφx hφy ht hR hStab 88 (by norm_num)
  obtain ⟨hI, -, h88⟩ := kSetup_more hS
  rwa [h88, hI] at h

end CFSG.KJ4.MLevel

end
