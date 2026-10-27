module

public import Certificates.Data.Kernel.FzUT.FusionP
public import CFSG.Certificates.Kernel.FzUT.Fusion

public section

namespace CFSG.KC.FzUT

open Certificates.FzR10 CFSG.OddStandard.SmallF3.FritzII

theorem sbB_eq (h : Nat) (k : Nat → Bool) : sbB h k = k h := by
  cases h <;> rfl

theorem fldN_le (P w m i : Nat) : fldN P w m i ≤ m := Nat.and_le_right

theorem fp_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := by simpa using h

theorem fp_ble {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := by simpa using h

theorem fp_ble' {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by simpa using h

theorem fp_bits : allN 32 (fun a => allN 32 fun c => allN 5 fun j =>
    beqB (parN (Nat.land a (Nat.xor c (Nat.shiftLeft 1 j))))
      (bxor (parN (Nat.land a c)) (bitN a j))) = true := by
  decide +kernel

theorem fp_lt : allN 32 (fun b => allN 8 fun r =>
    bimp (allN 5 fun j => bimp (Nat.ble r j) (bnot (bitN b j))) (Nat.blt b (Nat.shiftLeft 1 r)))
      = true := by
  decide +kernel

theorem fp_ex : ∀ b0 b1 b2 b3 b4 : Bool, ∃ a, a < 32 ∧ bitN a 0 = b0 ∧ bitN a 1 = b1 ∧
    bitN a 2 = b2 ∧ bitN a 3 = b3 ∧ bitN a 4 = b4 := by
  decide +kernel

theorem fp_lt16 : allN 32 (fun a => bimp (bnot (bitN a 4)) (Nat.blt a 16)) = true := by
  decide +kernel

theorem parN_flip {a c j : Nat} (ha : a < 32) (hc : c < 32) (hj : j < 5) :
    parN (Nat.land a (Nat.xor c (Nat.shiftLeft 1 j))) = xor (parN (Nat.land a c)) (bitN a j) := by
  have h := (allN_iff _ _).1 ((allN_iff _ _).1 ((allN_iff _ _).1 fp_bits a ha) c hc) j hj
  rw [beqB_iff, bxor_eq] at h
  exact h

theorem parN_zero (a : Nat) : parN (Nat.land a 0) = false := by
  rw [show Nat.land a 0 = 0 from Nat.and_zero a]
  decide +kernel

theorem fp_exists (b : Nat → Bool) : ∃ a, a < 32 ∧ ∀ j < 5, bitN a j = b j := by
  obtain ⟨a, ha, h0, h1, h2, h3, h4⟩ := fp_ex (b 0) (b 1) (b 2) (b 3) (b 4)
  refine ⟨a, ha, fun j hj => ?_⟩
  interval_cases j <;> assumption

theorem lt_of_bits {b r : Nat} (hb : b < 32) (hr : r < 8)
    (h : ∀ j < 5, r ≤ j → bitN b j = false) : b < Nat.shiftLeft 1 r := by
  have h' := (allN_iff _ _).1 ((allN_iff _ _).1 fp_lt b hb) r hr
  rw [bimp_iff] at h'
  have := h' ((allN_iff _ _).2 fun j hj => by
    rw [bimp_iff, bnot_iff]
    intro hrj
    exact h j hj (fp_ble hrj))
  exact fp_blt this

section Tree

variable {T S L TR n : Nat} {A : Nat → Bool} {G cd : Nat → Nat}

theorem tree_sound (hst : ∀ x < 512, A x = true → tstep T S L TR n A G cd x = true)
    (hcd : ∀ x, cd x < 32) (hn : n ≤ 5) (h00 : emP T S L 0 0 = 0) (f : Nat → Bool)
    (hf : ∀ x y, x < 512 → y < 512 → A x = true → A y = true →
      f (emP T S L x y) = xor (f x) (f y))
    (hG : ∀ j < n, A (G j) = true ∧ G j < 512) {a : Nat} (ha32 : a < 32)
    (ha : ∀ j < n, bitN a j = f (G j)) :
    ∀ x < 512, A x = true → f x = parN (Nat.land a (cd x)) := by
  suffices h : ∀ d, ∀ x < 512, A x = true → tdep TR x = d → f x = parN (Nat.land a (cd x)) from
    fun x hx hA => h _ x hx hA rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x hx hA hd
  have h := hst x hx hA
  unfold tstep at h
  rw [bor_iff, band_iff, band_iff, beq_iff, beq_iff, band_iff, Nat.blt_eq, band_iff, band_iff,
    beq_iff, band_iff, beq_iff, beq_iff] at h
  rcases h with ⟨-, rfl, h0⟩ | ⟨hg, hp, hdp, hx', hc⟩
  · have := hf 0 0 (by omega) (by omega) hA hA
    rw [h00] at this
    rw [h0, parN_zero]
    cases h' : f 0 <;> simp_all
  · have hp5 : tpar TR x < 512 := Nat.lt_succ_of_le (fldN_le _ _ _ _)
    have hdp' : tdep TR (tpar TR x) + 1 = tdep TR x := hdp
    rw [beq_iff] at hc
    have ihp := ih _ (by omega) _ hp5 hp rfl
    have hgn := hG _ hg
    rw [hx', hf _ _ hp5 hgn.2 hp hgn.1, ihp, ← ha _ hg, ← hx', hc,
      parN_flip ha32 (hcd _) (by omega)]

end Tree

section Sub

variable {P : Par} {T S L XT : Nat}

theorem xc_lt (XT x : Nat) : xc XT x < 32 := by
  have := fldN_le (Nat.shiftRight (xtr XT x) 1) 4 15 0
  unfold xc
  omega

theorem xd_lt (XT a x : Nat) : xd XT a x < 32 := Nat.lt_succ_of_le (fldN_le _ _ _ _)

theorem cmN_iff (T S L x y : Nat) : cmN T S L x y = true ↔ emP T S L x y = emP T S L y x :=
  beq_iff _ _

theorem emP_zero (T S L : Nat) : emP T S L 0 0 = 0 := by
  have h : Nat.beq 0 1 = false := rfl
  unfold emP actP apC
  simp only [Nat.zero_and, Nat.zero_shiftRight, h]
  decide +kernel

theorem fp_beq_f {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem xS_iff (hxt : xtOK T S L XT = true) {x : Nat} (hx : x < 512) :
    xS XT x = true ↔ emP T S L x 64 = emP T S L 64 x := by
  have h := (allN_iff _ _).1 hxt x hx
  rw [band_iff, beqB_iff] at h
  rw [h.1, cmN_iff]

theorem xk_eq (hxt : xtOK T S L XT = true) {x : Nat} (hx : x < 512) :
    xk XT x = kordN T S L x := by
  have h := (allN_iff _ _).1 hxt x hx
  rw [band_iff, beq_iff] at h
  exact h.2

theorem kordN_two (T S L x : Nat) : kordN T S L x = 2 ↔ x ≠ 0 ∧ emP T S L x x = 0 := by
  unfold kordN sqN
  by_cases h1 : x = 0
  · subst h1
    rw [Nat.beq_refl]
    simp
  · rw [fp_beq_f h1]
    by_cases h2 : emP T S L x x = 0
    · rw [h2, Nat.beq_refl]
      simp [h1]
    · rw [fp_beq_f h2]
      cases Nat.beq (emP T S L (emP T S L x x) (emP T S L x x)) 0 <;>
        cases Nat.beq (emP T S L (emP T S L (emP T S L x x) (emP T S L x x))
          (emP T S L (emP T S L x x) (emP T S L x x))) 0 <;> simp [h2]

theorem invB_iff (T S L x : Nat) : invB T S L x = true ↔ x ≠ 0 ∧ emP T S L x x = 0 := by
  unfold invB
  rw [band_iff, bnot_iff, beq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, h2⟩
    rw [h, Nat.beq_refl] at h1
    exact Bool.noConfusion h1
  · rintro ⟨h1, h2⟩
    exact ⟨fp_beq_f h1, h2⟩

variable (hE : ∀ x y, x < 512 → y < 512 → P.e x y = emP T S L x y) (htI : P.tI = 64)
  (hxt : xtOK T S L XT = true)
include hE htI hxt

theorem fzrS_iff {x : Nat} : fzrS P x ↔ x < 512 ∧ xS XT x = true := by
  unfold fzrS
  rw [htI]
  constructor
  · rintro ⟨hx, h⟩
    rw [hE _ _ hx (by omega), hE _ _ (by omega) hx] at h
    exact ⟨hx, (xS_iff hxt hx).2 h⟩
  · rintro ⟨hx, h⟩
    rw [hE _ _ hx (by omega), hE _ _ (by omega) hx]
    exact ⟨hx, (xS_iff hxt hx).1 h⟩

theorem f0_code {GS TS : Nat} (hts : treeSOK T S L XT GS TS = true) (f : Nat → Bool)
    (hf : ∀ x y, fzrS P x → fzrS P y → f (P.e x y) = xor (f x) (f y)) :
    ∃ a, a < 16 ∧ ∀ x < 512, xS XT x = true → f x = parN (Nat.land a (xc XT x)) := by
  obtain ⟨a, ha, hb⟩ := fp_exists fun j => if j < 4 then f (fldN GS 9 511 j) else false
  unfold treeSOK at hts
  rw [band_iff, allN_iff, allN_iff] at hts
  have h16 : a < 16 := by
    have h := (allN_iff _ _).1 fp_lt16 a ha
    rw [bimp_iff, bnot_iff] at h
    exact fp_blt (h (by simpa using hb 4 (by omega)))
  refine ⟨a, h16, tree_sound (fun x hx hA => (bimp_iff _ _).1 (hts.2 x hx) hA) (xc_lt XT)
    (by omega) (emP_zero T S L) f ?_ ?_ ha ?_⟩
  · intro x y hx hy hAx hAy
    rw [← hE _ _ hx hy]
    exact hf x y ((fzrS_iff hE htI hxt).2 ⟨hx, hAx⟩) ((fzrS_iff hE htI hxt).2 ⟨hy, hAy⟩)
  · exact fun j hj => ⟨hts.1 j hj, Nat.lt_succ_of_le (fldN_le _ _ _ _)⟩
  · intro j hj
    rw [hb j (by omega)]
    simp [hj]

theorem f1_code {GK RK TK a : Nat} (htk : treeKOK T S L XT GK RK TK a = true) (f : Nat → Bool)
    (hf : ∀ x y, x < 512 → y < 512 → inK XT a x = true → inK XT a y = true →
      f (P.e x y) = xor (f x) (f y)) :
    ∃ b, b < 32 ∧ b < Nat.shiftLeft 1 (rk RK a) ∧ ∀ x < 512, inK XT a x = true →
      f x = parN (Nat.land b (xd XT a x)) := by
  obtain ⟨b, hb, hbj⟩ := fp_exists fun j => f (kgen GK a j)
  unfold treeKOK at htk
  rw [band_iff, allN_iff, allN_iff] at htk
  have hf' : ∀ x y, x < 512 → y < 512 → inK XT a x = true → inK XT a y = true →
      f (emP T S L x y) = xor (f x) (f y) := fun x y hx hy h1 h2 => by
    rw [← hE _ _ hx hy]
    exact hf x y hx hy h1 h2
  have hG : ∀ j < 5, inK XT a (kgen GK a j) = true ∧ kgen GK a j < 512 := fun j hj =>
    ⟨((band_iff _ _).1 (htk.1 j hj)).1, Nat.lt_succ_of_le (fldN_le _ _ _ _)⟩
  have hf0 : inK XT a 0 = true → f 0 = false := fun h0 => by
    have := hf' 0 0 (by omega) (by omega) h0 h0
    rw [emP_zero] at this
    cases h' : f 0 <;> simp_all
  refine ⟨b, hb, lt_of_bits hb (Nat.lt_succ_of_le (fldN_le _ _ _ _)) fun j hj hrj => ?_,
    tree_sound (fun x hx hA => (bimp_iff _ _).1 (htk.2 x hx) hA) (xd_lt XT a) (le_refl 5)
      (emP_zero T S L) f hf' hG hb fun j hj => hbj j hj⟩
  have hk : kgen GK a j = 0 :=
    (beq_iff _ _).1 ((bimp_iff _ _).1 ((band_iff _ _).1 (htk.1 j hj)).2 (fp_ble' hrj))
  have h0 := (hG j hj).1
  rw [hk] at h0
  rw [hbj j hj, hk, hf0 h0]

end Sub

theorem histN_eq (f : Nat → Bool) (ky : Nat → Nat) :
    histN f ky = ∑ x ∈ (Finset.range 512).filter (fun x => f x = true), 2 ^ (10 * ky x) := by
  let R : Nat → Nat := fun n => Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec acc (Nat.add acc (Nat.shiftLeft 1 (Nat.mul 10 (ky i)))) (f i)) n
  suffices h : ∀ n, R n = ∑ x ∈ (Finset.range n).filter (fun x => f x = true), 2 ^ (10 * ky x)
    from h 512
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : R (n + 1) = Bool.rec (motive := fun _ => Nat) (R n)
        (Nat.add (R n) (Nat.shiftLeft 1 (Nat.mul 10 (ky n)))) (f n) := rfl
    rw [e, Finset.range_add_one, Finset.filter_insert]
    cases h : f n
    · rw [if_neg (by simp)]
      exact ih
    · have e2 : Nat.shiftLeft 1 (Nat.mul 10 (ky n)) = 2 ^ (10 * ky n) := by
        have := Nat.shiftLeft_eq 1 (10 * ky n)
        rw [one_mul] at this
        exact this
      rw [if_pos rfl, Finset.sum_insert (by simp), ← ih]
      change Nat.add (R n) (Nat.shiftLeft 1 (Nat.mul 10 (ky n))) = _
      rw [e2, Nat.add_eq, add_comm]

theorem sum_key_eq {A B : Finset ℕ} {κ : ℕ → ℕ} (hκ : ∀ x, κ x < 64)
    (h : ∀ k, (A.filter fun x => κ x = k).card = (B.filter fun x => κ x = k).card)
    (w : ℕ → ℕ) : ∑ x ∈ A, w (κ x) = ∑ x ∈ B, w (κ x) := by
  have e : ∀ C : Finset ℕ, ∑ x ∈ C, w (κ x) =
      ∑ k ∈ Finset.range 64, (C.filter fun x => κ x = k).card * w k := fun C => by
    rw [← Finset.sum_fiberwise_of_maps_to (s := C) (t := Finset.range 64) (g := κ)
      (fun x _ => Finset.mem_range.2 (hκ x))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => w k) fun x hx => by rw [(Finset.mem_filter.1 hx).2],
      Finset.sum_const, smul_eq_mul]
  rw [e A, e B]
  exact Finset.sum_congr rfl fun k _ => by rw [h k]

theorem keyN_lt (XT FR IN x : Nat) : keyN XT FR IN x < 64 := by
  have h := fldN_le (Nat.shiftRight (xtr XT x) 5) 5 31 0
  unfold keyN
  change xk XT x ≤ 31 at h
  cases thB XT FR IN x <;> simp only [Nat.add_eq, Nat.mul_eq] <;> omega

section Leaf

variable {P : Par} {θ : ℕ → Prop} {T S L FR XT DW nD IW nI U m IN : Nat}
  (hP : FuPar P T S L) (hR : FzRules P θ) (hxt : xtOK T S L XT = true)
  (hcls : ∀ x < 512, (θ x ↔ θ (fcls FR x))) (hdead : ∀ i < nD, ¬ θ (dwit DW i))
  (hU : ∀ j < 4, (θ (fldN U 9 511 j) ↔ bitN m j = true)) (hiw : iwOK T S L IW nI = true)
  (hl : leafOK T S L FR XT DW nD IW nI U m IN = true)
include hP hR hxt hcls hdead hU hiw hl

theorem leaf_sound : ∀ x < 512, (θ x ↔ thB XT FR IN x = true) := by
  intro x hx
  have hl' := (bimp_iff _ _).1 ((allN_iff _ _).1 hl x hx)
  unfold thB
  rw [band_iff, beq_iff, xk_eq hxt hx, kordN_two]
  by_cases hinv : x ≠ 0 ∧ emP T S L x x = 0
  · have hb := hl' (by rw [beq_iff, xk_eq hxt hx, kordN_two]; exact hinv)
    rw [hcls x hx]
    simp only [hinv, ne_eq, not_false_eq_true, and_self, true_and]
    cases hc : bitN IN (fcls FR x)
    · rw [hc] at hb
      change outC FR DW nD U m x = true at hb
      unfold outC at hb
      rw [bor_iff, anyN_iff, anyN_iff] at hb
      simp only [Bool.false_eq_true, iff_false]
      rcases hb with ⟨i, hi, he⟩ | ⟨j, hj, he⟩
      · rw [beq_iff] at he
        rw [← he, ← hcls (dwit DW i) (fl9_lt _ _)]
        exact hdead i hi
      · rw [band_iff, bnot_iff, beq_iff] at he
        rw [he.2, ← hcls (fldN U 9 511 j) (fl9_lt _ _), hU j hj, he.1]
        exact Bool.false_ne_true
    · rw [hc] at hb
      change inC T S L FR IW nI U m x = true at hb
      unfold inC at hb
      rw [bor_iff, bor_iff, beq_iff, anyN_iff, anyN_iff] at hb
      simp only [iff_true]
      rcases hb with he | ⟨i, hi, he⟩ | ⟨j, hj, he⟩
      · rw [he, ← hcls 64 (by omega), ← hP.tI]
        exact hR.th_t
      · rw [beq_iff] at he
        have hw := (allN_iff _ _).1 hiw i hi
        rw [band_iff, invB_iff] at hw
        have h5 : iwit IW i < 512 := fl9_lt IW i
        have hk := hR.ktl (iwit IW i) h5 (by rw [hP.inTL _ h5]; exact hw.1) hw.2.1
          (by rw [hP.e _ _ h5 h5]; exact hw.2.2)
        rw [hP.tI, hP.e _ _ (by omega) h5] at hk
        rw [he, ← hcls _ (emP_lt hP hR (by omega) h5)]
        exact hk
      · rw [band_iff, beq_iff] at he
        rw [he.2, ← hcls (fldN U 9 511 j) (fl9_lt _ _), hU j hj]
        exact he.1
  · simp only [hinv, false_and, iff_false]
    intro hθ
    obtain ⟨-, h0, h2⟩ := hR.th_inv x hθ
    rw [hP.e x x hx hx] at h2
    exact hinv ⟨h0, h2⟩

theorem killC_sound {FP FV : Nat} (hc : coverL T S L FR IN FP FV = true) : False := by
  have hth := leaf_sound hP hR hxt hcls hdead hU hiw hl
  unfold coverL at hc
  rw [band_iff, allN_iff] at hc
  obtain ⟨hfun, hall⟩ := hc
  have ht : fE FP FV P.tI = true := by
    simp only [funOK, band_iff] at hfun
    rw [hP.tI]
    exact hfun.2.2.2
  obtain ⟨x, hx, hθx, hfx⟩ := hR.cover _ (fun x y hx hy => fE_add hP hR hfun hx hy) ht
  obtain ⟨-, hx0, hxx⟩ := hR.th_inv x hθx
  have hinv : invB T S L x = true := by
    rw [invB_iff, ← hP.e x x hx hx]
    exact ⟨hx0, hxx⟩
  have h := (bimp_iff _ _).1 (hall x hx) (by rw [band_iff, bnot_iff]; exact ⟨hinv, hfx⟩)
  rw [bnot_iff] at h
  have h' := (hth x hx).1 hθx
  unfold thB at h'
  rw [band_iff, h] at h'
  exact Bool.false_ne_true h'.2

theorem killP_sound {GS TS GK RK TK u : Nat} (hts : treeSOK T S L XT GS TS = true)
    (htk : treesKOK T S L XT GK RK TK = true) (hp : profOK T S L XT FR IN RK u = true) :
    False := by
  have hth := leaf_sound hP hR hxt hcls hdead hU hiw hl
  have hE := hP.e
  have htI := hP.tI
  unfold profOK at hp
  rw [band_iff, band_iff, band_iff, blt_iff, ble_iff, sbB_eq, allN_iff] at hp
  obtain ⟨hu, hu5, hcnt, hall⟩ := hp
  have hθu : θ u := (hth u hu5).2 hu
  have hcent : fzrCent P u = (Finset.range 512).filter (fun x => cmN T S L x u = true) := by
    unfold fzrCent
    refine Finset.filter_congr fun x hx => ?_
    rw [Finset.mem_range] at hx
    rw [cmN_iff, hE x u hx hu5, hE u x hu5 hx]
  obtain ⟨f₀, f₁, hf0, hf1, h0t, h1t, -, hkey⟩ :=
    hR.prof u hθu (by rw [cent_card hP hR hu5]; exact hcnt)
  obtain ⟨a, ha16, ha⟩ := f0_code hE htI hxt hts f₀ hf0
  have h64 : (64 : Nat) < 512 := by omega
  have hS64 : xS XT 64 = true := (xS_iff hxt h64).2 rfl
  have hpa : parN (Nat.land a (xc XT 64)) = false := by
    rw [← ha 64 h64 hS64, ← htI]
    exact h0t
  have hall0 := hall a ha16
  rw [bor_iff, hpa] at hall0
  have hall' := (allN_iff _ _).1 (hall0.resolve_left Bool.false_ne_true)
  have htk' : treeKOK T S L XT GK RK TK a = true := by
    have h := (allN_iff _ _).1 htk a (by omega)
    rw [bor_iff, hpa] at h
    simpa using h
  have hK : ∀ x < 512, inK XT a x = true ↔ fzrS P x ∧ f₀ x = false := fun x hx => by
    unfold inK
    rw [band_iff, bnot_iff, fzrS_iff hE htI hxt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hx, h1⟩, by rw [ha x hx h1]; exact h2⟩
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h1, by rw [← ha x hx h1]; exact h2⟩
  obtain ⟨b, hb32, hb, hbf⟩ := f1_code hE htI hxt htk' f₁ fun x y hx hy h1 h2 =>
    hf1 x y ((hK x hx).1 h1).1 ((hK x hx).1 h1).2 ((hK y hy).1 h2).1 ((hK y hy).1 h2).2
  have hK64 : inK XT a 64 = true :=
    (hK 64 h64).2 ⟨(fzrS_iff hE htI hxt).2 ⟨h64, hS64⟩, by rw [← htI]; exact h0t⟩
  have hpb : parN (Nat.land b (xd XT a 64)) = false := by
    rw [← hbf 64 h64 hK64, ← htI]
    exact h1t
  have hH : fzrH P f₀ f₁ = (Finset.range 512).filter (fun x => hB XT a b x = true) := by
    unfold fzrH
    refine Finset.filter_congr fun x hx => ?_
    rw [Finset.mem_range] at hx
    unfold hB
    rw [band_iff, bnot_iff]
    constructor
    · rintro ⟨hS, h0, h1⟩
      have hk := (hK x hx).2 ⟨hS, h0⟩
      exact ⟨hk, by rw [← hbf x hx hk]; exact h1⟩
    · rintro ⟨hk, h1⟩
      have := (hK x hx).1 hk
      exact ⟨this.1, this.2, by rw [hbf x hx hk]; exact h1⟩
  have hkx : ∀ x < 512, fzrKey P θ x = keyN XT FR IN x := fun x hx => by
    unfold fzrKey keyN
    rw [kord_eq hP hR hx, ← xk_eq hxt hx]
    by_cases hθ : θ x
    · rw [if_pos hθ, (hth x hx).1 hθ]
      rfl
    · rw [if_neg hθ]
      cases h : thB XT FR IN x
      · rfl
      · exact absurd ((hth x hx).2 h) hθ
  have hfk : ∀ C : Finset ℕ, (∀ x ∈ C, x < 512) → ∀ k,
      (C.filter fun x => fzrKey P θ x = k) = (C.filter fun x => keyN XT FR IN x = k) :=
    fun C hC k => Finset.filter_congr fun x hx => by rw [hkx x (hC x hx)]
  have hHsub : ∀ x ∈ fzrH P f₀ f₁, x < 512 := fun x hx => by
    rw [hH, Finset.mem_filter, Finset.mem_range] at hx
    exact hx.1
  have hCsub : ∀ x ∈ fzrCent P u, x < 512 := fun x hx => by
    rw [hcent, Finset.mem_filter, Finset.mem_range] at hx
    exact hx.1
  have hsum : histN (hB XT a b) (keyN XT FR IN) =
      histN (fun x => cmN T S L x u) (keyN XT FR IN) := by
    rw [histN_eq, histN_eq, ← hH, ← hcent]
    refine sum_key_eq (keyN_lt XT FR IN) (fun k => ?_) (fun k => 2 ^ (10 * k))
    rw [← hfk _ hHsub, ← hfk _ hCsub]
    exact hkey k
  have h := hall' b hb32
  rw [bor_iff, bor_iff, ble_iff, hpb, bnot_iff, hsum, Nat.beq_refl] at h
  rcases h with h | h | h
  · omega
  · exact Bool.false_ne_true h
  · exact Bool.noConfusion h

end Leaf

theorem leaves_of {f : Nat → Bool} (h0 : allN 4 (fun i => f (Nat.add 0 i)) = true)
    (h4 : allN 4 (fun i => f (Nat.add 4 i)) = true) (h8 : allN 4 (fun i => f (Nat.add 8 i)) = true)
    (h12 : allN 4 (fun i => f (Nat.add 12 i)) = true) : ∀ m < 16, f m = true := by
  intro m hm
  rw [allN_iff] at h0 h4 h8 h12
  by_cases a : m < 4
  · simpa using h0 m a
  by_cases b : m < 8
  · have := h4 (m - 4) (by omega)
    rwa [show Nat.add 4 (m - 4) = m by simp only [Nat.add_eq]; omega] at this
  by_cases c : m < 12
  · have := h8 (m - 8) (by omega)
    rwa [show Nat.add 8 (m - 8) = m by simp only [Nat.add_eq]; omega] at this
  · have := h12 (m - 12) (by omega)
    rwa [show Nat.add 12 (m - 12) = m by simp only [Nat.add_eq]; omega] at this

theorem refute_leaves {P : Par} {T S L FR XT DW nD IW nI U GS TS GK RK TK LD : Nat}
    (hP : FuPar P T S L) (hF : forestOK T S L FR = true) (hD : deadOK T S L DW nD = true)
    (hiw : iwOK T S L IW nI = true) (hxt : xtOK T S L XT = true)
    (hts : treeSOK T S L XT GS TS = true) (htk : treesKOK T S L XT GK RK TK = true)
    (hL : ∀ m < 16, leafK T S L FR XT DW nD IW nI U RK LD m = true) :
    ¬ ∃ θ : ℕ → Prop, FzRules P θ := by
  classical
  rintro ⟨θ, hR⟩
  obtain ⟨m, hm32, hmb⟩ := fp_exists fun j => if j < 4 then decide (θ (fldN U 9 511 j)) else false
  have hm : m < 16 := by
    have h := (allN_iff _ _).1 fp_lt16 m hm32
    rw [bimp_iff, bnot_iff] at h
    exact fp_blt (h (by simpa using hmb 4 (by omega)))
  have hU : ∀ j < 4, (θ (fldN U 9 511 j) ↔ bitN m j = true) := fun j hj => by
    rw [hmb j (by omega)]
    simp [hj]
  have hcls := forest_sound hP hR hF
  have hdead := dead_sound hP hR hD
  have hk := hL m hm
  unfold leafK at hk
  cases hb : bitN (lrec LD m) 512
  · rw [hb] at hk
    change killP T S L FR XT DW nD IW nI U RK m _ _ = true at hk
    unfold killP at hk
    rw [band_iff] at hk
    exact killP_sound hP hR hxt hcls hdead hU hiw hk.1 hts htk hk.2
  · rw [hb] at hk
    change killC T S L FR XT DW nD IW nI U m _ _ _ = true at hk
    unfold killC at hk
    rw [band_iff] at hk
    exact killC_sound hP hR hxt hcls hdead hU hiw hk.1 hk.2

end CFSG.KC.FzUT
