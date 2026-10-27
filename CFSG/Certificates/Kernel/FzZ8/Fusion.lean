module

public import Certificates.Data.Kernel.FzZ8.Fusion
public import CFSG.Certificates.Kernel.FzUT.FusionP

public section

namespace CFSG.KC.FzZ8

open Certificates.FzR10 CFSG.OddStandard.SmallF3.FritzII
open CFSG.KC.FzUT (bor_iff bxor_eq beqB_iff blt_iff ble_iff beq_false_iff fl9_lt and63 shr6
  band_iff beq_iff bnot_iff bimp_iff allN_iff anyN_iff cntN_eq sbB_eq fldN_le fp_blt fp_ble
  fp_ble' parN_flip parN_zero fp_exists lt_of_bits xc_lt xd_lt fp_beq_f histN_eq sum_key_eq
  keyN_lt band bimp bnot allN anyN fldN bor bxor beqB bitN cntN fE frec fcls fdep fpar fkind faux
  dwit dkind dord parN xtr xS xc xk xd trec tpar tgen tdep inK kgen rk thB keyN histN hB sbB iwit
  lrec lIN)

structure FuParG (P : Par) (e : Nat → Nat → Nat) (tl wt tz : Nat → Bool) (rh : Nat → Nat)
    (pm ac : Nat → Nat → Nat) : Prop where
  he : ∀ x y, x < 512 → y < 512 → P.e x y = e x y
  tI : P.tI = 64
  sI : P.sI = 128
  inTL : ∀ x < 512, P.inTL x = tl x
  inW : ∀ x < 512, P.inW x = wt x
  inTZ : ∀ x < 512, P.inTZ x = tz x
  rho : ∀ x < 256, P.rhoMap x = rh x
  split : ∀ x y, x < 512 → y < 512 →
    e x y = pm (x &&& 63) (ac (x >>> 6) (y &&& 63)) + 64 * ((x >>> 6) ^^^ (y >>> 6))

section Sound

variable {P : Par} {e : Nat → Nat → Nat} {tl wt tz : Nat → Bool} {rh : Nat → Nat}
  {pm ac : Nat → Nat → Nat} {θ : ℕ → Prop} (hP : FuParG P e tl wt tz rh pm ac)
  (hθ : FzRules P θ)
include hP hθ

theorem e_lt {x y : Nat} (hx : x < 512) (hy : y < 512) : e x y < 512 := by
  rw [← hP.he x y hx hy]
  exact hθ.mul.lt x y hx hy

theorem kout_sound {sp a : Nat} (hsp : sp = P.sI ∨ sp = P.e P.tI P.sI) (hsp5 : sp < 512)
    (ha : a < 512) (htl : tl a = true) (h2 : e (e a sp) (e a sp) = 0) :
    θ (e a sp) ↔ θ sp := by
  have hl := e_lt hP hθ ha hsp5
  have := hθ.kout sp hsp a ha (by rw [hP.inTL a ha]; exact htl)
    (by rw [hP.he a sp ha hsp5, hP.he _ _ hl hl]; exact h2)
  rw [hP.he a sp ha hsp5] at this
  exact this

theorem edge_sound {k a x y : Nat} (ha : a < 512) (hx : x < 512) (hy : y < 512)
    (h : fuEdgeG e tl rh k a x y = true) : θ x ↔ θ y := by
  have h1 : (128 : Nat) = P.sI ∨ (128 : Nat) = P.e P.tI P.sI := Or.inl hP.sI.symm
  have h2 : e 64 128 = P.sI ∨ e 64 128 = P.e P.tI P.sI := by
    right
    rw [hP.tI, hP.sI, hP.he 64 128 (by norm_num) (by norm_num)]
  have h25 : e 64 128 < 512 := e_lt hP hθ (by norm_num) (by norm_num)
  simp only [fuEdgeG, koutG, bor_iff, band_iff, beq_iff, blt_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, hx2, rfl⟩ | ⟨-, hy2, rfl⟩ | ⟨-, htl, rfl, h', rfl⟩ |
    ⟨-, htl, rfl, h', rfl⟩ | ⟨-, htl, rfl, h', rfl⟩ | ⟨-, htl, rfl, h', rfl⟩
  · exact hθ.conj a x y ha hx hy (by rw [hP.he y a hy ha, hP.he a x ha hx]; exact h)
  · exact (hθ.conj a y x ha hy hx (by rw [hP.he x a hx ha, hP.he a y ha hy]; exact h)).symm
  · rw [← hP.rho x hx2]
    exact hθ.rho x hx2
  · rw [← hP.rho y hy2]
    exact (hθ.rho y hy2).symm
  · exact kout_sound hP hθ h1 (by norm_num) ha htl h'
  · exact (kout_sound hP hθ h1 (by norm_num) ha htl h').symm
  · exact kout_sound hP hθ h2 h25 ha htl h'
  · exact (kout_sound hP hθ h2 h25 ha htl h').symm

theorem forest_sound {FR : Nat} (hF : forestG e tl rh FR = true) :
    ∀ x < 512, θ x ↔ θ (fcls FR x) := by
  unfold forestG at hF
  rw [allN_iff] at hF
  suffices key : ∀ d x, x < 512 → fdep FR x = d → (θ x ↔ θ (fcls FR x)) from
    fun x hx => key _ x hx rfl
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih x hx hd
  have hr := hF x hx
  simp only [recG, bor_iff, band_iff, beq_iff] at hr
  rcases hr with ⟨-, hc, -⟩ | ⟨hdp, hcp, he⟩
  · rw [hc]
  · have hp5 : fpar FR x < 512 := fl9_lt _ _
    rw [edge_sound hP hθ (fl9_lt _ _) hx hp5 he,
      ih (fdep FR (fpar FR x)) (by omega) _ hp5 rfl, hcp]

theorem kord_eq {x : Nat} (hx : x < 512) : kord P.e x = kordG e x := by
  have l1 := e_lt hP hθ hx hx
  have l2 := e_lt hP hθ l1 l1
  have e1 := hP.he x x hx hx
  have e2 := hP.he _ _ l1 l1
  have e3 := hP.he _ _ l2 l2
  unfold kord kordG
  rw [e1, e2, e3]
  by_cases a : x = 0
  · rw [if_pos a, (beq_iff x 0).mpr a]
  rw [if_neg a, (beq_false_iff x 0).mpr a]
  by_cases b : e x x = 0
  · rw [if_pos b, (beq_iff _ 0).mpr b]
  rw [if_neg b, (beq_false_iff _ 0).mpr b]
  by_cases c : e (e x x) (e x x) = 0
  · rw [if_pos c, (beq_iff _ 0).mpr c]
  rw [if_neg c, (beq_false_iff _ 0).mpr c]
  by_cases d : e (e (e x x) (e x x)) (e (e x x) (e x x)) = 0
  · rw [if_pos d, (beq_iff _ 0).mpr d]
  rw [if_neg d, (beq_false_iff _ 0).mpr d]

theorem cent_card {w : Nat} (hw : w < 512) :
    (fzrCent P w).card = cntN 512 fun x => cmG e x w := by
  rw [cntN_eq]
  unfold fzrCent cmG
  refine congrArg Finset.card (Finset.filter_congr fun x hx => ?_)
  rw [Finset.mem_range] at hx
  rw [beq_iff, hP.he x w hx hw, hP.he w x hw hx]

theorem cntC_eq {w o : Nat} (hw : w < 512) :
    cntCG e w o = ((fzrCent P w).filter fun x => kord P.e x = o).card := by
  unfold cntCG
  rw [cntN_eq]
  unfold fzrCent cmG
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr fun x hx => ?_)
  rw [Finset.mem_range] at hx
  rw [band_iff, beq_iff, beq_iff, kord_eq hP hθ hx, hP.he x w hx hw, hP.he w x hw hx]

open Classical in
theorem key_split (A : Finset ℕ) (o : Nat) :
    (A.filter fun x => kord P.e x = o).card =
      (A.filter fun x => fzrKey P θ x = 2 * o + 1).card +
        (A.filter fun x => fzrKey P θ x = 2 * o).card := by
  have e1 : (A.filter fun x => kord P.e x = o ∧ θ x) =
      A.filter fun x => fzrKey P θ x = 2 * o + 1 := by
    refine Finset.filter_congr fun x _ => ?_
    unfold fzrKey
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_pos h2]
      omega
    · intro h1
      by_cases h2 : θ x
      · rw [if_pos h2] at h1
        exact ⟨by omega, h2⟩
      · rw [if_neg h2] at h1
        omega
  have e2 : (A.filter fun x => kord P.e x = o ∧ ¬ θ x) =
      A.filter fun x => fzrKey P θ x = 2 * o := by
    refine Finset.filter_congr fun x _ => ?_
    unfold fzrKey
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_neg h2]
      omega
    · intro h1
      by_cases h2 : θ x
      · rw [if_pos h2] at h1
        omega
      · rw [if_neg h2] at h1
        exact ⟨by omega, h2⟩
  rw [← Finset.card_filter_add_card_filter_not (s := A.filter fun x => kord P.e x = o)
    (fun x => θ x), Finset.filter_filter, Finset.filter_filter, e1, e2]

theorem kill_sound {w k o : Nat} (hw : w < 512) (h : killG e tl wt tz w k o = true) : ¬ θ w := by
  simp only [killG, invG, bor_iff, band_iff, beq_iff, bnot_iff, beq_false_iff, ble_iff,
    blt_iff] at h
  rcases h with ⟨-, htl, h0, h2⟩ | ⟨-, hw', hz⟩ | ⟨-, hc, hlt⟩
  · exact hθ.forb w hw (by rw [hP.inTL w hw]; exact htl) h0 (by rw [hP.he w w hw hw]; exact h2)
  · intro hθw
    have := hθ.wrule w (by rw [hP.inW w hw]; exact hw') hθw
    rw [hP.inTZ w hw, hz] at this
    exact Bool.false_ne_true this
  · intro hθw
    have hc' : 32 ≤ (fzrCent P w).card := by
      rw [cent_card hP hθ hw]
      exact hc
    obtain ⟨f₀, f₁, -, -, -, -, -, hkey⟩ := hθ.prof w hθw hc'
    have e1 := key_split hP hθ (fzrH P f₀ f₁) o
    have e2 := key_split hP hθ (fzrCent P w) o
    rw [hkey, hkey] at e1
    have sub : ((fzrH P f₀ f₁).filter fun x => kord P.e x = o).card ≤
        ((fzrCent P 64).filter fun x => kord P.e x = o).card := by
      refine Finset.card_le_card fun x hx => ?_
      simp only [fzrH, fzrCent, fzrS, Finset.mem_filter, Finset.mem_range, hP.tI] at hx ⊢
      exact ⟨⟨hx.1.1, hx.1.2.1.2⟩, hx.2⟩
    rw [cntC_eq hP hθ (by norm_num), cntC_eq hP hθ hw] at hlt
    omega

theorem dead_sound {DW n : Nat} (hD : deadG e tl wt tz DW n = true) :
    ∀ i < n, ¬ θ (dwit DW i) := by
  unfold deadG at hD
  rw [allN_iff] at hD
  exact fun i hi => kill_sound hP hθ (fl9_lt _ _) (hD i hi)

theorem fE_add {FP FV : Nat} (hfun : funG pm ac FP FV = true) {x y : Nat} (hx : x < 512)
    (hy : y < 512) : fE FP FV (P.e x y) = xor (fE FP FV x) (fE FP FV y) := by
  simp only [funG, band_iff, allN_iff, blt_iff, beqB_iff, bxor_eq] at hfun
  obtain ⟨hPm, hV, hA, -⟩ := hfun
  have hp : x &&& 63 < 64 := by rw [and63]; omega
  have hq : y &&& 63 < 64 := by rw [and63]; omega
  have hv : x >>> 6 < 8 := by rw [shr6]; omega
  have hw : y >>> 6 < 8 := by rw [shr6]; omega
  obtain ⟨hal, hab⟩ := hA _ hv _ hq
  obtain ⟨hml, hmb⟩ := hPm _ hp _ hal
  have elo : (pm (x &&& 63) (ac (x >>> 6) (y &&& 63)) + 64 * (x >>> 6 ^^^ y >>> 6)) &&& 63 =
      pm (x &&& 63) (ac (x >>> 6) (y &&& 63)) := by
    rw [and63]
    omega
  have ehi : (pm (x &&& 63) (ac (x >>> 6) (y &&& 63)) + 64 * (x >>> 6 ^^^ y >>> 6)) >>> 6 =
      x >>> 6 ^^^ y >>> 6 := by
    rw [shr6]
    omega
  rw [hP.he x y hx hy, hP.split x y hx hy]
  unfold fE
  rw [bxor_eq, bxor_eq, bxor_eq, elo, ehi, hmb, hab, hV _ hv _ hw]
  cases bitN FP (x &&& 63) <;> cases bitN FP (y &&& 63) <;> cases bitN FV (x >>> 6) <;>
    cases bitN FV (y >>> 6) <;> rfl

end Sound

section Tree

variable {e : Nat → Nat → Nat} {TR n : Nat} {A : Nat → Bool} {G cd : Nat → Nat}

theorem tree_sound (hst : ∀ x < 512, A x = true → tstepG e TR n A G cd x = true)
    (hcd : ∀ x, cd x < 32) (hn : n ≤ 5) (h00 : e 0 0 = 0) (f : Nat → Bool)
    (hf : ∀ x y, x < 512 → y < 512 → A x = true → A y = true → f (e x y) = xor (f x) (f y))
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
  unfold tstepG at h
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

variable {P : Par} {e : Nat → Nat → Nat} {XT : Nat}

theorem cmG_iff (e : Nat → Nat → Nat) (x y : Nat) : cmG e x y = true ↔ e x y = e y x :=
  beq_iff _ _

theorem xS_iff (hxt : xtG e XT = true) {x : Nat} (hx : x < 512) :
    xS XT x = true ↔ e x 64 = e 64 x := by
  have h := (allN_iff _ _).1 hxt x hx
  rw [band_iff, beqB_iff] at h
  rw [h.1, cmG_iff]

theorem xk_eq (hxt : xtG e XT = true) {x : Nat} (hx : x < 512) : xk XT x = kordG e x := by
  have h := (allN_iff _ _).1 hxt x hx
  rw [band_iff, beq_iff] at h
  exact h.2

theorem kordG_two (e : Nat → Nat → Nat) (x : Nat) : kordG e x = 2 ↔ x ≠ 0 ∧ e x x = 0 := by
  unfold kordG
  by_cases h1 : x = 0
  · subst h1
    rw [Nat.beq_refl]
    simp
  · rw [fp_beq_f h1]
    by_cases h2 : e x x = 0
    · rw [h2, Nat.beq_refl]
      simp [h1]
    · rw [fp_beq_f h2]
      cases Nat.beq (e (e x x) (e x x)) 0 <;>
        cases Nat.beq (e (e (e x x) (e x x)) (e (e x x) (e x x))) 0 <;> simp [h2]

theorem invG_iff (e : Nat → Nat → Nat) (x : Nat) : invG e x = true ↔ x ≠ 0 ∧ e x x = 0 := by
  unfold invG
  rw [band_iff, bnot_iff, beq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, h2⟩
    rw [h, Nat.beq_refl] at h1
    exact Bool.noConfusion h1
  · rintro ⟨h1, h2⟩
    exact ⟨fp_beq_f h1, h2⟩

variable (hE : ∀ x y, x < 512 → y < 512 → P.e x y = e x y) (htI : P.tI = 64)
  (hxt : xtG e XT = true)
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

theorem f0_code {GS TS : Nat} (h00 : e 0 0 = 0) (hts : treeSG e XT GS TS = true)
    (f : Nat → Bool) (hf : ∀ x y, fzrS P x → fzrS P y → f (P.e x y) = xor (f x) (f y)) :
    ∃ a, a < 16 ∧ ∀ x < 512, xS XT x = true → f x = parN (Nat.land a (xc XT x)) := by
  obtain ⟨a, ha, hb⟩ := fp_exists fun j => if j < 4 then f (fldN GS 9 511 j) else false
  unfold treeSG at hts
  rw [band_iff, allN_iff, allN_iff] at hts
  have h16 : a < 16 := by
    have h := (allN_iff _ _).1 CFSG.KC.FzUT.fp_lt16 a ha
    rw [bimp_iff, bnot_iff] at h
    exact fp_blt (h (by simpa using hb 4 (by omega)))
  refine ⟨a, h16, tree_sound (fun x hx hA => (bimp_iff _ _).1 (hts.2 x hx) hA) (xc_lt XT)
    (by omega) h00 f ?_ ?_ ha ?_⟩
  · intro x y hx hy hAx hAy
    rw [← hE _ _ hx hy]
    exact hf x y ((fzrS_iff hE htI hxt).2 ⟨hx, hAx⟩) ((fzrS_iff hE htI hxt).2 ⟨hy, hAy⟩)
  · exact fun j hj => ⟨hts.1 j hj, Nat.lt_succ_of_le (fldN_le _ _ _ _)⟩
  · intro j hj
    rw [hb j (by omega)]
    simp [hj]

theorem f1_code {GK RK TK a : Nat} (h00 : e 0 0 = 0) (htk : treeKG e XT GK RK TK a = true)
    (f : Nat → Bool)
    (hf : ∀ x y, x < 512 → y < 512 → inK XT a x = true → inK XT a y = true →
      f (P.e x y) = xor (f x) (f y)) :
    ∃ b, b < 32 ∧ b < Nat.shiftLeft 1 (rk RK a) ∧ ∀ x < 512, inK XT a x = true →
      f x = parN (Nat.land b (xd XT a x)) := by
  obtain ⟨b, hb, hbj⟩ := fp_exists fun j => f (kgen GK a j)
  unfold treeKG at htk
  rw [band_iff, allN_iff, allN_iff] at htk
  have hf' : ∀ x y, x < 512 → y < 512 → inK XT a x = true → inK XT a y = true →
      f (e x y) = xor (f x) (f y) := fun x y hx hy h1 h2 => by
    rw [← hE _ _ hx hy]
    exact hf x y hx hy h1 h2
  have hG : ∀ j < 5, inK XT a (kgen GK a j) = true ∧ kgen GK a j < 512 := fun j hj =>
    ⟨((band_iff _ _).1 (htk.1 j hj)).1, Nat.lt_succ_of_le (fldN_le _ _ _ _)⟩
  have hf0 : inK XT a 0 = true → f 0 = false := fun h0 => by
    have := hf' 0 0 (by omega) (by omega) h0 h0
    rw [h00] at this
    cases h' : f 0 <;> simp_all
  refine ⟨b, hb, lt_of_bits hb (Nat.lt_succ_of_le (fldN_le _ _ _ _)) fun j hj hrj => ?_,
    tree_sound (fun x hx hA => (bimp_iff _ _).1 (htk.2 x hx) hA) (xd_lt XT a) (le_refl 5)
      h00 f hf' hG hb fun j hj => hbj j hj⟩
  have hk : kgen GK a j = 0 :=
    (beq_iff _ _).1 ((bimp_iff _ _).1 ((band_iff _ _).1 (htk.1 j hj)).2 (fp_ble' hrj))
  have h0 := (hG j hj).1
  rw [hk] at h0
  rw [hbj j hj, hk, hf0 h0]

end Sub

section Leaf

variable {P : Par} {e : Nat → Nat → Nat} {tl wt tz : Nat → Bool} {rh : Nat → Nat}
  {pm ac : Nat → Nat → Nat} {θ : ℕ → Prop} {FR XT DW nD IW nI U m IN : Nat}
  (hP : FuParG P e tl wt tz rh pm ac) (hR : FzRules P θ) (hxt : xtG e XT = true)
  (hcls : ∀ x < 512, (θ x ↔ θ (fcls FR x))) (hdead : ∀ i < nD, ¬ θ (dwit DW i))
  (hU : ∀ j < 3, (θ (fldN U 9 511 j) ↔ bitN m j = true)) (hiw : iwG e tl IW nI = true)
  (hl : leafG e FR XT DW nD IW nI U m IN = true)
include hP hR hxt hcls hdead hU hiw hl

theorem leaf_sound : ∀ x < 512, (θ x ↔ thB XT FR IN x = true) := by
  intro x hx
  have hl' := (bimp_iff _ _).1 ((allN_iff _ _).1 hl x hx)
  unfold thB
  rw [band_iff, beq_iff, xk_eq hxt hx, kordG_two]
  by_cases hinv : x ≠ 0 ∧ e x x = 0
  · have hb := hl' (by rw [beq_iff, xk_eq hxt hx, kordG_two]; exact hinv)
    rw [hcls x hx]
    simp only [hinv, ne_eq, not_false_eq_true, and_self, true_and]
    cases hc : bitN IN (fcls FR x)
    · rw [hc] at hb
      change outCG FR DW nD U m x = true at hb
      unfold outCG at hb
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
      change inCG e FR IW nI U m x = true at hb
      unfold inCG at hb
      rw [bor_iff, bor_iff, beq_iff, anyN_iff, anyN_iff] at hb
      simp only [iff_true]
      rcases hb with he | ⟨i, hi, he⟩ | ⟨j, hj, he⟩
      · rw [he, ← hcls 64 (by omega), ← hP.tI]
        exact hR.th_t
      · rw [beq_iff] at he
        have hw := (allN_iff _ _).1 hiw i hi
        rw [band_iff, invG_iff] at hw
        have h5 : iwit IW i < 512 := fl9_lt IW i
        have hk := hR.ktl (iwit IW i) h5 (by rw [hP.inTL _ h5]; exact hw.1) hw.2.1
          (by rw [hP.he _ _ h5 h5]; exact hw.2.2)
        rw [hP.tI, hP.he _ _ (by omega) h5] at hk
        rw [he, ← hcls _ (e_lt hP hR (by omega) h5)]
        exact hk
      · rw [band_iff, beq_iff] at he
        rw [he.2, ← hcls (fldN U 9 511 j) (fl9_lt _ _), hU j hj]
        exact he.1
  · simp only [hinv, false_and, iff_false]
    intro hθ
    obtain ⟨-, h0, h2⟩ := hR.th_inv x hθ
    rw [hP.he x x hx hx] at h2
    exact hinv ⟨h0, h2⟩

theorem killC_sound {FP FV : Nat} (hc : coverLG e pm ac FR IN FP FV = true) : False := by
  have hth := leaf_sound hP hR hxt hcls hdead hU hiw hl
  unfold coverLG at hc
  rw [band_iff, allN_iff] at hc
  obtain ⟨hfun, hall⟩ := hc
  have ht : fE FP FV P.tI = true := by
    simp only [funG, band_iff] at hfun
    rw [hP.tI]
    exact hfun.2.2.2
  obtain ⟨x, hx, hθx, hfx⟩ := hR.cover _ (fun x y hx hy => fE_add hP hR hfun hx hy) ht
  obtain ⟨-, hx0, hxx⟩ := hR.th_inv x hθx
  have hinv : invG e x = true := by
    rw [invG_iff, ← hP.he x x hx hx]
    exact ⟨hx0, hxx⟩
  have h := (bimp_iff _ _).1 (hall x hx) (by rw [band_iff, bnot_iff]; exact ⟨hinv, hfx⟩)
  rw [bnot_iff] at h
  have h' := (hth x hx).1 hθx
  unfold thB at h'
  rw [band_iff, h] at h'
  exact Bool.false_ne_true h'.2

theorem killP_sound {GS TS GK RK TK u : Nat} (hts : treeSG e XT GS TS = true)
    (htk : treesKG e XT GK RK TK = true) (hp : profG e XT FR IN RK u = true) :
    False := by
  have hth := leaf_sound hP hR hxt hcls hdead hU hiw hl
  have hE := hP.he
  have htI := hP.tI
  have h00 : e 0 0 = 0 := by
    rw [← hE 0 0 (by omega) (by omega)]
    exact hR.mul.one_l 0 (by omega)
  unfold profG at hp
  rw [band_iff, band_iff, band_iff, blt_iff, ble_iff, sbB_eq, allN_iff] at hp
  obtain ⟨hu, hu5, hcnt, hall⟩ := hp
  have hθu : θ u := (hth u hu5).2 hu
  have hcent : fzrCent P u = (Finset.range 512).filter (fun x => cmG e x u = true) := by
    unfold fzrCent
    refine Finset.filter_congr fun x hx => ?_
    rw [Finset.mem_range] at hx
    rw [cmG_iff, hE x u hx hu5, hE u x hu5 hx]
  obtain ⟨f₀, f₁, hf0, hf1, h0t, h1t, -, hkey⟩ :=
    hR.prof u hθu (by rw [cent_card hP hR hu5]; exact hcnt)
  obtain ⟨a, ha16, ha⟩ := f0_code hE htI hxt h00 hts f₀ hf0
  have h64 : (64 : Nat) < 512 := by omega
  have hS64 : xS XT 64 = true := (xS_iff hxt h64).2 rfl
  have hpa : parN (Nat.land a (xc XT 64)) = false := by
    rw [← ha 64 h64 hS64, ← htI]
    exact h0t
  have hall0 := hall a ha16
  rw [bor_iff, hpa] at hall0
  have hall' := (allN_iff _ _).1 (hall0.resolve_left Bool.false_ne_true)
  have htk' : treeKG e XT GK RK TK a = true := by
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
  obtain ⟨b, hb32, hb, hbf⟩ := f1_code hE htI hxt h00 htk' f₁ fun x y hx hy h1 h2 =>
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
      histN (fun x => cmG e x u) (keyN XT FR IN) := by
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

theorem fp_lt8 : allN 32 (fun a => bimp (band (bnot (bitN a 3)) (bnot (bitN a 4)))
    (Nat.blt a 8)) = true := by
  decide +kernel

theorem leaves8_of {f : Nat → Bool} (h0 : allN 4 (fun i => f (Nat.add 0 i)) = true)
    (h4 : allN 4 (fun i => f (Nat.add 4 i)) = true) : ∀ m < 8, f m = true := by
  intro m hm
  rw [allN_iff] at h0 h4
  by_cases a : m < 4
  · simpa using h0 m a
  · have := h4 (m - 4) (by omega)
    rwa [show Nat.add 4 (m - 4) = m by simp only [Nat.add_eq]; omega] at this

theorem refuteG {P : Par} {e : Nat → Nat → Nat} {tl wt tz : Nat → Bool} {rh : Nat → Nat}
    {pm ac : Nat → Nat → Nat} {FR XT DW nD IW nI U GS TS GK RK TK LD : Nat}
    (hP : FuParG P e tl wt tz rh pm ac) (hF : forestG e tl rh FR = true)
    (hD : deadG e tl wt tz DW nD = true) (hiw : iwG e tl IW nI = true) (hxt : xtG e XT = true)
    (hts : treeSG e XT GS TS = true) (htk : treesKG e XT GK RK TK = true)
    (hL : ∀ m < 8, leafKG e pm ac FR XT DW nD IW nI U RK LD m = true) :
    ¬ ∃ θ : ℕ → Prop, FzRules P θ := by
  classical
  rintro ⟨θ, hR⟩
  obtain ⟨m, hm32, hmb⟩ := fp_exists fun j => if j < 3 then decide (θ (fldN U 9 511 j)) else false
  have hm : m < 8 := by
    have h := (allN_iff _ _).1 fp_lt8 m hm32
    rw [bimp_iff, band_iff, bnot_iff, bnot_iff] at h
    exact fp_blt (h ⟨by simpa using hmb 3 (by omega), by simpa using hmb 4 (by omega)⟩)
  have hU : ∀ j < 3, (θ (fldN U 9 511 j) ↔ bitN m j = true) := fun j hj => by
    rw [hmb j (by omega)]
    simp [hj]
  have hcls := forest_sound hP hR hF
  have hdead := dead_sound hP hR hD
  have hk := hL m hm
  unfold leafKG at hk
  rw [band_iff] at hk
  obtain ⟨hl, hk⟩ := hk
  cases hb : bitN (lrec LD m) 512
  · rw [hb] at hk
    exact killP_sound hP hR hxt hcls hdead hU hiw hl hts htk hk
  · rw [hb] at hk
    exact killC_sound hP hR hxt hcls hdead hU hiw hl hk

end CFSG.KC.FzZ8
