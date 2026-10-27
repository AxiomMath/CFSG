module

public import Certificates.Data.Kernel.FzUT.Fusion
public import CFSG.Certificates.Kernel.FzUT.Shape
public import CFSG.Certificates.Kernel.FzUT.FusionT

public section

namespace CFSG.KC.FzUT

open Certificates.FzL26 Certificates.FzR10
open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII

theorem bor_iff (a b : Bool) : bor a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem bxor_eq (a b : Bool) : bxor a b = xor a b := by
  cases a <;> cases b <;> rfl

theorem beqB_iff (a b : Bool) : beqB a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem blt_iff (a b : Nat) : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem ble_iff (a b : Nat) : Nat.ble a b = true ↔ a ≤ b := by
  rw [Nat.ble_eq]

theorem beq_false_iff (a b : Nat) : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_iff]

theorem fl9_lt (P i : Nat) : fldN P 9 511 i < 512 := fldN_lt P 9 i

theorem and63 (x : Nat) : x &&& 63 = x % 64 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 6
  norm_num at this
  exact this

theorem and15 (x : Nat) : x &&& 15 = x % 16 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 4
  norm_num at this
  exact this

theorem and3 (x : Nat) : x &&& 3 = x % 4 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 2
  norm_num at this
  exact this

theorem shr6 (x : Nat) : x >>> 6 = x / 64 := by
  rw [Nat.shiftRight_eq_div_pow]

structure FuPar (P : Par) (T S L : Nat) : Prop where
  e : ∀ x y, x < 512 → y < 512 → P.e x y = emP T S L x y
  tI : P.tI = 64
  sI : P.sI = 128
  inTL : ∀ x < 512, P.inTL x = inTLN T x
  inW : ∀ x < 512, P.inW x = inWN T x
  inTZ : ∀ x < 512, P.inTZ x = inTZN x
  rho : ∀ x < 256, P.rhoMap x = rhoN x

section Sound

variable {P : Par} {T S L : Nat} {θ : ℕ → Prop} (hP : FuPar P T S L) (hθ : FzRules P θ)
include hP hθ

theorem emP_lt {x y : Nat} (hx : x < 512) (hy : y < 512) : emP T S L x y < 512 := by
  rw [← hP.e x y hx hy]
  exact hθ.mul.lt x y hx hy

theorem kout_sound {sp a : Nat} (hsp : sp = P.sI ∨ sp = P.e P.tI P.sI) (hsp5 : sp < 512)
    (ha : a < 512) (htl : inTLN T a = true) (h2 : emP T S L (emP T S L a sp) (emP T S L a sp) = 0) :
    θ (emP T S L a sp) ↔ θ sp := by
  have hl := emP_lt hP hθ ha hsp5
  have := hθ.kout sp hsp a ha (by rw [hP.inTL a ha]; exact htl)
    (by rw [hP.e a sp ha hsp5, hP.e _ _ hl hl]; exact h2)
  rw [hP.e a sp ha hsp5] at this
  exact this

theorem edge_sound {k a x y : Nat} (ha : a < 512) (hx : x < 512) (hy : y < 512)
    (h : fuEdge T S L k a x y = true) : θ x ↔ θ y := by
  have h1 : (128 : Nat) = P.sI ∨ (128 : Nat) = P.e P.tI P.sI := Or.inl hP.sI.symm
  have h2 : emP T S L 64 128 = P.sI ∨ emP T S L 64 128 = P.e P.tI P.sI := by
    right
    rw [hP.tI, hP.sI, hP.e 64 128 (by norm_num) (by norm_num)]
  have h25 : emP T S L 64 128 < 512 := emP_lt hP hθ (by norm_num) (by norm_num)
  simp only [fuEdge, koutE, bor_iff, band_iff, beq_iff, blt_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, hx2, rfl⟩ | ⟨-, hy2, rfl⟩ | ⟨-, htl, rfl, h', rfl⟩ |
    ⟨-, htl, rfl, h', rfl⟩ | ⟨-, htl, rfl, h', rfl⟩ | ⟨-, htl, rfl, h', rfl⟩
  · exact hθ.conj a x y ha hx hy (by rw [hP.e y a hy ha, hP.e a x ha hx]; exact h)
  · exact (hθ.conj a y x ha hy hx (by rw [hP.e x a hx ha, hP.e a y ha hy]; exact h)).symm
  · rw [← hP.rho x hx2]
    exact hθ.rho x hx2
  · rw [← hP.rho y hy2]
    exact (hθ.rho y hy2).symm
  · exact kout_sound hP hθ h1 (by norm_num) ha htl h'
  · exact (kout_sound hP hθ h1 (by norm_num) ha htl h').symm
  · exact kout_sound hP hθ h2 h25 ha htl h'
  · exact (kout_sound hP hθ h2 h25 ha htl h').symm

theorem forest_sound {FR : Nat} (hF : forestOK T S L FR = true) :
    ∀ x < 512, θ x ↔ θ (fcls FR x) := by
  unfold forestOK at hF
  rw [allN_iff] at hF
  suffices key : ∀ d x, x < 512 → fdep FR x = d → (θ x ↔ θ (fcls FR x)) from
    fun x hx => key _ x hx rfl
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih x hx hd
  have hr := hF x hx
  simp only [recOK, bor_iff, band_iff, beq_iff] at hr
  rcases hr with ⟨-, hc, -⟩ | ⟨hdp, hcp, he⟩
  · rw [hc]
  · have hp5 : fpar FR x < 512 := fl9_lt _ _
    rw [edge_sound hP hθ (fl9_lt _ _) hx hp5 he,
      ih (fdep FR (fpar FR x)) (by omega) _ hp5 rfl, hcp]

end Sound

theorem cntN_eq (n : Nat) (f : Nat → Bool) :
    cntN n f = ((Finset.range n).filter fun i => f i = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : cntN (n + 1) f =
        Bool.rec (motive := fun _ => Nat) (cntN n f) (cntN n f + 1) (f n) := rfl
    rw [e, Finset.range_add_one, Finset.filter_insert]
    cases h : f n
    · rw [if_neg (by simp)]
      exact ih
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      exact congrArg (· + 1) ih

section Count

variable {P : Par} {T S L : Nat} {θ : ℕ → Prop} (hP : FuPar P T S L) (hθ : FzRules P θ)
include hP hθ

theorem kord_eq {x : Nat} (hx : x < 512) : kord P.e x = kordN T S L x := by
  have l1 := emP_lt hP hθ hx hx
  have l2 := emP_lt hP hθ l1 l1
  have e1 := hP.e x x hx hx
  have e2 := hP.e _ _ l1 l1
  have e3 := hP.e _ _ l2 l2
  unfold kord kordN sqN
  rw [e1, e2, e3]
  by_cases a : x = 0
  · rw [if_pos a, (beq_iff x 0).mpr a]
  rw [if_neg a, (beq_false_iff x 0).mpr a]
  by_cases b : emP T S L x x = 0
  · rw [if_pos b, (beq_iff _ 0).mpr b]
  rw [if_neg b, (beq_false_iff _ 0).mpr b]
  by_cases c : emP T S L (emP T S L x x) (emP T S L x x) = 0
  · rw [if_pos c, (beq_iff _ 0).mpr c]
  rw [if_neg c, (beq_false_iff _ 0).mpr c]
  by_cases d : emP T S L (emP T S L (emP T S L x x) (emP T S L x x))
      (emP T S L (emP T S L x x) (emP T S L x x)) = 0
  · rw [if_pos d, (beq_iff _ 0).mpr d]
  rw [if_neg d, (beq_false_iff _ 0).mpr d]

theorem cent_card {w : Nat} (hw : w < 512) :
    (fzrCent P w).card = cntN 512 fun x => cmN T S L x w := by
  rw [cntN_eq]
  unfold fzrCent cmN
  refine congrArg Finset.card (Finset.filter_congr fun x hx => ?_)
  rw [Finset.mem_range] at hx
  rw [beq_iff, hP.e x w hx hw, hP.e w x hw hx]

theorem cntC_eq {w o : Nat} (hw : w < 512) :
    cntC T S L w o = ((fzrCent P w).filter fun x => kord P.e x = o).card := by
  unfold cntC
  rw [cntN_eq]
  unfold fzrCent cmN
  rw [Finset.filter_filter]
  refine congrArg Finset.card (Finset.filter_congr fun x hx => ?_)
  rw [Finset.mem_range] at hx
  rw [band_iff, beq_iff, beq_iff, kord_eq hP hθ hx, hP.e x w hx hw, hP.e w x hw hx]

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

theorem kill_sound {w k o : Nat} (hw : w < 512) (h : killOK T S L w k o = true) : ¬ θ w := by
  simp only [killOK, invB, bor_iff, band_iff, beq_iff, bnot_iff, beq_false_iff, ble_iff,
    blt_iff] at h
  rcases h with ⟨-, htl, h0, h2⟩ | ⟨-, hw', hz⟩ | ⟨-, hc, hlt⟩
  · exact hθ.forb w hw (by rw [hP.inTL w hw]; exact htl) h0 (by rw [hP.e w w hw hw]; exact h2)
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

theorem dead_sound {DW n : Nat} (hD : deadOK T S L DW n = true) :
    ∀ i < n, ¬ θ (dwit DW i) := by
  unfold deadOK at hD
  rw [allN_iff] at hD
  exact fun i hi => kill_sound hP hθ (fl9_lt _ _) (hD i hi)

theorem fE_add {FP FV : Nat} (hfun : funOK T S L FP FV = true) {x y : Nat} (hx : x < 512)
    (hy : y < 512) : fE FP FV (P.e x y) = xor (fE FP FV x) (fE FP FV y) := by
  simp only [funOK, band_iff, allN_iff, blt_iff, beqB_iff, bxor_eq] at hfun
  obtain ⟨hPm, hV, hA, -⟩ := hfun
  have hp : x &&& 63 < 64 := by rw [and63]; omega
  have hq : y &&& 63 < 64 := by rw [and63]; omega
  have hv : x >>> 6 < 8 := by rw [shr6]; omega
  have hw : y >>> 6 < 8 := by rw [shr6]; omega
  have hvw : x >>> 6 ^^^ y >>> 6 < 8 := Nat.xor_lt_two_pow (n := 3) hv hw
  obtain ⟨hal, hab⟩ := hA _ hv _ hq
  obtain ⟨hml, hmb⟩ := hPm _ hp _ hal
  have elo : (pmulP (x &&& 63) (actP T S L (x >>> 6) (y &&& 63)) +
      64 * (x >>> 6 ^^^ y >>> 6)) &&& 63 = pmulP (x &&& 63) (actP T S L (x >>> 6) (y &&& 63)) := by
    rw [and63]
    omega
  have ehi : (pmulP (x &&& 63) (actP T S L (x >>> 6) (y &&& 63)) +
      64 * (x >>> 6 ^^^ y >>> 6)) >>> 6 = x >>> 6 ^^^ y >>> 6 := by
    rw [shr6]
    omega
  rw [hP.e x y hx hy]
  unfold fE emP
  rw [bxor_eq, bxor_eq, bxor_eq, elo, ehi, hmb, hab, hV _ hv _ hw]
  cases bitN FP (x &&& 63) <;> cases bitN FP (y &&& 63) <;> cases bitN FV (x >>> 6) <;>
    cases bitN FV (y >>> 6) <;> rfl

theorem cover_sound {FR DW n FP FV : Nat} (hF : forestOK T S L FR = true)
    (hC : coverOK T S L FR DW n FP FV = true) (hdead : ∀ i < n, ¬ θ (dwit DW i)) : False := by
  unfold coverOK at hC
  rw [band_iff, allN_iff] at hC
  obtain ⟨hfun, hall⟩ := hC
  have ht : fE FP FV P.tI = true := by
    simp only [funOK, band_iff] at hfun
    rw [hP.tI]
    exact hfun.2.2.2
  obtain ⟨x, hx, hθx, hfx⟩ := hθ.cover _ (fun x y hx hy => fE_add hP hθ hfun hx hy) ht
  obtain ⟨-, hx0, hxx⟩ := hθ.th_inv x hθx
  have hinv : invB T S L x = true := by
    unfold invB
    rw [band_iff, bnot_iff, beq_false_iff, beq_iff, ← hP.e x x hx hx]
    exact ⟨hx0, hxx⟩
  have hx' := hall x hx
  rw [bimp_iff, band_iff, bnot_iff, anyN_iff] at hx'
  obtain ⟨i, hi, hci⟩ := hx' ⟨hinv, hfx⟩
  rw [beq_iff] at hci
  have hd5 : dwit DW i < 512 := fl9_lt _ _
  apply hdead i hi
  rw [forest_sound hP hθ hF _ hd5, hci, ← forest_sound hP hθ hF x hx]
  exact hθx

end Count

theorem fusion_refute {P : Par} {T S L FR DW n FP FV : Nat} (hP : FuPar P T S L)
    (hF : forestOK T S L FR = true) (hD : deadOK T S L DW n = true)
    (hC : coverOK T S L FR DW n FP FV = true) : ¬ ∃ θ : ℕ → Prop, FzRules P θ := by
  rintro ⟨θ, hθ⟩
  exact cover_sound hP hθ hF hC (dead_sound hP hθ hD)

theorem fix_iff (σ : MulAut FzUT) {n : Nat} (hn : n < 64) :
    (fzAutI σ).ap n = n ↔ evD (gc σ) n = n := by
  have h1 := ap_eq_iff σ hn
  have h3 : enc (fzElt n) = n := fzIdx_fzElt hn
  have h2 := evD_gc σ (fzElt n)
  rw [h3] at h2
  have e : (fzAutI σ).ap n = n ↔ σ (fzElt n) = fzElt n := by
    rw [← beq_iff_eq (a := (fzAutI σ).ap n) (b := n), h1, decide_eq_true_iff]
  rw [e, h2]
  constructor
  · intro h
    rw [h, h3]
  · intro h
    apply enc_injective
    rw [h, h3]

theorem rho0_eq {n : Nat} (hn : n < 64) : rho0 n = r0P n := by
  have h3 : enc (fzElt n) = n := fzIdx_fzElt hn
  have h1 := r0P_eq (fzElt n)
  have h2 := fzIdx_rho0 (fzElt n)
  rw [h3] at h1
  have h4 : fzIdx (fzElt n) = n := fzIdx_fzElt hn
  rw [h4] at h2
  exact h2.trans h1.symm

theorem fuPar_parT (t s l : MulAut FzUT) : FuPar (parT t s l) (gc t) (gc s) (gc l) where
  e x y hx hy := by
    rw [← fzEIdx_fzEOf hx, ← fzEIdx_fzEOf hy, parT_e]
    exact (emP_eq (fzEOf x) (fzEOf y)).symm
  tI := parOf_tI _ _ _
  sI := parOf_sI _ _ _
  inTL x hx := by
    rw [parOf_inTL]
    unfold inTLN
    rw [and63, and3, shr6]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, band_iff, beq_iff]
    rw [fix_iff t (Nat.mod_lt _ (by norm_num))]
  inW x hx := by
    rw [parOf_inW]
    unfold inWN
    rw [and63, shr6]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, band_iff, beq_iff, blt_iff, decide_eq_true_eq]
    rw [fix_iff t (Nat.mod_lt _ (by norm_num))]
  inTZ x hx := by
    rw [parOf_inTZ]
    unfold inTZN
    rw [and15, shr6]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, beq_iff_eq, band_iff, beq_iff]
    constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by omega⟩
  rho x hx := by
    rw [parOf_rho]
    unfold rhoN
    rw [and63, shr6, rho0_eq (Nat.mod_lt _ (by norm_num))]

end CFSG.KC.FzUT
