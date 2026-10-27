module

public import Certificates.Data.Kernel.LocalComp.ExcDerivSq
public import CFSG.Certificates.Kernel.LocalCompExcDerivSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcU6Inputs
public import CFSG.Certificates.Kernel.LocalCompExcTextSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Child3Reps

public section

namespace CFSG.KC.LocalComp.ExcDeriv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CodesImg
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.ComponentClassification.RankTwoClassical.ExcU6 CFSG.EvenSmallLie.UnitarySix

variable {forbid : List Nat}

theorem arrOf_img {g : Equiv.Perm (Fin 693)} {P : Nat}
    (hg : imageList g = (unpack 693 10 P).toList) : arrOf g = unpack 693 10 P := by
  unfold arrOf unpack
  exact congrArg (Array.ofFn (n := 693)) (funext fun i => val_of_img hg i)

theorem fixCount_img {g : Equiv.Perm (Fin 693)} {P : Nat}
    (hg : imageList g = (unpack 693 10 P).toList) : fixCount g = fixCntK 10 (mask 10) P 693 := by
  unfold fixCount
  rw [arrOf_img hg, fixCntK_eq, CFSG.Certificates.Native.fixedList, List.countP_eq_length_filter]
  refine congrArg List.length (List.filter_congr fun p hp => ?_)
  rw [CFSG.KC.Child3.unpack_get' (List.mem_range.1 hp)]
  cases e : Nat.beq (pg 10 (mask 10) P p) p
  · have hne : pg 10 (mask 10) P p ≠ p := fun h' => by
      rw [h', Nat.beq_refl] at e
      exact Bool.false_ne_true e.symm
    simp [hne]
  · simp [Nat.eq_of_beq_eq_true e]

theorem badK_sound_u6 (hsz : szOK 693 10 = true)
    (hid : imageList (1 : Equiv.Perm (Fin 693)) = (unpack 693 10 (pidn 693 10)).toList)
    {cur : List (Equiv.Perm (Fin 693))} {CUR : List Nat} (hc : Corr 693 10 cur CUR)
    (h : badK 693 10 (mask 10) (693 * 10) (pidn 693 10) [] forbid CUR = true) :
    badState forbid cur = true := by
  unfold badK at h
  unfold badState
  simp only [Bool.or_eq_true, List.any_eq_true]
  cases e1 : anyL (fun g => neCK 693 10 (mask 10) (693 * 10) (pcomp 693 10 (mask 10) g g)
      (pidn 693 10)) CUR
  · rw [e1] at h
    cases e2 : anyL (fun g => anyL (fun h => neCK 693 10 (mask 10) (693 * 10)
        (pcomp 693 10 (mask 10) g h) (pcomp 693 10 (mask 10) h g)) CUR) CUR
    · rw [e2] at h
      right
      obtain ⟨mm, hmm, hf⟩ := anyN_spec h
      rw [CFSG.KS.PF.strictB_eqP] at hf
      simp only [bAnd_iff] at hf
      obtain ⟨hne, hz⟩ := hf
      have hp := maskProd_img hsz hid (mp := maskProd) (fun _ => rfl) (fun _ _ _ => rfl) hc mm
      have hlen : Nat.shiftLeft 1 (lenK CUR) = 2 ^ cur.length := by
        rw [lenK_eq, ← List.Forall₂.length_eq hc]
        exact (Nat.shiftLeft_eq 1 _).trans (Nat.one_mul _)
      refine ⟨mm, List.mem_range.2 ?_, ?_⟩
      · rwa [hlen] at hmm
      · simp only [tab_eq, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨schreierPermEq_of_neCK hp hid hne, ?_⟩
        have hm := memK_spec hz
        rw [fixCount_img hp]
        exact List.elem_iff.2 hm
    · left
      right
      obtain ⟨G, hG, hf⟩ := anyL_spec e2
      obtain ⟨H, hH, hf'⟩ := anyL_spec hf
      obtain ⟨g, hg, eg⟩ := hc.mem hG
      obtain ⟨h', hh, eh⟩ := hc.mem hH
      refine ⟨g, hg, h', hh, ?_⟩
      rw [Bool.not_eq_true']
      exact schreierPermEq_of_neCK (mulK_rep hsz eg eh) (mulK_rep hsz eh eg) hf'
  · left
    left
    obtain ⟨G, hG, hf⟩ := anyL_spec e1
    obtain ⟨g, hg, eg⟩ := hc.mem hG
    refine ⟨g, hg, ?_⟩
    rw [Bool.not_eq_true']
    exact schreierPermEq_of_neCK (mulK_rep hsz eg eg) hid hf

theorem derivSqK_sound_u6 {A AI : Nat → Nat} {kA : Nat}
    (hsz : szOK 693 10 = true)
    (hid : imageList (1 : Equiv.Perm (Fin 693)) = (unpack 693 10 (pidn 693 10)).toList)
    (hlen : alphabet.length = kA)
    (hA : ∀ j < alphabet.length, imageList (alphabet.getD j 1) = (unpack 693 10 (A j)).toList)
    (hAp : ∀ j < alphabet.length, permOK 693 10 (mask 10) (693 * 10) (A j) (AI j) = true) :
    ∀ (steps : List (ℕ × List ℤ × ℕ)) {cur : List (Equiv.Perm (Fin 693))} {CUR : List Nat},
      Corr 693 10 cur CUR →
      derivSqK 693 10 (mask 10) (693 * 10) (pidn 693 10) A AI kA forbid steps CUR = true →
      derivCheck forbid cur steps = true := by
  intro steps
  induction steps with
  | nil =>
    intro cur CUR hc h
    rw [derivCheck]
    exact badK_sound_u6 hsz hid hc h
  | cons st rest ih =>
    intro cur CUR hc h
    obtain ⟨mm, wd, i⟩ := st
    rw [derivCheck, Bool.or_eq_true]
    change bIf(badK 693 10 (mask 10) (693 * 10) (pidn 693 10) [] forbid CUR, true,
      stepSqK 693 10 (mask 10) (693 * 10) (pidn 693 10) A AI kA CUR mm wd i
        (derivSqK 693 10 (mask 10) (693 * 10) (pidn 693 10) A AI kA forbid rest)) = true at h
    cases hb : badK 693 10 (mask 10) (693 * 10) (pidn 693 10) [] forbid CUR
    · rw [hb] at h
      right
      unfold stepSqK at h
      simp only [CFSG.KS.PF.strictB_eqP, bAnd_iff] at h
      obtain ⟨h1, h3, h4, h5, h6, h7⟩ := h
      have hp := maskProd_img hsz hid (mp := maskProd) (fun _ => rfl) (fun _ _ _ => rfl) hc mm
      have h3' : lettersK alphabet.length wd = true := by rw [hlen]; exact h3
      have hc' := evalCodes_img hsz hA hAp hid h3'
      have hc2 := mulK_rep hsz hc' hc'
      have hci := invK_rep hc2 h4
      have hcl : CUR.length = cur.length := (List.Forall₂.length_eq hc).symm
      have hi : i < cur.length := by
        have := Nat.blt_eq.mp h6
        rwa [lenK_eq, hcl] at this
      have hnew := mulK_rep hsz (mulK_rep hsz hc2 (hc.getD i hi)) hci
      simp only [tab_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
      refine ⟨⟨⟨schreierPermEq_of_neCK hp hid h1, ?_⟩, hi⟩, ih (hc.snoc hnew) h7⟩
      have e2 := mulK_rep hsz hp hc'
      rw [← Nat.eq_of_beq_eq_true h5] at e2
      exact schreierPermEq_of_img (mulK_rep hsz hc' hp) e2
    · left
      exact badK_sound_u6 hsz hid hc hb

theorem parseDerivs_derivsC_u6 {ds : List (List (Nat × List Int × Nat))} (h : ds ≠ []) :
    parseDerivs (String.ofList (derivsC ds)) = ds :=
  parseDerivs_derivsC_sp6 h

end CFSG.KC.LocalComp.ExcDeriv

end
