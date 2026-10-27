module

public import Certificates.Data.Kernel.Misc.HypRun
public import Certificates.Data.CFSGNative.Fischer.HyperovalSearch
public import CFSG.Certificates.Kernel.Misc.XiSound
public import CFSG.Certificates.Kernel.Misc.HypNative
import CFSG.Certificates.Kernel.Misc.KernelRfl
import CFSG.Certificates.Kernel.Misc.HypSoundLam
import CFSG.Certificates.Kernel.Misc.HypSoundLamOK
import CFSG.Certificates.Kernel.Misc.HypSoundWords
import CFSG.Certificates.Kernel.Misc.HypSoundRoot
import CFSG.Certificates.Kernel.Misc.HypSoundOrbit
import CFSG.Certificates.Kernel.Misc.HypSoundSearch
import CFSG.Certificates.Kernel.Misc.HypSoundQ0Tp
import CFSG.Certificates.Kernel.Misc.HypSoundQ0Words
public import CFSG.Certificates.Kernel.Misc.O73Sound
public import CFSG.Certificates.Kernel.Misc.T46Sound
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib

public section

set_option maxRecDepth 100000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.TW CFSG.KS.PK

theorem hyp_eq : hypCertificate () =
    hypG uPts [30, 33, 16, 12, 9, 39, 39] [41, 46, 21, 23, 36] #[76, 307, 51, 217, 67] := by
  kernelRfl

theorem hyp_sound_q0 {U : Array Nat} {xw yw : List Int} {sel : Array Nat}
    {selL UL GP : List Nat} {UP PP XP YP J0 J1 J2 QB PW RES : Nat}
    {PB TP HS ML LB LI WT GI : Nat → Nat} {PL NL : Nat → List Nat} {SP : List Nat}
    (hU : U = UL.toArray) (hsel : sel = selL.toArray) (hp : ptsK UL UP = true)
    (hpos : posK UL UP PP = true) (hg : ∀ k < 46, gensOK UL UP GP k 1 = true)
    (hxy : xyK GP xw yw = true)
    (hX : Nat.beq XP (powP 3 (wordG GP xw)) = true) (hY : Nat.beq YP (powP 2 (wordG GP yw)) = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true)
    (hmem : ∀ k < 12, memK HS ML (352 * k) 352 = true) (hdist : distinctK HS SP = true)
    (ho0 : orbK UP XP YP HS ML J0 0 1 = true) (ho1 : orbK UP XP YP HS ML J1 1 2 = true)
    (ho2 : orbK UP XP YP HS ML J2 2 3 = true)
    (hlam : ∀ k < 32, lamK UP PP TP LB selL (32 * k) 32 = true)
    (hli : ∀ k < 16, liK LB LI (64 * k) 64 = true)
    (hlamOK : lamOKK UP PP PB LB PL selL = true) (hw : wordsK TP WT GI QB PW = true)
    (hrL : ∀ k < 21, rootLK UP PP HS PL (33 * k) 33 = true) (hrC : rootCK TP HS ML = true)
    (hnl : ∀ k < 21, nlK GI PL NL (33 * k) 33 = true)
    (hs : ∀ j < 1024, searchK PB LB HS LI NL RES j 1 = true)
    (hq0 : CFSG.KC.Misc.O73.at' 10 QB 0 = 0) :
    hypG U xw yw sel = true := by
  subst hU hsel
  have H := Pts.of hp hpos
  have hTR : ∀ f < 693, TR 693 ((tvTabsG UL.toArray)[f]!) (fd 10 (TP f)) :=
    fun f hf => tvTabs_TR H htab hf
  have hmemK : ∀ k < 4224, listsP (HS k) (ML k) = true := memK_spec hmem
  have hHSlt : ∀ k < 4224, HS k < 2 ^ 693 := fun k hk => (listsP_spec (hmemK k hk)).1
  have hdistS : ∀ j < 4224, ∀ j' < 4224, HS j = HS j' → j = j' := distinct_spec hdist
  have hr1 : HS 0 = rootK UP 1 := (orbK_spec (c := 1) 0 (by norm_num) hmemK ho0).1
  have hr2 : HS 1408 = rootK UP 2 := (orbK_spec (c := 2) 1 (by norm_num) hmemK ho1).1
  have hr3 : HS 2816 = rootK UP 3 := (orbK_spec (c := 3) 2 (by norm_num) hmemK ho2).1
  obtain ⟨hlen, hselb, hlamOK'⟩ := lamOKG_of hp hpos hperp hpl hl hlamOK
  have hlamT := lamTabG_eq H hTR hlen hselb hlam
  obtain ⟨hwOK, hgi⟩ := words_sound hTR hw hq0
  obtain ⟨hR1, hR2, hR3⟩ := root_sound hp hpos hperp hpl htab hmemK hr1 hr2 hr3 hrL hrC
  obtain ⟨hHeq, hO1, hO2, hO3, hfam⟩ :=
    orbit_sound hp hpos hg hxy hX hY hmem hdist ho0 ho1 ho2
  have hS := search_sound (sel := selL.toArray) hp hpos hperp hpl hHeq hHSlt hdistS hlamT hli hgi
    hnl hs
  have hgi_eq : (mkCtxG UL.toArray (perpTabG UL.toArray) (gWordsG UL.toArray)
      (lamTabG UL.toArray selL.toArray)).gI = wordInvsG UL.toArray (gWordsG UL.toArray) := rfl
  have hH_eq : (hypEnumG UL.toArray xw yw 1).1 ++ (hypEnumG UL.toArray xw yw 2).1 ++
      (hypEnumG UL.toArray xw yw 3).1 = hypUnionG UL.toArray xw yw := rfl
  unfold hypG hypChecksG
  simp only []
  simp only [Bool.and_eq_true]
  simp only [and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlamT]; exact hlamOK'
  · rw [hgi_eq]; exact hwOK
  · exact hR1
  · exact hR2
  · exact hR3
  · rw [hH_eq]; exact hO1
  · rw [hH_eq]; exact hO2
  · rw [hH_eq]; exact hO3
  · rw [hH_eq]; exact hfam
  · rw [hH_eq]; exact hS

theorem hyp_sound {U : Array Nat} {xw yw : List Int} {sel : Array Nat} {selL UL GP : List Nat}
    {UP PP XP YP J0 J1 J2 QB PW RES : Nat} {PB TP HS ML LB LI WT GI : Nat → Nat}
    {PL NL : Nat → List Nat} {SP : List Nat}
    (hU : U = UL.toArray) (hsel : sel = selL.toArray) (hp : ptsK UL UP = true)
    (hpos : posK UL UP PP = true) (hg : ∀ k < 46, gensOK UL UP GP k 1 = true)
    (hxy : xyK GP xw yw = true)
    (hX : Nat.beq XP (powP 3 (wordG GP xw)) = true) (hY : Nat.beq YP (powP 2 (wordG GP yw)) = true)
    (hperp : ∀ k < 21, perpK UP PB (33 * k) 33 = true) (hpl : plK PB PL = true)
    (hl : ∀ k < 21, linesK UP PP PB PL (33 * k) 33 = true)
    (htab : ∀ k < 21, tabK UP TP (33 * k) 33 = true)
    (hmem : ∀ k < 12, memK HS ML (352 * k) 352 = true) (hdist : distinctK HS SP = true)
    (ho0 : orbK UP XP YP HS ML J0 0 1 = true) (ho1 : orbK UP XP YP HS ML J1 1 2 = true)
    (ho2 : orbK UP XP YP HS ML J2 2 3 = true)
    (hlam : ∀ k < 32, lamK UP PP TP LB selL (32 * k) 32 = true)
    (hli : ∀ k < 16, liK LB LI (64 * k) 64 = true)
    (hlamOK : lamOKK UP PP PB LB PL selL = true) (hw : wordsK TP WT GI QB PW = true)
    (hrL : ∀ k < 21, rootLK UP PP HS PL (33 * k) 33 = true) (hrC : rootCK TP HS ML = true)
    (hnl : ∀ k < 21, nlK GI PL NL (33 * k) 33 = true)
    (hs : ∀ j < 1024, searchK PB LB HS LI NL RES j 1 = true) :
    hypG U xw yw sel = true := by
  obtain ⟨hc, hm, hl', hz⟩ := tp_centers_geom (Pts.of hp hpos) htab
  exact hyp_sound_q0 hU hsel hp hpos hg hxy hX hY hperp hpl hl htab hmem hdist ho0 ho1 ho2 hlam hli
    hlamOK hw hrL hrC hnl hs (qb0_of_words hc hm hl' hz hw)

end CFSG.KC.Misc.Hyp

end
