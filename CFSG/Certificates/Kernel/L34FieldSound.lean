module

public import Certificates.Data.Kernel.L34Field
public import CFSG.Certificates.Kernel.L34W.Tab42Sound
public import CFSG.Certificates.Kernel.L34KSound
import CFSG.Certificates.Kernel.L34KeySound
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Field

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.KC.L34W CFSG.KC.L34Key CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

variable {G : Nat → Nat}

theorem cp {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pcomp 42 6 (mask 6) p q) :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem wK_eq (hG : GensG G) (w : List Nat) : Cn (wK G w) ∧ wordTab w = unpack 42 6 (wK G w) := by
  unfold wordTab wK
  rw [idTab42]
  exact pword_spec (gS G) genT w _ cn_pidn fun j _ => genT_gS hG j

theorem true_of_notB_false {a : Bool} (h : CFSG.KLie.CT.notB a = false) : a = true := by
  cases a
  · exact absurd h (by decide)
  · rfl

theorem found_of_notIn {N x : Nat} {T : Nat → Nat} (h : CFSG.KLie.CT.notB (notInK N T x) = true) :
    found (indexOf (pts 42 6 N T)) (pts 42 6 N T) (unpack 42 6 x) = true := by
  rw [notB_iff] at h
  unfold notInK at h
  rw [strictB_app] at h
  have h' : CFSG.KLie.CT.notB (allN N fun i => CFSG.KLie.CT.notB (Nat.beq (T i) x)) = true := by rw [h]; rfl
  obtain ⟨q, hq, e⟩ := exists_of_notB_allN' h'
  exact found_pts hq (Nat.eq_of_beq_eq_true (true_of_notB_false e))

theorem syl2WitOK_of {TT TG BT Y YI : Nat → Nat} {r : Nat} (hG : GensG G)
    (hr2 : r₂T = unpack 42 6 r) (hr : Cn r)
    (hET : (enumBFS 42 (wordTabs wT₀) 64).tabs = pts 42 6 64 TT) (hTT : ∀ q < 64, Cn (TT q))
    (hTG : (wordTabs wT₀).size = 4 ∧ ∀ i < 4, (wordTabs wT₀)[i]! = unpack 42 6 (TG i) ∧ Cn (TG i))
    (hEB : (enumBFS 42 (wordTabs wB₀) 192).tabs = pts 42 6 192 BT)
    (hY : ∀ k < 105, wordTab (wReps.getD k []) = unpack 42 6 (Y k) ∧ Cn (Y k))
    (hYI : ∀ k < 105, invTab 42 (unpack 42 6 (Y k)) = unpack 42 6 (YI k) ∧ Cn (YI k))
    (h : syl2K G TT TG BT Y YI r = true) : syl2WitOK = true := by
  unfold syl2WitOK
  dsimp only
  rw [hEB, CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  have hk' : k < 105 := hk
  obtain ⟨ey, cy⟩ := hY k hk'
  obtain ⟨eyi, cyi⟩ := hYI k hk'
  unfold syl2K at h
  rw [strictB_app] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h k hk'
  rw [strictB_app] at h'
  rw [ey]
  rcases orB_iff.1 h' with h1 | h1
  · rw [Bool.or_eq_true]
    left
    unfold r2NotNormalizes
    dsimp only
    rw [hET, anyBelow_iff, hTG.1]
    unfold nnK at h1
    rw [strictB_app] at h1
    obtain ⟨i, hi, hi'⟩ := exists_of_notB_allN' h1
    have hn := true_of_notB_false hi'
    refine ⟨i, hi, ?_⟩
    obtain ⟨eg, cg⟩ := hTG.2 i hi
    have cz := cp (cp cyi hr) cy
    unfold r2Conj conjTab
    rw [eg, eyi, hr2, comp_unpack' cyi hr, comp_unpack' (cp cyi hr) cy, comp_unpack' cz cg,
      comp_unpack' (cp cz cg) cz]
    exact notIn_sound rfl (cp (cp cz cg) cz) hTT hn
  · rw [Bool.or_eq_true]
    right
    unfold witK at h1
    obtain ⟨e, he, hpe⟩ := List.any_eq_true.1 h1
    obtain ⟨b1, b2⟩ := andB_iff.1 hpe
    rw [strictB_app, strictB_app] at b2
    obtain ⟨cc, ec⟩ := wK_eq hG e.2
    obtain ⟨cm, b3⟩ := andB_iff.1 b2
    obtain ⟨cci, b4⟩ := andB_iff.1 b3
    obtain ⟨ecc, b5⟩ := andB_iff.1 b4
    have eci := Nat.eq_of_beq_eq_true ecc
    have hk1 : (e.1 == k) = true := by
      rw [beq_iff_eq]
      exact Nat.eq_of_beq_eq_true b1
    rw [List.any_eq_true]
    refine ⟨e, he, ?_⟩
    unfold invOK
    rw [ec, hr2, comp_unpack' cc hr, comp_unpack' hr cc, beq_unpack (cp cc hr) (cp hr cc),
      ← commPt_eq cc hr, cm, invTab_eq_of_pcomp cc cci eci, size_unpack,
      comp_inv_of_pcomp cc cci eci, comp_unpack' cci cy, found_of_notIn b5, hk1]
    simp only [beq_self_eq_true, Bool.and_self]

theorem fieldFreeOK_of {r : Nat} (hG : GensG G) (hr2 : r₂T = unpack 42 6 r) (hr : Cn r)
    (h : fieldK G r = true) : fieldFreeOK = true := by
  unfold fieldFreeOK
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  unfold fieldK at h
  simp only [strictB_app] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h k hk
  obtain ⟨ct, et⟩ := tgK_eq hG k
  unfold tgT
  rw [et, hr2, comp_unpack' hr ct, comp_unpack' (cp hr ct) hr, comp_unpack' (cp (cp hr ct) hr) ct,
    idTab42, beq_unpack (cp (cp (cp hr ct) hr) ct) cn_pidn]
  rcases orB_iff.1 h' with h1 | h1
  · rw [notB_iff] at h1
    rw [h1]
    rfl
  · obtain ⟨m, hm, hm'⟩ := exists_of_notB_allN' h1
    have hA := true_of_notB_false hm'
    obtain ⟨hA1, hA2⟩ := andB_iff.1 hA
    obtain ⟨cui, eui⟩ := andB_iff.1 hA1
    obtain ⟨cu, eu⟩ := tgK_eq hG m
    have eui' := Nat.eq_of_beq_eq_true eui
    rw [Bool.or_eq_true]
    right
    rw [anyBelow_iff]
    refine ⟨m, hm, ?_⟩
    obtain ⟨c0, e0⟩ := tgK_eq hG 0
    obtain ⟨c4, e4⟩ := tgK_eq hG 4
    obtain ⟨c8, e8⟩ := tgK_eq hG 8
    obtain ⟨c12, e12⟩ := tgK_eq hG 12
    have cX := cp (cp (cp cu hr) cui) hr
    unfold invOK
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [eu, e0, e4, e8, e12, invTab_eq_of_pcomp cu cui eui', size_unpack,
      comp_inv_of_pcomp cu cui eui', comp_unpack' cu hr, comp_unpack' (cp cu hr) cui,
      comp_unpack' (cp (cp cu hr) cui) hr, comp_unpack' cX c0, comp_unpack' cX c4,
      comp_unpack' cX c8, comp_unpack' cX c12, beq_unpack ct (cp cX c0), beq_unpack ct (cp cX c4),
      beq_unpack ct (cp cX c8), beq_unpack ct (cp cX c12)]
    simp only [orB_eq] at hA2
    simp only [beq_self_eq_true, Bool.true_and, hA2]

end CFSG.KC.L34Field

end
