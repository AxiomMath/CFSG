module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMCover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzFuse
public import Certificates.Certificate17621

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeASuzInv
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)

section Datum

theorem rkBMInvAt_inv_aux {F : Type} [Group F] {g : F} (h : RkBMInvAt g) : RkBMInvAt g⁻¹ := by
  obtain ⟨⟨s, hs2, hsg⟩, t, t', ht2, ht'2, htg, ht'g, h3, h1⟩ := h
  refine ⟨⟨s, hs2, ?_⟩, t, t', ht2, ht'2, ?_, ?_, h3, h1⟩
  · have hss : s * s = 1 := by rw [← sq]; exact hs2
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have : (s * g * s)⁻¹ = s * g⁻¹ * s := by
      rw [mul_inv_rev, mul_inv_rev, hsi, mul_assoc]
    rw [← this, hsg, inv_inv]
  · exact (Commute.inv_right (show Commute t g from htg)).eq
  · exact (Commute.inv_right (show Commute t' g from ht'g)).eq

theorem rkBMInvAt_pow_aux {F : Type} [Group F] {c : F} (hc : c ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : RkBMInvAt c) : RkBMInvAt (c ^ e) := by
  rcases he with rfl | rfl
  · rwa [pow_one]
  · have : c ^ 2 = c⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ]
      exact hc
    rw [this]
    exact rkBMInvAt_inv_aux h


theorem rkBMInvAt_of_invAtOK {c : Array ℕ} {tp : Array (Array ℕ)} {C : Equiv.Perm (Fin 1782)}
    (hc : Rep 1782 c C) (hC : C ∈ suzM) (h : invAtOK (levels ()) c tp = true) :
    RkBMInvAt (⟨C, hC⟩ : ↥suzM) := by
  simp only [invAtOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hsv, hsP, htv, htP, ht'v, ht'P, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have rs := rep_of_validA hsv
  have rt := rep_of_validA htv
  have rt' := rep_of_validA ht'v
  have sP := mem_suzM_of_inP rs hsP
  have tP := mem_suzM_of_inP rt htP
  have t'P := mem_suzM_of_inP rt' ht'P
  have e1 := (eqA_iff (rep_compA rs rs) rep_idA).1 h1
  have e2 := (eqA_iff (rep_compA (rep_compA rs hc) (rep_compA rs hc)) rep_idA).1 h2
  have e3 := (eqA_iff (rep_compA rt rt) rep_idA).1 h3
  have e4 := (eqA_iff (rep_compA rt' rt') rep_idA).1 h4
  have e5 := (eqA_iff (rep_compA rt hc) (rep_compA hc rt)).1 h5
  have e6 := (eqA_iff (rep_compA rt' hc) (rep_compA hc rt')).1 h6
  have e7 := (eqA_iff (rep_powArr (rep_compA rt rt') 3) rep_idA).1 h7
  have e8 : permOfArr 1782 (rebuild (levels ()) tp[1]!) *
      permOfArr 1782 (rebuild (levels ()) tp[2]!) ≠ 1 := fun h => by
    rw [(eqA_iff (rep_compA rt rt') rep_idA).2 h] at h8
    exact absurd h8 (by decide)
  generalize permOfArr 1782 (rebuild (levels ()) tp[0]!) = S at *
  generalize permOfArr 1782 (rebuild (levels ()) tp[1]!) = T at *
  generalize permOfArr 1782 (rebuild (levels ()) tp[2]!) = T' at *
  refine ⟨⟨⟨S, sP⟩, Subtype.ext ?_, Subtype.ext ?_⟩, ⟨T, tP⟩, ⟨T', t'P⟩, Subtype.ext ?_,
    Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, ?_⟩
  · simpa [sq] using e1
  · have : S * C * S * C = 1 := by rw [mul_assoc (S * C) S C]; exact e2
    simpa using eq_inv_of_mul_eq_one_left this
  · simpa [sq] using e3
  · simpa [sq] using e4
  · simpa using e5
  · simpa using e6
  · simpa [pow_three, mul_assoc] using e7
  · intro h
    exact e8 (by simpa using congrArg Subtype.val h)

end Datum

section Classes


theorem suzInv_parts :
    invAtOK (levels ()) (xAArr (levels ())) tupA = true ∧
    invAtOK (levels ()) (xBArr (levels ())) tupB = true ∧
    invAtOK (levels ()) (yArr (levels ())) tupY = true := by
  have h : suzInvCheck () = true := Certificates.certificate17621
  simpa only [suzInvCheck, Bool.and_eq_true, and_assoc] using h

theorem rkBMInv_suzM : RkBMInv ↥suzM := by
  intro g hg1 hg3
  have hs3 : orderOf (g : Equiv.Perm (Fin 1782)) = 3 := by
    have h1 : (g : Equiv.Perm (Fin 1782)) ^ 3 = 1 := by
      have := congrArg Subtype.val hg3
      simpa using this
    have h2 : (g : Equiv.Perm (Fin 1782)) ≠ 1 := fun h => hg1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨k, hk, c, hc, e, he, hcon⟩ := suz_exists_conj_classes g.2 hs3
  have hrep : ∃ c' : ↥suzM, (c' : Equiv.Perm (Fin 1782)) = c ∧ c' ^ 3 = 1 ∧ RkBMInvAt c' := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨⟨fuseXA, fuseXA_mem⟩, rfl, Subtype.ext (by simpa using fuseXA_pow),
        rkBMInvAt_of_invAtOK rep_fuseXA fuseXA_mem suzInv_parts.1⟩
    · exact ⟨⟨fuseXB, fuseXB_mem⟩, rfl, Subtype.ext (by simpa using fuseXB_pow),
        rkBMInvAt_of_invAtOK rep_fuseXB fuseXB_mem suzInv_parts.2.1⟩
    · exact ⟨⟨yPerm, yPerm_mem⟩, rfl, Subtype.ext (by simpa using yPerm_pow),
        rkBMInvAt_of_invAtOK rep_y yPerm_mem suzInv_parts.2.2⟩
  obtain ⟨c', hc'val, hc'3, hdat⟩ := hrep
  have hconj := (rkBMInvAt_pow_aux hc'3 he hdat).conj (⟨k, hk⟩ : ↥suzM)
  have hkg : (⟨k, hk⟩ : ↥suzM) * c' ^ e * (⟨k, hk⟩ : ↥suzM)⁻¹ = g := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp
  rwa [hkg] at hconj


theorem rkBMInv_Suz : RkBMInv CFSG.Blueprint.NativeSporadic.Suz :=
  RkBMInv.of_equiv suzEquivM.symm rkBMInv_suzM

end Classes

end CFSG.HardMathSupport.Dickson.I271
