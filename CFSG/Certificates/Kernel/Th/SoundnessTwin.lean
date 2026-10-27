
module

public import CFSG.Certificates.Kernel.Th.SoundnessTwinBase

public import CFSG.Certificates.Kernel.Th.SoundnessGen
public import CFSG.Certificates.Kernel.Th.S.BaseS
import CFSG.Certificates.Kernel.Th.Spec.Base
import CFSG.Certificates.Kernel.Th.Spec.Base2
public import CFSG.Certificates.Kernel.Th.S.SurjS
public import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.Bridge.ThData
public import CFSG.Sporadic.Bridge.ThSurjInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.SurjRel
public import CFSG.Certificates.Kernel.Th.Spec.SurjCheck
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.Th.Spec.GjBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.ThBase
public import CFSG.Sporadic.Th
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.KernelCentralizerBase
public import CFSG.Sporadic.Th.KernelContractBase
public import CFSG.Sporadic.Th.KernelOrderBase
public import CFSG.Sporadic.Th.KernelPlanesBase
public import CFSG.Sporadic.Th.KernelSimpleBase
public import CFSG.Sporadic.ThSchreier.FullAutCoreBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase
import CFSG.Certificates.Kernel.Th.Spec.Base2Base

public section

namespace CFSG.KC.Th.Soundness

open CFSG.Sporadic.Th CFSG.KC.Th

theorem isHsw_pres : IsHsw CFSG.Sporadic.Bridge.Th.pres := by
  have hp : TauCeti.SporadicName.Th.presentation = CFSG.Sporadic.Bridge.Th.pres := rfl
  exact hp ▸ isHsw_th

theorem base_sound (c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE F C G N : ℕ)
    (_hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (_hF : SeedS.packOK F SeedS.fcRowsList = true) (_hC : SeedS.packOK C BaseS.deltaRows = true)
    (_hG : Nat.beq (mulB c rm (mulB c rm C F) (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 C)) G = true)
    (_hN : Nat.beq (mulB c rm N C) ONE = true) (_hB : formBaseCheck 124 (blkG rm G) = true) :
    formBaseCheck 124 Native.baseCode = true ∧
      Native.eqRows (Native.mulRows (Native.invRows Native.cRows) Native.cRows) Native.idRows = true := by
  exact ⟨CFSG.KC.Th.Spec.formBaseCheck_baseCode _hk _hF _hC _hG _hB,
    CFSG.KC.Th.Spec.eqRows_invRows_cRows _hk _hC _hN⟩

theorem surj_sound (p : TauCeti.GroupPresentation) (_hp : IsHsw p)
    (c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE SA SB : ℕ) (RB : ℕ → ℕ)
    (LI LS LA LB : List Char) (S0 S1 : List ℕ)
    (_hI : CFSG.Sporadic.Bridge.Th.imgText = String.ofList LI)
    (_hS : CFSG.Sporadic.Bridge.Th.stdText = String.ofList LS)
    (_hA : Native.seedA = String.ofList LA) (_hB : Native.seedB = String.ofList LB)
    (_hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (_hdA : SeedS.decOK SA LA = true) (_hdB : SeedS.decOK SB LB = true)
    (_hT : SurjS.textOK RB rm LI = true) (_hR : SurjS.regsOK RB c rm ONE = true)
    (_hrel : BigS.relsOK RB c rm ONE SurjS.GR SurjS.IR = true)
    (_hW : SurjS.wordsOK LS [S0, S1] = true)
    (_h0 : Nat.beq (SurjS.wordV RB c rm S0 ONE) SA = true)
    (_h1 : Nat.beq (SurjS.wordV RB c rm S1 ONE) SB = true) :
    CFSG.Sporadic.Bridge.Th.thCheck p.relatorLetters = true := by
  have hrm : rm = 2 ^ 248 - 1 := (CFSG.KC.Th.Spec.consts_spec _hk).2.1
  obtain ⟨hsz, hmat⟩ := CFSG.KC.Th.Spec.imgMats_spec hrm _hI _hT
  have hinv : ∀ g < 8, CFSG.KC.Th.Spec.pkMat (RB (g + 1)) * CFSG.KC.Th.Spec.pkMat (RB (g + 9)) =
      1 := by
    intro g hg
    rw [← CFSG.KC.Th.Spec.pkMat_mulB _hk, CFSG.KC.Th.Spec.regsOK_mul _hR g hg]
    exact CFSG.KC.Th.Spec.pkMat_one _hk
  have hrels := CFSG.KC.Th.Spec.relators_spec _hk p _hp _hrel
  obtain ⟨hwords, hparse⟩ := CFSG.KC.Th.Spec.parseWords_spec _hW
  have hstd : CFSG.Sporadic.Bridge.Th.stdWords =
      [S0.map CFSG.KC.Th.Spec.lettOfCode, S1.map CFSG.KC.Th.Spec.lettOfCode] := by
    unfold CFSG.Sporadic.Bridge.Th.stdWords
    rw [_hS, hparse]
    rfl
  have hx0 : ∀ x ∈ S0, x / 2 < 8 := (hwords S0 (by simp)).2
  have hx1 : ∀ x ∈ S1, x / 2 < 8 := (hwords S1 (by simp)).2
  have hw0 : ∀ l ∈ S0.map CFSG.KC.Th.Spec.lettOfCode, l.1 < 8 := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    exact hx0 x hx
  have hw1 : ∀ l ∈ S1.map CFSG.KC.Th.Spec.lettOfCode, l.1 < 8 := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    exact hx1 x hx
  have hone := CFSG.KC.Th.Spec.pkMat_one _hk
  have hs0 : CFSG.KC.Th.Spec.wordMat RB (S0.map CFSG.KC.Th.Spec.lettOfCode) =
      rowsMatrix (Native.rowsOf Native.seedA) := by
    have h := CFSG.KC.Th.Spec.wordV_spec (RB := RB) _hk S0 ONE hx0
    rw [hone, Nat.eq_of_beq_eq_true _h0] at h
    obtain ⟨-, hA⟩ := CFSG.KC.Th.Spec.decOK_sound _hdA
    rw [← _hA] at hA
    exact h.symm.trans hA
  have hs1 : CFSG.KC.Th.Spec.wordMat RB (S1.map CFSG.KC.Th.Spec.lettOfCode) =
      rowsMatrix (Native.rowsOf Native.seedB) := by
    have h := CFSG.KC.Th.Spec.wordV_spec (RB := RB) _hk S1 ONE hx1
    rw [hone, Nat.eq_of_beq_eq_true _h1] at h
    obtain ⟨-, hB⟩ := CFSG.KC.Th.Spec.decOK_sound _hdB
    rw [← _hB] at hB
    exact h.symm.trans hB
  exact CFSG.KC.Th.Spec.thCheck_of_spec hsz hmat hinv hrels hstd hw0 hw1 hs0 hs1

end CFSG.KC.Th.Soundness

end
