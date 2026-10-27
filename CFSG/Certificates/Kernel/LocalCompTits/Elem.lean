module

public import Certificates.Data.Kernel.LocalComp.TitsElem
public import CFSG.Certificates.Kernel.LocalCompTits.Words
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native
  CFSG.KC.LocalComp.Tits

attribute [local irreducible] compT powT invT idT wT

local macro "pk" : tactic =>
  `(tactic| repeat' (first | assumption | exact Pk.id | apply Pk.comp | apply Pk.pow))

theorem elemProd_pk {x0 x1 x2 x3 x4 : Nat} {X0 X1 X2 X3 X4 : Table} (h0 : Pk X0 x0)
    (h1 : Pk X1 x1) (h2 : Pk X2 x2) (h3 : Pk X3 x3) (h4 : Pk X4 x4) (k : Nat) :
    Pk (elemProdT X0 X1 X2 X3 X4 k) (elemProdK 1755 11 x0 x1 x2 x3 x4 k) := by
  unfold elemProdT elemProdK
  rw [nPts_eq]
  pk

theorem elemOK_of_K {TG : Nat → Nat} {CP : List Nat} {w0 w1 w2 w3 w4 : List Nat}
    (hg : genTables = Array.ofFn (n := 4) fun s => tabP 1755 (TG s.val))
    (hc : checkPts = CP.toArray) (h : elemK 1755 11 TG CP w0 w1 w2 w3 w4 = true) :
    elemOK w0 w1 w2 w3 w4 = true := by
  unfold elemK invoK commK at h
  simp only [strictB_eqP, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hl, hTG, i0, i1, i2, i3, i4, c01, c02, c03, c04, c12, c13, c14, c23, c24, c34, hp⟩ := h
  have hTG' : ∀ s < 4, permOK 1755 11 (mask 11) (1755 * 11) (TG s)
      (pinvS 1755 11 (mask 11) (TG s)) = true := fun s hs => allN_spec hTG s hs
  have p0 := wT_eq hg hTG' (texpand w0)
  have p1 := wT_eq hg hTG' (texpand w1)
  have p2 := wT_eq hg hTG' (texpand w2)
  have p3 := wT_eq hg hTG' (texpand w3)
  have p4 := wT_eq hg hTG' (texpand w4)
  rw [← lettersOK_eq] at hl
  unfold lettersOK at hl
  simp only [List.append_nil, Bool.and_eq_true] at hl
  unfold elemOK CFSG.SectionRank.Native.Tits.commOK
  simp only [nPts_eq, Bool.and_eq_true, and_assoc]
  refine ⟨hl.1, hl.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (eqOn_eq hc (by pk) (by pk)).trans i0
  · exact (eqOn_eq hc (by pk) (by pk)).trans i1
  · exact (eqOn_eq hc (by pk) (by pk)).trans i2
  · exact (eqOn_eq hc (by pk) (by pk)).trans i3
  · exact (eqOn_eq hc (by pk) (by pk)).trans i4
  · exact (eqOn_eq hc (by pk) (by pk)).trans c01
  · exact (eqOn_eq hc (by pk) (by pk)).trans c02
  · exact (eqOn_eq hc (by pk) (by pk)).trans c03
  · exact (eqOn_eq hc (by pk) (by pk)).trans c04
  · exact (eqOn_eq hc (by pk) (by pk)).trans c12
  · exact (eqOn_eq hc (by pk) (by pk)).trans c13
  · exact (eqOn_eq hc (by pk) (by pk)).trans c14
  · exact (eqOn_eq hc (by pk) (by pk)).trans c23
  · exact (eqOn_eq hc (by pk) (by pk)).trans c24
  · exact (eqOn_eq hc (by pk) (by pk)).trans c34
  · rw [TW.allIn_iff]
    intro k hk
    have e := allN_spec hp k hk
    rw [eqOn_eq hc (elemProd_pk p0 p1 p2 p3 p4 (k + 1)) Pk.id]
    exact e

end CFSG.KC.LocalComp.TitsSound

end
