module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusSound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusData
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThree
public import Certificates.Certificate17305

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.HardMathSupport.Dickson.Sec6

@[expose] noncomputable def thS : ↥J :=
  slpJ a b CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative.prog3 11

@[expose] noncomputable def thZ :
    ↥J := ThCent.zJ

@[expose] noncomputable def thU : ↥J :=
  slpJ a b TabThNative.progU 22

section Census


theorem prog3_lt' : prog3.all (Op.lt n3) = true := by decide

theorem rowsMatrix_regs3' :
    (regs3 ()).size = n3 ∧ ∀ r < n3, rowsMatrix (regs3 ())[r]! = matJ (slpJ a b prog3 r) :=
  rowsMatrix_slpRows rowsMatrix_seedA rowsMatrix_seedB prog3_lt'

theorem progU_lt : TabThNative.progU.all (Op.lt TabThNative.nU) = true := by decide

theorem rowsMatrix_regsU :
    (TabThNative.regsU ()).size = TabThNative.nU ∧ ∀ r < TabThNative.nU,
      rowsMatrix (TabThNative.regsU ())[r]! = matJ (slpJ a b TabThNative.progU r) :=
  rowsMatrix_slpRows rowsMatrix_seedA rowsMatrix_seedB progU_lt

theorem ord_of_ordOK' {X : Array V4} {g : ↥J} (hX : rowsMatrix X = matJ g) {p : ℕ}
    [Fact p.Prime] (h : ordOK X p = true) : orderOf g = p := by
  unfold ordOK at h
  simp only [Bool.and_eq_true] at h
  have hid : rowsMatrix idRows = matJ (1 : ↥J) := by rw [rowsMatrix_idRows, matJ_one]
  refine orderOf_eq_prime (eq_of_rowsMatrix_eq (g := g ^ p) (h := 1) ?_ hid h.1)
    (ne_of_rowsDiffer hX hid h.2)
  rw [rowsMatrix_powRowsN, hX, matJ_pow]

theorem th_orderOf :
    orderOf thS = 3 ∧ orderOf thZ = 3 ∧ orderOf thU = 3 :=
  ⟨Certificates.certificate17305.1, Certificates.certificate17305.2.1,
    Certificates.certificate17305.2.2.1⟩

theorem th_census (x : ↥J) (hx : orderOf x = 3) :
    ∃ k : ↥J, ∃ c : ↥J, (c = thS ∨ c = thZ ∨ c = thU) ∧ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      k * c ^ e * k⁻¹ = x :=
  Certificates.certificate17305.2.2.2 x hx

end Census

end CFSG.HardMathSupport.Dickson.I271
