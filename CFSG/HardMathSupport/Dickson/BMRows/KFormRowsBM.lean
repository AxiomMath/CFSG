module

public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteAll
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteB
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteChev2
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteM
public import CFSG.HardMathSupport.Dickson.BMRows.KFormDefs
public import CFSG.HardMathSupport.Dickson.BMRows.KFormRows
public import CFSG.HardMathSupport.Dickson.BMRows.M13Rows

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA


theorem qrowK
    (hM11 : I1416QRows.I1416QRow .M 11) :
    ∀ (s : TauCeti.SporadicName) (p : ℕ),
      (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
      (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) → I1416QRows.I1416QRow s p := by
  intro s p hB hM
  by_cases hsB : s = .B
  · subst hsB
    exact qrows_B_all (qrow_B_three_of_kGroup (hB rfl)) (qrow_B_five_of_kGroup (hB rfl))
      qrow_B_seven p
  · by_cases hsM : s = .M
    · subst hsM
      exact qrows_M_all (qrow_M_three_of_kGroup (hM rfl)) (qrow_M_five_of_kGroup (hM rfl))
        qrow_M_seven hM11 qrow_M_thirteen p
    · exact qrow_of_ne_BM hsB hsM p

theorem rowK
    (hM11 : I1416Rows.I1416SporRow .M 11) :
    ∀ (s : TauCeti.SporadicName) (p : ℕ),
      (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
      (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) → I1416Rows.I1416SporRow s p := by
  intro s p hB hM
  by_cases hsB : s = .B
  · subst hsB
    exact rows_B_all (row_B_three_of_kGroup (hB rfl)) (row_B_five_of_kGroup (hB rfl))
      row_B_seven p
  · by_cases hsM : s = .M
    · subst hsM
      exact rows_M_all (row_M_three_of_kGroup (hM rfl)) (row_M_five_of_kGroup (hM rfl))
        row_M_seven hM11 row_M_thirteen p
    · exact row_of_ne_BM hsB hsM p

theorem crowK
    (hM11 : Chev2Rows.CRow .M 11) :
    ∀ (s : TauCeti.SporadicName) (p : ℕ),
      (s = .B → CFSG.Open.IsKGroup (NativeSporadic.Carrier .B)) →
      (s = .M → CFSG.Open.IsKGroup (NativeSporadic.Carrier .M)) → Chev2Rows.CRow s p := by
  intro s p hB hM
  by_cases hsB : s = .B
  · subst hsB
    exact crows_B_all (crow_B_three_of_kGroup (hB rfl)) (crow_B_five_of_kGroup (hB rfl))
      crow_B_seven p
  · by_cases hsM : s = .M
    · subst hsM
      exact crows_M_all (crow_M_three_of_kGroup (hM rfl)) (crow_M_five_of_kGroup (hM rfl))
        crow_M_seven hM11 crow_M_thirteen p
    · exact crow_of_ne_BM hsB hsM p

theorem i1416QSporSK_of_rows
    (hM11 : I1416QRows.I1416QRow .M 11) : I1416QSporSK :=
  i1416QSporSK_iff.2 (qrowK hM11)

theorem i1416TwoSporSK_of_rows
    (hM11 : I1416Rows.I1416SporRow .M 11) : I1416TwoSporSK :=
  i1416TwoSporSK_iff.2 (rowK hM11)

theorem i1416Chev2SporListK_of_rows
    (hM11 : Chev2Rows.CRow .M 11) : I1416Chev2SporListK :=
  i1416Chev2SporListK_iff.2 (crowK hM11)

end CFSG.HardMathSupport.Dickson.BMRows
