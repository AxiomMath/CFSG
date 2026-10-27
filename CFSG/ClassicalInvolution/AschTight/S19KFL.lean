module

public import CFSG.ClassicalInvolution.AschTight.S19TStmt
public import CFSG.ClassicalInvolution.AschTight.S19KBridge
public import CFSG.ClassicalInvolution.AschTight.S19KLinFL
public import CFSG.ClassicalInvolution.AschTight.S19KUniIn
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem factFL : S19T.FactFL := by
  intro p e _ hp2 hq E _ _ _ Ω t k e' ht hM L hL φ hφ
  obtain ⟨M⟩ := hM
  have hD4 : t ≠ .trialityD4 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain rfl : e = e' := (M.exp_eq_f hD4).symm
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨θ, hθ, hker, rfl⟩ := exists_theta_psl M hL
    have hodd : Odd (Nat.card (GaloisField p e)) := by
      rw [hcard]
      exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    exact flLin hodd (by rw [hcard]; exact hq)
      (ModelFacts.LinearAut.linearAutClassification hp2 hq le_rfl) θ hθ hker φ hφ
  · obtain ⟨θ, hθ, hker, rfl⟩ := exists_theta_psu hp2 M hL
    exact flUni (ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq) hp2 hq hcard θ hθ hker φ hφ

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
