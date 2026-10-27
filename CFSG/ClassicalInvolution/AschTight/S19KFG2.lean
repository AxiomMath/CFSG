module

public import CFSG.ClassicalInvolution.AschTight.S19QStmt
public import CFSG.ClassicalInvolution.AschTight.S19KBridge
public import CFSG.ClassicalInvolution.AschTight.S19KOutL
public import CFSG.ClassicalInvolution.AschTight.S19KOutU2
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem factFG2 : S19Q.FactFG2 := by
  intro p e _ hp2 hq E _ _ _ Ω t k e' ht hM L hL
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
    exact fg2Lin hodd (by rw [hcard]; exact hq)
      (ModelFacts.LinearAut.linearAutClassification hp2 hq le_rfl) θ hθ hker
  · obtain ⟨θ, hθ, hker, rfl⟩ := exists_theta_psu hp2 M hL
    exact fg2Uni (ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq) hp2 hq θ hθ hker

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
