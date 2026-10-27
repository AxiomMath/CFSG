module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4ThreeProof
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4Kill
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympU4Surv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem genericKill_or_surv_of_FU4_data {Y : Type} [Group Y] (hF : FU4 Y) (α : MulAut Y)
    (hα : α * α = 1) :
    GenericKill Y α ∨ ∃ (p f : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (h : UnitaryFieldData p f K),
      (p ≠ 2 ∧ p ^ f % 8 ≠ 7 ∧ Nat.card K = (p ^ f) ^ 2) ∧
      ∃ (e : Y ≃* hypPSU h 2 0) (α' : MulAut (hypPSU h 2 0)),
        (∀ x, e (α x) = α' (e x)) ∧ SurvU4Orth h α' := by
  obtain ⟨p, f, hp, hf, hp2, hq8, hL⟩ := hF
  obtain ⟨K, iK, fK, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (Y ≃* StatedProj (StatedSU 4 (p ^ f) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have : Fact p.Prime := ⟨hp⟩
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  have : CharP K p := h.charP
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  have e : Y ≃* hypPSU h 2 0 := e₀.trans (hypPSUEquivStatedProj h hR₀ (by omega)).symm
  set α' : MulAut (hypPSU h 2 0) := e.symm.trans (α.trans e) with hα'
  have hcomm : ∀ x, e (α x) = α' (e x) := fun x => by simp [hα']
  have hα'2 : α' ^ 2 = 1 := by
    ext s
    obtain ⟨x, rfl⟩ := e.surjective s
    rw [sq, MulAut.mul_apply, ← hcomm, ← hcomm]
    have : α (α x) = x := by
      have := congrArg (fun a : MulAut Y => a x) hα
      simpa using this
    rw [this]
    rfl
  rcases genericKill_or_survU4Orth_of_hyp minIndexU33 h hp2 α' hα'2 with hk | hS
  · exact Or.inl (genericKill_of_mulEquiv e α α' hcomm hk)
  · exact Or.inr ⟨p, f, K, iK, fK, h, ⟨hp2, hq8, hcard⟩, e, α', hcomm, hS⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
