module

public import CFSG.GH74.Generic.BProg.Stage1Split

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

@[expose] def Stage1NontrivNonsolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → QShapeNS (↥K ⧸ pPrimeCore 2 ↥K) → ∀ A : Subgroup G, IsSource2 x K A →
      ∀ (y : G) (Lb : Subgroup (CentralizerBar x)) (E : Subgroup G) (Ib : Subgroup (CentralizerBar x)),
        IsE 2 A E → NonsolvAdm x y K E Lb Ib → ¬ NbhdSemisimple x y Lb → thetaHalfPrime A ≠ ⊥

@[expose] def Stage1NontrivSolv : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → NoAltJ2 G → ∀ (x : G) (K : Subgroup G),
    IsJ2Circ x K → QShapeNS (↥K ⧸ pPrimeCore 2 ↥K) → ∀ A : Subgroup G, IsSource2 x K A →
      ∀ (y : G) (Lb : Subgroup (CentralizerBar x)) (E : Subgroup G) (Ib : Subgroup (CentralizerBar x)),
        IsE 2 A E → SolvAdm x y K E Lb Ib → ¬ NbhdSemisimple x y Lb → thetaHalfPrime A ≠ ⊥

theorem stage1Nontriv_of_branches (hN : Stage1NontrivNonsolv) (hS : Stage1NontrivSolv) :
    Stage1Nontriv := by
  intro G _ _ hyp noAlt x K hcirc hP A hsrc hnot
  have h : ∃ (y : G) (Lb : Subgroup (CentralizerBar x)), IsAdmPair x K A y Lb ∧
      ¬ NbhdSemisimple x y Lb := by
    by_contra h
    push Not at h
    exact hnot fun y Lb hadm => h y Lb hadm
  obtain ⟨y, Lb, hadm, hns⟩ := h
  obtain ⟨E, Ib, hE, hcase⟩ := hadm.adm
  rcases hcase with hn | hs
  · exact hN G hyp noAlt x K hcirc hP A hsrc y Lb E Ib hE hn hns
  · exact hS G hyp noAlt x K hcirc hP A hsrc y Lb E Ib hE hs hns

end CFSG.GH74.Generic.BProg.B1
