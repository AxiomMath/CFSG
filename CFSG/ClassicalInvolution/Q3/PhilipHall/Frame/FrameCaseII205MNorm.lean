module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3Stmt
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.T3
open scoped commutatorElement

section Join

variable {X : Type} [Group X]

theorem le_normalizer_iSup_of_forall {P : Subgroup X} {S : Set (Subgroup X)}
    (h : ∀ p ∈ P, ∀ Q ∈ S, ∀ x ∈ Q, p * x * p⁻¹ ∈ Q) :
    P ≤ Subgroup.normalizer ((⨆ Q ∈ S, Q : Subgroup X) : Set X) := by
  have key : ∀ p ∈ P, ∀ m ∈ (⨆ Q ∈ S, Q : Subgroup X),
      p * m * p⁻¹ ∈ (⨆ Q ∈ S, Q : Subgroup X) := by
    intro p hp
    have hT : (⨆ Q ∈ S, Q : Subgroup X) ≤
        (⨆ Q ∈ S, Q : Subgroup X).comap (MulAut.conj p).toMonoidHom := by
      refine iSup₂_le fun Q hQ => ?_
      intro x hx
      exact le_iSup₂ (f := fun (Q : Subgroup X) (_ : Q ∈ S) => Q) Q hQ (h p hp Q hQ x hx)
    intro m hm
    exact hT hm
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    exact key p hp m hm
  · intro hm
    have h' := key p⁻¹ (P.inv_mem hp) _ hm
    have e : p⁻¹ * (p * m * p⁻¹) * p⁻¹⁻¹ = m := by group
    rwa [e] at h'

theorem conj_mem_of_commutator_le {P Q : Subgroup X} (hPQ : ⁅P, Q⁆ ≤ Q) {p x : X}
    (hp : p ∈ P) (hx : x ∈ Q) : p * x * p⁻¹ ∈ Q := by
  have h1 : ⁅p, x⁆ ∈ Q := hPQ (Subgroup.commutator_mem_commutator hp hx)
  have h2 : p * x * p⁻¹ = ⁅p, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact Q.mul_mem h1 hx

end Join

section Subnormal

variable {X : Type} [Group X] [Finite X]

theorem self_mem_aStar {Ω : Set (Subgroup X)} (K : Subgroup X) : K ∈ aStar Ω K :=
  Relation.ReflTransGen.refl

end Subnormal

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
