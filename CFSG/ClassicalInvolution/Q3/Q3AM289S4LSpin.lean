module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LShape
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3 CFSG.LieType.Universal.Spin
  CliffordAlgebra
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


theorem modelPkg_of_spin {ι : Type} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm 𝔽₃ (ι → 𝔽₃))
    (𝓕 : Set (Subgroup (spinGroup Q))) [Finite (spinGroup Q)]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank 𝔽₃ (ι → 𝔽₃))
    (hperf : Group.IsPerfect (spinGroup Q)) (hrange : (spinAction Q).range = elementaryGroup Q)
    (cq : Q3W.CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars 𝔽₃ (ι → 𝔽₃)))
    (hconj : ∀ R ∈ 𝓕, ∀ g : spinGroup Q, conjSub g R ∈ 𝓕)
    (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : spinGroup Q, R' = conjSub g R)
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hopp : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False) :
    ModelPkg (⟨spinGroup Q, 𝓕⟩ : CompData) := by
  have hodd := CFSG.ClassicalInvolution.ModelFacts.TG3.odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.TG3.two_ne_zero_three
  have h3 : (3 : 𝔽₃) = 0 := by
    have := CharP.cast_eq_zero 𝔽₃ 3
    simpa using this
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hnt : Nontrivial (ι → 𝔽₃) :=
    Module.finrank_pos_iff.mp (show 0 < Module.finrank 𝔽₃ (ι → 𝔽₃) by omega)
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  refine ⟨inferInstance, by rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top,
    hsingle, hsl2, ι → 𝔽₃, inferInstance, inferInstance, inferInstance, Q, spinAction Q,
    spinGroup.negOne Q hQnd.ne_zero, ?_, vFrames_of_regular hodd h3 hQ hdim, hopp⟩
  exact
    { range := hrange
      ker_le := ker_spinAction_le_center Q
      ker_two := fun x hx => (mem_ker_spinAction_iff Q hQnd x).mp hx
      z_sq := spinGroup.negOne_mul_self _ _
      z_mem := (mem_ker_spinAction_iff Q hQnd _).mpr (Or.inr rfl)
      map_mem := fun R hR => by
        obtain ⟨i, Fr, hFr, -⟩ := cq.map_mem R hR
        exact ⟨Fr, hFr⟩
      inj := cq.inj
      map_inj := fun R hR R' hR' h =>
        Q3W.eq_of_map_eq_of_pow3 (spinAction Q) cq.ker_le cq.cop (cq.pow3 R hR) (cq.pow3 R' hR') h
      surj := fun Fr => cq.surj _ ⟨_, IsFundamental.of_frame Fr⟩
      center_le := cq.center_le
      conj := hconj }

theorem s4LinkModelLeafAt_of_spin {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm 𝔽₃ (ι → 𝔽₃)) (𝓕 : Set (Subgroup (spinGroup Q))) [Finite (spinGroup Q)]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank 𝔽₃ (ι → 𝔽₃))
    (hperf : Group.IsPerfect (spinGroup Q)) (hrange : (spinAction Q).range = elementaryGroup Q)
    (cq : Q3W.CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars 𝔽₃ (ι → 𝔽₃)))
    (hconj : ∀ R ∈ 𝓕, ∀ g : spinGroup Q, conjSub g R ∈ 𝓕)
    (hsingle : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : spinGroup Q, R' = conjSub g R)
    (hsl2 : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, 𝔽₃)))
    (hopp : ∀ F₁ F₂ : Frame Q, F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1) → False) :
    Q3AM.S4LinkModelLeafAt (⟨spinGroup Q, 𝓕⟩ : CompData) :=
  s4LinkModelLeafAt_of_pkg
    (modelPkg_of_spin Q 𝓕 hQ hdim hperf hrange cq hconj hsingle hsl2 hopp)

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
