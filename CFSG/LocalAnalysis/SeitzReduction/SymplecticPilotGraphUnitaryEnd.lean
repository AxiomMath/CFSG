module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndFieldBasic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.SeitzReduction.F4Pilot (normalizerMulAut)

@[expose] def PrimeFormBarInvertsInput : Prop :=
  ∀ (f : ℕ) (K' : Type) [Field K'] (h : UnitaryFieldData 2 f K') (m : ℕ) (C : GL (Fin m) K')
    (hC : IsPrimeFormGram C), 3 ≤ m → ∀ φ : K' ≃+* K', (∀ x, φ x = h.bar x) →
    ∀ d ∈ primeFormD h (C : Matrix (Fin m) (Fin m) K'),
      d * primeFormFieldHom h hC φ * d⁻¹ * (primeFormFieldHom h hC φ)⁻¹ ∈
          inner (primeFormP h (C : Matrix (Fin m) (Fin m) K')) →
        d ∈ inner (primeFormP h (C : Matrix (Fin m) (Fin m) K'))

section Model

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') {m : ℕ} {C : GL (Fin m) K'}
  (hC : IsPrimeFormGram C) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ 2 ^ f = 2))

include hC hm hq in
theorem primeFormFieldFactor_conj (x : primeFormP h (C : Matrix (Fin m) (Fin m) K')) :
    primeFormFieldFactor h hC hm hq (MulAut.conj x) = 1 := by
  rw [← MonoidHom.mem_ker, ker_primeFormFieldFactor h hC hm hq]
  exact UnitaryPilot.inner_le_primeFormD h _ ⟨x, rfl⟩

end Model

section NormalForm

theorem exists_primeFormFieldHom_eq_of_lieModel_PSU {S : Type} [Group S] {m f : ℕ}
    (hS : LieModel S .PSU m 2 f) {θ : MulAut S} (hθθ : θ * θ = 1)
    (hout : θ ∉ (MulAut.conj : S →* MulAut S).range) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (C₀ : GL (Fin m) K')
      (hC₀ : IsPrimeFormGram C₀) (_ : 3 ≤ m) (_ : ¬(m = 3 ∧ 2 ^ f = 2)) (φ : K' ≃+* K')
      (ε : S ≃* primeFormP h (C₀ : Matrix (Fin m) (Fin m) K')),
      ((C₀ : Matrix (Fin m) (Fin m) K') = 1 ∨
        ∃ r, m = 2 * r ∧ (C₀ : Matrix (Fin m) (Fin m) K') = blockSwapJ m r) ∧
      (∀ x, φ x = h.bar x) ∧ MulAut.congr ε θ = primeFormFieldHom h hC₀ φ := by
  have hadm : StatedLieAdmissible .PSU m 2 f := F4Pilot.statedLieAdmissible_of_lieModel hS
  have hm : 3 ≤ m := hadm.2.2.1
  have hq : ¬(m = 3 ∧ 2 ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hS
  have hC : IsPrimeFormGram (1 : GL (Fin m) K') := isPrimeFormGram_one
  set β := MulAut.congr ψ θ with hβdef
  have hβo : β ∉ inner (primeFormP h ((1 : GL (Fin m) K') : Matrix (Fin m) (Fin m) K')) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hβ1 : β ≠ 1 := fun h1 => hβo (h1 ▸ one_mem _)
  have hβ : orderOf β = 2 :=
    orderOf_eq_prime (by rw [_root_.sq, hβdef, ← map_mul, hθθ, map_one]) hβ1
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts h hC hm hq β hβ
  rcases hcases with hid | hbar
  · exfalso
    apply hβo
    refine hDinner _ ?_ hβ
    rw [← ker_primeFormFieldFactor h hC hm hq, MonoidHom.mem_ker]
    exact hid
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ', -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hm hq β hβ hbar
  refine ⟨K', inferInstance, h, C₀, hC₀, hm, hq, primeFormFieldFactor h hC hm hq β,
    ψ.trans θ'.symm, hcase₀, hbar, MulEquiv.ext fun x => ?_⟩
  have h1 := hθβ (θ' x)
  rw [MulEquiv.symm_apply_apply] at h1
  change θ'.symm (ψ (θ (ψ.symm (θ' x)))) =
    primeFormFieldAut h hC₀ (primeFormFieldFactor h hC hm hq β) x
  have h2 : ψ (θ (ψ.symm (θ' x))) = β (θ' x) := rfl
  rw [h2, h1, MulEquiv.symm_apply_apply]

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

end NormalForm

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem primeFormFieldFactor_fieldHom {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K')
    {m : ℕ} {C : GL (Fin m) K'} (hC : IsPrimeFormGram C) (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ 2 ^ f = 2))
    (φ : K' ≃+* K') : primeFormFieldFactor h hC hm hq (primeFormFieldHom h hC φ) = φ := by
  have h1 := primeFormFieldFactor_apply h hC hm hq 1 φ
  rwa [map_one, one_mul] at h1

end Endgame

end CFSG.SeitzReduction.SymplecticPilot
