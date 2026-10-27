module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthOddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K] {d : ℕ}

@[expose] def EvenOrthogonalSymmetryCentralizer (Q : QuadraticForm K (Fin d → K)) : Prop :=
  ∀ v : Fin d → K, Q v = 1 →
    (∀ x, (symmetryGL Q v : Matrix (Fin d) (Fin d) K) *ᵥ x = x + polar Q x v • v) ∧
    (∀ x y : vPerp Q v, vQuotForm Q v (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      polar Q x y) ∧
    (vQuotForm Q v).IsAlt ∧ (vQuotForm Q v).Nondegenerate ∧
    Module.finrank K (vQuot Q v) + 2 = d ∧
    ∃ ρ : symmetryCentralizer Q v →* LinearMap.GeneralLinearGroup K (vQuot Q v),
      (∀ (g : symmetryCentralizer Q v) (x y : vPerp Q v),
        (y : Fin d → K) = ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K) →
          (ρ g : vQuot Q v →ₗ[K] vQuot Q v) (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk y) ∧
      ρ.range = bilinIsometryGroup (vQuotForm Q v) ∧
      ρ.ker = Subgroup.zpowers ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ ∧
      ((matrixDerived Q ⊓ symmetryCentralizer Q v).subgroupOf (symmetryCentralizer Q v)).map ρ =
        bilinIsometryGroup (vQuotForm Q v) ∧
      ∀ H : Subgroup (MulAut (matrixProjectiveDerived Q)),
        (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range ≤
          H →
        H ≤ matrixProjectiveImage Q →
        CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {symmetryAut Q v}) = ⊥

theorem evenOrthogonalSymmetryCentralizer_of_regular {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (Q : QuadraticForm K (Fin (2 * n) → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    EvenOrthogonalSymmetryCentralizer Q := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  intro v hv
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  refine ⟨fun x => by rw [symmetryGL_mulVec_of_charTwo hv, polar_comm], vQuotForm_mk Q v,
    vQuotForm_isAlt Q v, vQuotForm_nondegenerate hQ hv0, finrank_vQuot hQ hv,
    symmetryRestrict hQ hv, fun g x y hxy => ?_, range_symmetryRestrict hQ hv hE,
    ker_symmetryRestrict hQ hv, map_derived_symmetryRestrict hQ hv hE,
    fun H hInn hHE => oddCore_centralizer_symmetryAut hf hK rfl hn hQ hT hE hv H hInn hHE⟩
  rw [symmetryRestrict_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hxy.symm)

theorem even_orthogonal_symmetry_centralizer_odd_core (G : Type) [Group G] (t : StatedLieTag)
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ) (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          EvenOrthogonalSymmetryCentralizer (coordinateQuadPlus n K)
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          EvenOrthogonalSymmetryCentralizer (coordinateQuadMinus n K hn b c)
    | _ => False := by
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := h.1
    intro K _ _ hK _
    have hreg := regular_coordinateQuadPlus n K (by omega)
    exact evenOrthogonalSymmetryCentralizer_of_regular hf hK (by omega) _ hreg.1 hreg.2
      (commutator_coordinateQuadPlus n K (by omega))
  · obtain ⟨-, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr _
    have hreg := regular_coordinateQuadMinus n K b c hn hirr
    exact evenOrthogonalSymmetryCentralizer_of_regular hf hK (by omega) _ hreg.1 hreg.2
      (commutator_coordinateQuadMinus n K b c hn hirr)

end CFSG.ComponentClassification.UnbalancedCatalog
