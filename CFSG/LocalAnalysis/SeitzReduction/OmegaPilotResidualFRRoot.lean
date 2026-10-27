module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixTwist
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthQuotient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)

section Root

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem kappa_projHom_eichler {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    {u w : Fin d → K} (E E' : orthDerived Q)
    (hE : (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) = eichler Q u w)
    (hE' : (E' : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      eichler Q (coordinateSemilinearMap S.val u) (coordinateSemilinearMap S.val w)) :
    matrixProjectiveConjugationHom Q S (projHom Q E) = projHom Q E' :=
  kappa_projHom S E E' fun x => by
    rw [hE', hE, semilinear_eichler_conj (coordinateSemilinearMap_smul S.val)
      (pairSemilinearMap_quad hS)]

theorem quad_coordinateSemilinearMap {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    (x : Fin d → K) : Q (coordinateSemilinearMap S.val x) = S.val.right (Q x) :=
  hS x

theorem eichler_smul_apply_of_singular {u w : Fin d → K} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (c : K) (x : Fin d → K) :
    eichler Q u (c • w) x = x + c • (polar Q x u • w - polar Q x w • u) := by
  have hpol : polar Q u (c • w) = 0 := by rw [polar_smul_right, huw, smul_zero]
  rw [eichler_apply hu hpol, QuadraticMap.map_smul, hw, smul_zero, zero_mul, add_zero,
    polar_smul_right, smul_eq_mul]
  module

variable [Finite K] [CharP K 2]

theorem right_eq_one_of_fix_rootGroup (hQ : (polarBilin Q).Nondegenerate)
    (hT3 : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hQ0 : ∃ v, Q v ≠ 0) {S : similarityPairs Q} (hS : S ∈ unitMultiplierPairs Q)
    {u w : Fin d → K} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (hind : LinearIndependent K ![u, w])
    (hfix : ∀ (c : K) (E : orthDerived Q),
      (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) = eichler Q u (c • w) →
        matrixProjectiveConjugationHom Q S (projHom Q E) = projHom Q E) :
    S.val.right = 1 := by
  set T := coordinateSemilinearMap S.val with hTdef
  set σ := S.val.right with hσ
  have hTu : Q (T u) = 0 := by rw [hTdef, quad_coordinateSemilinearMap hS, hu, map_zero]
  have hTw : Q (T w) = 0 := by rw [hTdef, quad_coordinateSemilinearMap hS, hw, map_zero]
  have hTuw : polar Q (T u) (T w) = 0 := by
    rw [hTdef, polar_coordinateSemilinearMap hS, huw, map_zero]
  have key : ∀ c : K, ∀ x : Fin d → K,
      x + σ c • (polar Q x (T u) • T w - polar Q x (T w) • T u) =
        x + c • (polar Q x u • w - polar Q x w • u) := by
    intro c x
    set E : orthDerived Q := ⟨eichler Q u (c • w), eichler_mem_orthDerived hQ hT3 _ _⟩
    set E' : orthDerived Q := ⟨eichler Q (T u) (T (c • w)), eichler_mem_orthDerived hQ hT3 _ _⟩
    have h1 := kappa_projHom_eichler hS E E' rfl rfl
    rw [hfix c E rfl] at h1
    have h2 : E = E' := projHom_injective hQ0 h1
    have h3 := congrArg (fun F : orthDerived Q => (F : (Fin d → K) ≃ₗ[K] (Fin d → K)) x) h2
    simp only [E, E'] at h3
    rw [hTdef, coordinateSemilinearMap_smul, ← hTdef, ← hσ,
      eichler_smul_apply_of_singular hu hw huw, eichler_smul_apply_of_singular hTu hTw hTuw] at h3
    exact h3.symm
  have hD : ∀ x : Fin d → K,
      polar Q x (T u) • T w - polar Q x (T w) • T u = polar Q x u • w - polar Q x w • u := by
    intro x
    have := key 1 x
    rwa [map_one, one_smul, one_smul, add_right_inj] at this
  have hu0 : u ≠ 0 := hind.ne_zero 0
  obtain ⟨x₀, hx₀⟩ := exists_polar_eq_one hQ hu0
  have hDx : polar Q x₀ u • w - polar Q x₀ w • u ≠ 0 := by
    intro h0
    rw [polar_comm, hx₀, one_smul] at h0
    have h1 : (-polar Q x₀ w) • u + (1 : K) • w = 0 := by
      rw [one_smul, neg_smul, ← h0]
      abel
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hind) _ _ h1).2
  apply RingEquiv.ext
  intro c
  have h1 := key c x₀
  rw [hD, add_right_inj, ← sub_eq_zero, ← sub_smul] at h1
  have h2 := (smul_eq_zero.mp h1).resolve_right hDx
  exact sub_eq_zero.mp h2

end Root

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem plusFieldPart_eq_one_of_fix_rootGroup (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {u w : Fin (2 * n) → K} (hu : coordinateQuadPlus n K u = 0)
    (hw : coordinateQuadPlus n K w = 0) (huw : polar (coordinateQuadPlus n K) u w = 0)
    (hind : LinearIndependent K ![u, w])
    (β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
    (hfix : ∀ (c : K) (E : orthDerived (coordinateQuadPlus n K)),
      (E : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
        eichler (coordinateQuadPlus n K) u (c • w) →
        β (projHom _ E) = projHom _ E) :
    plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn β = 1 := by
  have hreg := regular_coordinateQuadPlus n K (by omega)
  have hβE : β ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [plusImage_eq_top hn]
    exact Subgroup.mem_top β
  obtain ⟨S, hS, rfl⟩ := exists_unit_rep hβE
  have hσ : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn
      (matrixProjectiveConjugationHom _ S) = S.val.right :=
    orthAutFieldPart_kappa _ _ S
  rw [hσ]
  exact right_eq_one_of_fix_rootGroup hreg.1 hreg.2
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_ne_zero_of_polar_nondegenerate
      (by omega) hreg.1) hS hu hw huw hind hfix

end Plus

end CFSG.SeitzReduction.OmegaPilot
