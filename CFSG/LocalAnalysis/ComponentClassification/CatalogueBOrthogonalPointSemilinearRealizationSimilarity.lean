module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealizationBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataFamily

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization

open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalPointAction CatalogueBOrthogonalPointKernel

universe u

variable {K : Type u} [Field K] {d : ℕ}

@[expose] def realizingSimilarity (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) : similarityPairs Q :=
  ⟨realizingPair sigma T, ⟨mu, by
    intro v
    change Q (coordinateSemilinearMap (realizingPair sigma T) v) =
      (mu : K) * sigma (Q v)
    rw [realizingPair_apply]
    exact hT v⟩⟩

theorem realizingSimilarity_val (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    (realizingSimilarity Q sigma T mu hT).val = realizingPair sigma T := rfl

theorem realizingSimilarity_left (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    (realizingSimilarity Q sigma T mu hT).val.left = realizingMatrix sigma T := rfl

theorem realizingSimilarity_right (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    (realizingSimilarity Q sigma T mu hT).val.right = sigma := rfl

theorem realizingSimilarity_apply (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (v : Fin d → K) :
    coordinateSemilinearMap (realizingSimilarity Q sigma T mu hT).val v = T v :=
  realizingPair_apply sigma T v

theorem realizingSimilarity_addEquiv (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    coordinateSemilinearMap (realizingSimilarity Q sigma T mu hT).val = T.toAddEquiv :=
  realizingPair_addEquiv sigma T

theorem realizingSimilarity_inverse_apply (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (v : Fin d → K) :
    coordinateSemilinearMap (realizingSimilarity Q sigma T mu hT)⁻¹.val v = T.symm v :=
  realizingPair_inverse_apply sigma T v

theorem realizingSimilarity_linearMap (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    coordinateSemilinearLinearMap (realizingSimilarity Q sigma T mu hT).val = T.toLinearMap :=
  realizingPair_linearMap sigma T

theorem realizingSimilarity_semilinearEquiv (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    coordinateSemilinearEquiv (realizingSimilarity Q sigma T mu hT).val = T :=
  realizingPair_semilinearEquiv sigma T

theorem exists_nonzero_quadratic_value (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0) :
    ∃ v, Q v ≠ 0 := by
  by_contra h
  push Not at h
  apply hQ
  apply QuadraticMap.ext
  intro v
  exact h v

theorem realizingSimilarity_multiplier (Q : QuadraticForm K (Fin d → K)) (hQ : Q ≠ 0)
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) :
    multiplier Q (realizingSimilarity Q sigma T mu hT) = mu := by
  apply multiplier_unique Q (exists_nonzero_quadratic_value Q hQ)
    (realizingSimilarity Q sigma T mu hT).val _ _
    (multiplier_spec Q (realizingSimilarity Q sigma T mu hT))
  intro v
  change Q (coordinateSemilinearMap (realizingSimilarity Q sigma T mu hT).val v) =
    (mu : K) * sigma (Q v)
  rw [realizingSimilarity_apply]
  exact hT v

theorem realizingSimilarity_point_submodule (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (L : Points Q) :
    (similarityPointAction Q (realizingSimilarity Q sigma T mu hT) L).val =
      L.val.map T.toLinearMap := by
  rw [similarityPointAction_submodule, realizingSimilarity_linearMap]
  rfl

theorem realizingSimilarity_pointMk (Q : QuadraticForm K (Fin d → K)) (sigma : K ≃+* K)
    (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (x : Fin d → K)
    (hx : x ≠ 0) (hQx : Q x = 0) :
    similarityPointAction Q (realizingSimilarity Q sigma T mu hT) (pointMk x hx hQx) =
      pointMk (T x) (fun h => hx (T.map_eq_zero_iff.mp h))
        (by rw [hT, hQx, map_zero, mul_zero]) := by
  apply Subtype.ext
  rw [realizingSimilarity_point_submodule, pointMk_submodule, pointMk_submodule,
    Submodule.map_span, Set.image_singleton]
  rfl

theorem pointPerm_eq_realizingSimilarity (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (phi : Equiv.Perm (Points Q))
    (hphi : ∀ L : Points Q, (phi L).val = L.val.map T.toLinearMap) :
    phi = similarityPointAction Q (realizingSimilarity Q sigma T mu hT) := by
  apply Equiv.ext
  intro L
  apply Subtype.ext
  exact (hphi L).trans (realizingSimilarity_point_submodule Q sigma T mu hT L).symm

theorem pointPerm_mem_similarityPointImage (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (phi : Equiv.Perm (Points Q))
    (hphi : ∀ L : Points Q, (phi L).val = L.val.map T.toLinearMap) :
    phi ∈ similarityPointImage Q :=
  ⟨realizingSimilarity Q sigma T mu hT,
    (pointPerm_eq_realizingSimilarity Q sigma T mu hT phi hphi).symm⟩

theorem similarity_point_realization (Q : QuadraticForm K (Fin d → K))
    (sigma : K ≃+* K) (T : (Fin d → K) ≃ₛₗ[sigma.toRingHom] (Fin d → K)) (mu : Kˣ)
    (hT : ∀ v, Q (T v) = (mu : K) * sigma (Q v)) (phi : Equiv.Perm (Points Q))
    (hphi : ∀ L : Points Q, (phi L).val = L.val.map T.toLinearMap) :
    ∃ g : similarityPairs Q,
      g.val.left = realizingMatrix sigma T ∧ g.val.right = sigma ∧
      coordinateSemilinearMap g.val = T.toAddEquiv ∧
      (∀ L : Points Q, (similarityPointAction Q g L).val = L.val.map T.toLinearMap) ∧
      phi = similarityPointAction Q g ∧ phi ∈ similarityPointImage Q :=
  ⟨realizingSimilarity Q sigma T mu hT, rfl, rfl,
    realizingSimilarity_addEquiv Q sigma T mu hT,
    realizingSimilarity_point_submodule Q sigma T mu hT,
    pointPerm_eq_realizingSimilarity Q sigma T mu hT phi hphi,
    pointPerm_mem_similarityPointImage Q sigma T mu hT phi hphi⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointSemilinearRealization
