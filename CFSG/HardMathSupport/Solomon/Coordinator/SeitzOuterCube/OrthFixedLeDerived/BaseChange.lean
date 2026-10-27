module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldD4
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.OrthFixedLeDerived.OddDegree
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution TauCeti

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def linIncl :
    ((Fin d → k) ≃ₗ[k] (Fin d → k)) →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (matrixLinearIso (d := d) (K := K)).toMonoidHom.comp
    ((glIncl k).comp (matrixLinearIso (d := d) (K := k)).symm.toMonoidHom)

theorem linIncl_matrixLinearIso (A : GL (Fin d) k) :
    linIncl k (matrixLinearIso A) = matrixLinearIso (glIncl k A) := by
  simp [linIncl]

theorem linIncl_apply_vecIncl (g : (Fin d → k) ≃ₗ[k] (Fin d → k)) (v : Fin d → k) :
    linIncl k g (vecIncl k v) = vecIncl k (g v) := by
  obtain ⟨A, rfl⟩ := (matrixLinearIso (d := d) (K := k)).surjective g
  rw [linIncl_matrixLinearIso]
  exact mulVec_vecIncl k A v

theorem linIncl_mem_orthogonalGroup (hext : IsExtension k Q₀ Q)
    {g : (Fin d → k) ≃ₗ[k] (Fin d → k)} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q₀) :
    linIncl k g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  obtain ⟨A, rfl⟩ := (matrixLinearIso (d := d) (K := k)).surjective g
  rw [linIncl_matrixLinearIso]
  exact glIncl_mem_isometries k hext (A := A) hg

theorem linIncl_reflect (hext : IsExtension k Q₀ Q) {u : Fin d → k} (hu : Q₀ u ≠ 0) :
    linIncl k (reflect Q₀ u) = reflect Q (vecIncl k u) := by
  apply linearEquiv_ext_vecIncl k
  intro w
  rw [linIncl_apply_vecIncl, reflect_vecIncl k hext hu]

@[expose] noncomputable def orthIncl (hext : IsExtension k Q₀ Q) :
    TauCeti.QuadraticMap.orthogonalGroup Q₀ →* TauCeti.QuadraticMap.orthogonalGroup Q :=
  ((linIncl k).comp (TauCeti.QuadraticMap.orthogonalGroup Q₀).subtype).codRestrict _
    (fun g => linIncl_mem_orthogonalGroup k hext g.2)

theorem coe_orthIncl (hext : IsExtension k Q₀ Q) (g : TauCeti.QuadraticMap.orthogonalGroup Q₀) :
    ((orthIncl k hext g : TauCeti.QuadraticMap.orthogonalGroup Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      linIncl k (g : (Fin d → k) ≃ₗ[k] (Fin d → k)) := rfl

theorem map_vecIncl_ne_zero (hext : IsExtension k Q₀ Q) {u : Fin d → k} (hu : Q₀ u ≠ 0) :
    Q (vecIncl k u) ≠ 0 := by
  rw [hext]
  intro h
  exact hu (Subtype.ext (by simpa using h))

theorem orthIncl_reflectionOrthogonal (hext : IsExtension k Q₀ Q) (u : Fin d → k)
    [Invertible (Q₀ u)] [Invertible (Q (vecIncl k u))] :
    orthIncl k hext (TauCeti.QuadraticMap.reflectionOrthogonal Q₀ u) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q (vecIncl k u) := by
  have hu : Q₀ u ≠ 0 := (isUnit_of_invertible (Q₀ u)).ne_zero
  apply Subtype.ext
  rw [coe_orthIncl, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
    TauCeti.QuadraticMap.coe_reflectionOrthogonal, ← reflect_eq_reflection,
    ← reflect_eq_reflection]
  exact linIncl_reflect k hext hu

@[expose] noncomputable def detSquareClassMap :
    kˣ × Multiplicative (SquareClassGroup k) →* Kˣ × Multiplicative (SquareClassGroup K) :=
  (Units.map (k.subtype : k →* K)).prodMap
    (AddMonoidHom.toMultiplicative (k.subtype.squareClassMap.toAddMonoidHom))

theorem detSquareClassMap_apply (u : kˣ) (c : Multiplicative (SquareClassGroup k)) :
    detSquareClassMap k (u, c) = (Units.map (k.subtype : k →* K) u,
      Multiplicative.ofAdd (k.subtype.squareClassMap (Multiplicative.toAdd c))) := rfl

theorem detSquareClassMap_injective (hodd : Odd (Module.finrank k K)) :
    Function.Injective (detSquareClassMap k) := by
  rintro ⟨u, c⟩ ⟨u', c'⟩ h
  simp only [detSquareClassMap_apply, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hinj : Function.Injective (Units.map (k.subtype : k →* K)) :=
    Units.map_injective k.subtype_injective
  refine Prod.ext (hinj h1) ?_
  have h3 := squareClassMap_injective_of_odd_finrank (k := k) (K := K) hodd
    (Multiplicative.ofAdd.injective h2)
  exact Multiplicative.toAdd.injective h3

variable [Finite K] [Invertible (2 : K)] [Invertible (2 : k)]

theorem detSpinorNorm_orthIncl [Finite k] (hext : IsExtension k Q₀ Q)
    (hnd₀ : Q₀.Nondegenerate) (hnd : Q.Nondegenerate)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q₀) :
    detSpinorNorm hnd (orthIncl k hext g) = detSquareClassMap k (detSpinorNorm hnd₀ g) := by
  have h : (detSpinorNorm hnd).comp (orthIncl k hext) =
      (detSquareClassMap k).comp (detSpinorNorm hnd₀) := by
    have : NeZero (2 : k) := ⟨(isUnit_of_invertible (2 : k)).ne_zero⟩
    refine TauCeti.QuadraticMap.orthogonalGroup_hom_ext Q₀ hnd₀ fun u hu => ?_
    have hQu : Q (vecIncl k u) ≠ 0 := map_vecIncl_ne_zero k hext
      (isUnit_of_invertible (Q₀ u)).ne_zero
    letI : Invertible (Q (vecIncl k u)) := invertibleOfNonzero hQu
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, orthIncl_reflectionOrthogonal,
      detSpinorNorm_reflectionOrthogonal, detSpinorNorm_reflectionOrthogonal,
      detSquareClassMap_apply]
    refine Prod.ext (Units.ext (by simp)) ?_
    have hv : Q (vecIncl k u) = ((Q₀ u : k) : K) := hext u
    simp only [squareClassHom_apply, toAdd_ofAdd, RingHom.squareClassMap_apply]
    exact congrArg (Multiplicative.ofAdd ∘ squareClass) (Units.ext hv)
  exact DFunLike.congr_fun h g

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
