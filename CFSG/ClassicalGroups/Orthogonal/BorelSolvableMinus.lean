module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isSolvable_tailTorus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (r : ℕ) :
    Group.IsSolvable ↥(tailTorus r (minusTailForm K b c)) := by
  let qA : QuadraticForm K (Fin 2 → K) := minusTailForm K b c
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) => (g : _ → _)) DFunLike.coe_injective
  have hO : Group.IsSolvable
      ↥(TauCeti.QuadraticMap.orthogonalGroup qA) := by
    refine CFSG.StandardType.LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two
      (nondegenerate_minusTailForm hirr) ?_
    rw [finrank_fin_two_fun]
  let φ : ((Fin r → Kˣ) × ↥(TauCeti.QuadraticMap.orthogonalGroup qA)) →*
      (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    { toFun := fun x : ((Fin r → Kˣ) ×
        ↥(TauCeti.QuadraticMap.orthogonalGroup qA)) => tailDiag r x.1 x.2.1
      map_one' := by
        refine LinearEquiv.ext fun v => ?_
        simp [tailDiag_apply, torusElt_apply]
      map_mul' := fun x y => by
        change tailDiag r (x.1 * y.1) (x.2.1 * y.2.1) =
          tailDiag r x.1 x.2.1 * tailDiag r y.1 y.2.1
        rw [tailDiag_mul] }
  have hrange : φ.range = tailDiagGroup r qA := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2.1, x.2.2, rfl⟩
    · rintro ⟨t, h, hh, rfl⟩
      exact ⟨(t, ⟨h, hh⟩), rfl⟩
  haveI hsrc : Group.IsSolvable
      ((Fin r → Kˣ) × ↥(TauCeti.QuadraticMap.orthogonalGroup qA)) := by
    haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup qA) := hO
    infer_instance
  haveI hdiag : Group.IsSolvable ↥(tailDiagGroup r qA) := by
    refine Group.isSolvable_of_surjective
      (f := φ.codRestrict (tailDiagGroup r qA) fun x => hrange ▸ ⟨x, rfl⟩) ?_
    intro y
    have hy : (y : (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)))) ∈ φ.range := hrange.symm ▸ y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (inf_le_right :
      tailTorus r qA ≤ tailDiagGroup r qA))
    (Subgroup.inclusion_injective _)

theorem isSolvable_borel_orth_minus {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (r : ℕ) :
    Group.IsSolvable ↥(tailBorel r (minusTailForm K b c)) := by
  let qA : QuadraticForm K (Fin 2 → K) := minusTailForm K b c
  let B := tailBorel r qA
  let U := tailUnipotent r qA
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) => (g : _ → _)) DFunLike.coe_injective
  haveI : Finite ↥B := Subtype.finite
  have hani : qA.Anisotropic := anisotropic_minusTailForm hirr
  have hUle : U ≤ B := tailUnipotent_le_tailBorel hani
  have hUn : (U.subgroupOf B).Normal := tailUnipotent_normal hani
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (U.subgroupOf B) := by
    have h := isPGroup_tailUnipotent (p := 2) (r := r) (qA := qA) hani
    exact h.of_equiv ((Subgroup.subgroupOfEquivOfLe tailUnipotent_le).trans
      (Subgroup.subgroupOfEquivOfLe hUle).symm)
  haveI : Group.IsSolvable ↥(U.subgroupOf B) := by
    haveI : Finite ↥(U.subgroupOf B) := Subtype.finite
    haveI : Group.IsNilpotent ↥(U.subgroupOf B) := IsPGroup.isNilpotent hU2
    infer_instance
  haveI hT : Group.IsSolvable ↥(tailTorus r qA) := isSolvable_tailTorus hirr r
  haveI : Group.IsSolvable (↥B ⧸ U.subgroupOf B) := by
    obtain ⟨e⟩ := nonempty_quotient_mulEquiv_tailTorus (r := r) (qA := qA) hani
    exact Group.isSolvable_of_surjective
      (f := (e.symm : ↥(tailTorus r qA) →* (↥B ⧸ U.subgroupOf B)))
      e.symm.surjective
  exact Group.isSolvable_of_subgroup_quotient (U.subgroupOf B)

end CFSG.ClassicalGroups.Orthogonal
