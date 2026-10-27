module

public import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import CFSG.LieType.AlgebraicGroups.DerivedSemisimple

public noncomputable section

open WithConv TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
variable {M : Type w} [AddCommGroup M] [Module k M] [Comodule k H M]

theorem exists_subcomodule_span_pointOrbit (m : M) :
    ∃ N : Subcomodule k H M,
      N.toSubmodule = Submodule.span k
        (Set.range fun g : WithConv (H →ₐ[k] k) => basePointsRepresentation (H := H) M g m) := by
  let E : Submodule k M := Submodule.span k
    (Set.range fun g : WithConv (H →ₐ[k] k) => basePointsRepresentation (H := H) M g m)
  have hstable : ∀ g : WithConv (H →ₐ[k] k), ∀ x ∈ E,
      basePointsRepresentation (H := H) M g x ∈ E := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span (Set.mem_range_self (g * h))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact E.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact E.smul_mem a hx
  let N : Subcomodule k H M := Subcomodule.ofEndOfPointStable (K := k) E (by
    intro g x hx
    rw [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    exact Submodule.tmul_mem_baseChange_of_mem _ (hstable (toConv g) x hx))
  exact ⟨N, Subcomodule.ofEndOfPointStable_toSubmodule _ _⟩

theorem exists_cyclic_pointOrbitSubcomodule (m : M) :
    ∃ N : Subcomodule k H M,
      N.toSubmodule = Submodule.span k
        (Set.range fun g : WithConv (H →ₐ[k] k) => basePointsRepresentation (H := H) M g m) ∧
      letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
      ∃ n : N, (n : M) = m ∧
        Submodule.span k (Set.range fun g : WithConv (H →ₐ[k] k) =>
          basePointsRepresentation (H := H) N g n) = ⊤ := by
  obtain ⟨N, hN⟩ := exists_subcomodule_span_pointOrbit (k := k) (H := H) m
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  have hm : m ∈ N := by
    change m ∈ N.toSubmodule
    rw [hN]
    have hm' : basePointsRepresentation (H := H) M (1 : WithConv (H →ₐ[k] k)) m ∈
        Submodule.span k (Set.range fun g : WithConv (H →ₐ[k] k) =>
          basePointsRepresentation (H := H) M g m) :=
      Submodule.subset_span (Set.mem_range_self (1 : WithConv (H →ₐ[k] k)))
    simpa only [map_one, Module.End.one_apply] using hm'
  let n : N := ⟨m, hm⟩
  refine ⟨N, hN, n, rfl, ?_⟩
  let f : N →ₗ[k] M := SMulMemClass.subtype N
  have hf : Function.Injective f := Subtype.val_injective
  apply (Submodule.map_injective_of_injective (f := f) hf).eq_iff.mp
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top]
  have hfun : f ∘ (fun g : WithConv (H →ₐ[k] k) => basePointsRepresentation (H := H) N g n) =
      fun g : WithConv (H →ₐ[k] k) => basePointsRepresentation (H := H) M g m := by
    funext g
    simpa only [Function.comp_apply, f, SMulMemClass.subtype_apply,
      Subcomodule.subtype_apply] using
      DerivedSemisimple.hom_basePointsRepresentation (Subcomodule.subtype N) g n
  rw [hfun, ← hN]
  ext x
  constructor
  · intro hx
    change x ∈ N at hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    change (x : M) ∈ N
    exact x.2

omit [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] in
theorem point_line_subcomodule_iff (N : Subcomodule k H M)
    (g : WithConv (H →ₐ[k] k)) (n : N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
    basePointsRepresentation (H := H) N g n ∈ k ∙ n ↔
      basePointsRepresentation (H := H) M g (n : M) ∈ k ∙ (n : M) := by
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  have hpoint : ((basePointsRepresentation (H := H) N g n : N) : M) =
      basePointsRepresentation (H := H) M g (n : M) := by
    simpa only [Subcomodule.subtype_apply] using
      DerivedSemisimple.hom_basePointsRepresentation (Subcomodule.subtype N) g n
  have hmem := Submodule.apply_mem_span_image_iff_mem_span
    (f := SMulMemClass.subtype N) (x := basePointsRepresentation (H := H) N g n)
    (s := ({n} : Set N)) (show Function.Injective (SMulMemClass.subtype N) from
      Subtype.val_injective)
  simpa only [Set.image_singleton, SMulMemClass.subtype_apply, hpoint] using hmem.symm

omit [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] in
theorem differential_line_subcomodule_iff (N : Subcomodule k H M)
    (d : Derivation k H (Bialgebra.CounitAlgebra k H k)) (n : N) :
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
    differential (R := k) (H := H) (M := N) d n ∈ k ∙ n ↔
      differential (R := k) (H := H) (M := M) d (n : M) ∈ k ∙ (n : M) := by
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  have hdiff : ((differential (R := k) (H := H) (M := N) d n : N) : M) =
      differential (R := k) (H := H) (M := M) d (n : M) := by
    simpa only [Subcomodule.subtype_apply] using (Subcomodule.subtype N).map_differential d n
  have hmem := Submodule.apply_mem_span_image_iff_mem_span
    (f := SMulMemClass.subtype N) (x := differential (R := k) (H := H) (M := N) d n)
    (s := ({n} : Set N)) (show Function.Injective (SMulMemClass.subtype N) from
      Subtype.val_injective)
  simpa only [Set.image_singleton, SMulMemClass.subtype_apply, hdiff] using hmem.symm

end CFSG.LieType.AlgebraicGroups
