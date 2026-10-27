module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalGraph
public import CFSG.LieType.AlgebraicGroups.TangentDimensionBound
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv TensorProduct

open scoped CFSG.ConvolutionPoints

section Cover

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [Algebra k A]

theorem finrank_tangentSpace_quotient_le (S : Set (A →ₐ[k] k))
    [Algebra.FiniteType k (A ⧸ pointsIdeal S)] [IsDomain (A ⧸ pointsIdeal S)]
    [Algebra.Smooth k (A ⧸ pointsIdeal S)] (hS : pointsZero k (pointsIdeal S) = S)
    {I : Type} [Finite I] [Nonempty I] (a b : I → ℕ) (f : ∀ i, A →ₐ[k] TorusAffine k (a i) (b i))
    (hcov : (⋃ i, Set.range fun z : TorusAffine k (a i) (b i) →ₐ[k] k => z.comp (f i)) = S)
    {n : ℕ} (hn : ∀ i, a i + b i ≤ n) (x : A ⧸ pointsIdeal S →ₐ[k] k) :
    Module.finrank k (TangentSpace k (A ⧸ pointsIdeal S) x) ≤ n := by
  have : Fintype I := Fintype.ofFinite I
  have hf : ∀ i, ∀ z : TorusAffine k (a i) (b i) →ₐ[k] k, z.comp (f i) ∈ S := fun i z =>
    (Set.ext_iff.1 hcov _).1 (Set.mem_iUnion.2 ⟨i, z, rfl⟩)
  have hcov' : ∀ y : A ⧸ pointsIdeal S →ₐ[k] k, ∃ i, ∃ z : TorusAffine k (a i) (b i) →ₐ[k] k,
      z.comp (liftOfPoints S (f i) (hf i)) = y := by
    intro y
    have hy : y.comp (Ideal.Quotient.mkₐ k (pointsIdeal S)) ∈ S := by
      refine (Set.ext_iff.1 hS _).1 fun c hc => ?_
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hc,
        map_zero]
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.1 ((Set.ext_iff.1 hcov _).2 hy)
    refine ⟨i, z, Ideal.Quotient.algHom_ext k ?_⟩
    rw [AlgHom.comp_assoc, liftOfPoints_comp_mkₐ]
    exact hz
  obtain ⟨h1, h2⟩ := exceptional_Lang_finite_parameter_tangent_dimension_bound a b
    (fun i => liftOfPoints S (f i) (hf i)) hcov' x
  have h3 : (Module.finrank k (TangentSpace k (A ⧸ pointsIdeal S) x) : Cardinal) ≤ (n : ℕ) :=
    h1.le.trans (h2.trans (Nat.cast_le.2 (Finset.sup_le fun i _ => hn i)))
  exact_mod_cast h3

end Cover

section Count

theorem le_six_of_injective_posRoot
    {n : ℕ} (f : Fin n → Fin Tag.G2.rank → ℤ)
    (hf : Function.Injective f) (hr : ∀ j, IsRoot Tag.G2 (f j) ∧ 0 < height (f j)) : n ≤ 6 :=
  calc n = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    _ ≤ ((rootFinset Tag.G2).filter fun v => 0 < height v).card :=
        Finset.card_le_card fun v hv => by
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
          exact Finset.mem_filter.2 ⟨mem_rootFinset.2 (hr j).1, (hr j).2⟩
    _ = 6 := by decide

theorem rank_add_bruhatParam_le_G2
    {N : ℕ} {α : Fin N → Fin Tag.G2.rank → ℤ}
    (hα : Function.Injective α) (hαr : Set.range α = {β | IsRoot Tag.G2 β ∧ 0 < height β})
    {m : ℕ} {β : Fin m → Fin Tag.G2.rank → ℤ} (hβ : Function.Injective β) {w : WeylGroup Tag.G2}
    (hβr : Set.range β = inversionSet w) : Tag.G2.rank + (N + m) ≤ 14 := by
  have hN : N ≤ 6 := le_six_of_injective_posRoot α hα fun j => by
    have h : α j ∈ Set.range α := Set.mem_range_self j
    rw [hαr] at h
    exact h
  have hm : m ≤ 6 := le_six_of_injective_posRoot β hβ fun j => by
    have h : β j ∈ Set.range β := Set.mem_range_self j
    rw [hβr] at h
    exact ⟨h.1, h.2.1⟩
  have h2 : Tag.G2.rank = 2 := rfl
  omega

end Count

section Bound

variable {L : Type} [Field L] [IsAlgClosed L]

theorem finrank_tangentSpace_realizedCoord_G2_le
    (x : realizedCoord Tag.G2 L →ₐ[L] L) :
    Module.finrank L (TangentSpace L (realizedCoord Tag.G2 L) x) ≤ 14 := by
  have hreal := isConnectedAlgebraicSubgroup_adjointPointSubgroup Tag.G2 L
  have := hreal.finiteType
  obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots Tag.G2)
  choose m β hβ hβr using fun w : WeylGroup Tag.G2 => exists_enum (inversionSet_finite w)
  obtain ⟨-, -, hcov, -, -, -⟩ := exceptional_Lang_rootword_Bruhat_regular_cover Tag.G2 L
  refine finrank_tangentSpace_quotient_le (subgroupPoints (adjointPointSubgroup Tag.G2 L))
    hreal.pointsZero_eq (fun _ => Tag.G2.rank) (fun w => N + m w)
    (fun w => bruhatCo Tag.G2 L w α (β w)) ?_
    (fun w => rank_add_bruhatParam_le_G2 hα hαr (hβ w) (hβr w)) x
  rw [hcov α hα hαr m β hβ hβr, subgroupPoints_map, transportPoints_modGLPoint]
  rfl

theorem finrank_tangentSpace_g2GraphCoord_le
    {Φ : MulAut (adjointGroup Tag.G2 L)}
    (hΦ : IsG2Exceptional L Φ) (x : g2GraphCoord L Φ →ₐ[L] L) :
    Module.finrank L (TangentSpace L (g2GraphCoord L Φ) x) ≤ 14 := by
  have hreal := g2Graph_realization hΦ
  have := hreal.2.1.finiteType
  have := hreal.2.1.isDomain
  have := hreal.2.2.1
  obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots Tag.G2)
  choose m β hβ hβr using fun w : WeylGroup Tag.G2 => exists_enum (inversionSet_finite w)
  obtain ⟨-, -, -, hgraph, -, -⟩ := exceptional_Lang_rootword_Bruhat_regular_cover Tag.G2 L
  obtain ⟨ν, -, hcov, -, -⟩ := hgraph 14 (g2GraphHom Φ) (g2GraphHom_regular_x hΦ)
    (g2GraphHom_regular_y hΦ)
  refine finrank_tangentSpace_quotient_le (subgroupPoints (graphPointSubgroup (g2GraphHom Φ)))
    hreal.2.1.pointsZero_eq (fun _ => Tag.G2.rank) (fun w => N + m w)
    (fun w => Algebra.TensorProduct.productMap (bruhatCo Tag.G2 L w α (β w)) (ν w α (β w))) ?_
    (fun w => rank_add_bruhatParam_le_G2 hα hαr (hβ w) (hβr w)) x
  rw [hcov α hα hαr m β hβ hβr, subgroupPoints_map, transportPoints_graphSubgroup]
  rfl

end Bound

end CFSG.LieType.AlgebraicGroups
