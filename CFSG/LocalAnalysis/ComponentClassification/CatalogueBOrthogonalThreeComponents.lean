module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalThreeSimilarityGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroProjective

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap CatalogueBLinearTwo CatalogueBOrthogonalThreeSimilarity
open CFSG.GorensteinWalter

universe u v

variable {K : Type u} [Field K]

@[expose] def traceZeroProjectiveProjection :
    ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K →* ProjGenLinGroup (Fin 2) K :=
  MonoidHom.fst _ _

theorem traceZeroProjectiveProjection_kernel_central :
    (traceZeroProjectiveProjection (K := K)).ker ≤
      Subgroup.center (ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K) := by
  rintro ⟨g, ε⟩ h
  have hg : g = 1 := h
  subst g
  apply Subgroup.mem_center_iff.mpr
  rintro ⟨a, δ⟩
  apply Prod.ext
  · exact mul_one a |>.trans (one_mul a).symm
  · exact mul_comm δ ε

theorem traceZeroProjectiveProjection_surjective :
    Function.Surjective (traceZeroProjectiveProjection (K := K)) :=
  fun g => ⟨(g, 1), rfl⟩

variable [Finite K]

theorem traceZero_product_finite :
    Finite (ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K) := by
  let : Finite (GL (Fin 2) K) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let : Finite Kˣ := Finite.of_injective Units.val Units.val_injective
  infer_instance

theorem traceZero_product_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Finite (ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K) := traceZero_product_finite
  let : Finite (ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective traceZeroProjectiveProjection traceZeroProjectiveProjection_surjective
  have hmap := CatalogueBCentralQuotient.pComponent_map p
    traceZeroProjectiveProjection traceZeroProjectiveProjection_surjective
    traceZeroProjectiveProjection_kernel_central L hL
  have hquasi := (pgl_pComponent_classification K hodd p
    (L.map traceZeroProjectiveProjection) hmap).2.2
  exact (CatalogueBCentralQuotient.pComponent_quasisimple_iff
    traceZeroProjectiveProjection traceZeroProjectiveProjection_kernel_central p L hL).mpr hquasi

theorem traceZero_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let e := traceZeroProjectiveEquiv (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)
  let J := L.map e.symm.toMonoidHom
  have hJ := CatalogueBAlternating.pComponent_map_equiv p e.symm L hL
  have hquasi := traceZero_product_pComponent_quasisimple hodd p J hJ
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      (L.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem traceZero_product_three_solvable (hcard : Nat.card K = 3) :
    Group.IsSolvable (ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K) := by
  let : Group.IsSolvable (ProjGenLinGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveGeneralLinear_two_small_solvable K (Or.inr hcard)
  infer_instance

theorem traceZero_three_solvable (hcard : Nat.card K = 3) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) := by
  have hodd : Odd (Nat.card K) := hcard ▸ (by decide : Odd 3)
  let : Group.IsSolvable (ProjGenLinGroup (Fin 2) K × rootsOfUnity 2 K) :=
    traceZero_product_three_solvable hcard
  exact Group.isSolvable_of_surjective
    (f := (traceZeroProjectiveEquiv (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).toMonoidHom)
    (traceZeroProjectiveEquiv (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)).surjective

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_three_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  obtain ⟨_, _, e, _, _, _⟩ :=
    exists_trace_zero_similarity_and_orthogonal_equiv hodd Q hQ hdim
  have hmap := CatalogueBAlternating.pComponent_map_equiv p e L hL
  have hquasi := traceZero_pComponent_quasisimple hodd p (L.map e.toMonoidHom) hmap
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (L.equivMapOfInjective e.toMonoidHom e.injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem orthogonal_three_solvable (hcard : Nat.card K = 3)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hodd : Odd (Nat.card K) := hcard ▸ (by decide : Odd 3)
  obtain ⟨_, _, e, _, _, _⟩ :=
    exists_trace_zero_similarity_and_orthogonal_equiv hodd Q hQ hdim
  let : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) :=
    traceZero_three_solvable hcard
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem orthogonal_three_actual_p_component_verification (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 3) :
    (∀ (p : ℕ) [Fact p.Prime] (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (Nat.card K = 3 → Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      ∀ (p : ℕ) [Fact p.Prime] (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
        ¬ CFSG.IsPComponent p L) := by
  refine ⟨fun p _ L hL => orthogonal_three_pComponent_quasisimple hodd Q hQ hdim p L hL, ?_⟩
  intro hcard
  let : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    orthogonal_three_solvable hcard Q hQ hdim
  exact ⟨inferInstance, fun p _ L => CatalogueBGeneralLinear.no_pComponent_of_solvable p L⟩

end CFSG.ComponentClassification.CatalogueBOrthogonal
