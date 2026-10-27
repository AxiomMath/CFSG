module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitSimilarity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitComponentsProduct
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitKernel

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalNonsplitFourComponents

open Matrix CatalogueBOrthogonalFourNonsplit

universe u v

variable {K : Type u} [Field K] [Finite K] (delta : K)

instance nonsplitFourExtensionFinite : Finite (extension delta) :=
  Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd delta 0).symm

instance hermitianIsometriesFinite : Finite (HermitianIsometries delta) := by
  apply Finite.of_injective
    (fun g : HermitianIsometries delta =>
      (g.val : hermitianSubmodule delta → hermitianSubmodule delta))
  intro g h heq
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact congrFun heq X

variable [Fact (¬ IsSquare delta)]

@[expose] def specialLinearCover (h2 : (2 : K) ≠ 0) :
    SpecialLinearGroup (Fin 2) (extension delta) →* specialImage delta h2 :=
  (specialRho delta h2).rangeRestrict

omit [Finite K] [Fact (¬ IsSquare delta)] in
theorem specialLinearCover_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (specialLinearCover delta h2) :=
  (specialRho delta h2).rangeRestrict_surjective

omit [Finite K] in
theorem specialLinearCover_kernel_central (h2 : (2 : K) ≠ 0) :
    (specialLinearCover delta h2).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin 2) (extension delta)) := by
  intro g hg
  apply specialRho_kernel_le_center delta h2
  exact congrArg Subtype.val (show specialLinearCover delta h2 g = 1 from hg)

theorem specialImage_pComponent_quasisimple (h2 : (2 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (specialImage delta h2))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let f := specialLinearCover delta h2
  obtain ⟨J, hJ, hmap, _⟩ := CatalogueBCentralQuotient.pComponent_exists_lift p f
    (specialLinearCover_surjective delta h2) (specialLinearCover_kernel_central delta h2) L hL
  have hquasi := (CatalogueBCentralQuotient.pComponent_quasisimple_iff f
    (specialLinearCover_kernel_central delta h2) p J hJ).mp
      (CatalogueBOrthogonalFourSplitComponents.specialLinearTwo_pComponent_quasisimple p J hJ)
  exact hmap ▸ hquasi

theorem hermitian_pComponent_quasisimple (h2 : (2 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (HermitianIsometries delta))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L :=
  CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient
    p (specialImage delta h2) (specialImage_pComponent_quasisimple delta h2 p) L hL

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_four_nonsplit_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  obtain ⟨delta, hns, _, _, e, _, _, _⟩ :=
    exists_hermitian_similarity_and_orthogonal_equiv hodd Q hQ hdim hno
  let : Fact (¬ IsSquare (delta : K)) := ⟨hns⟩
  have hmap := CatalogueBAlternating.pComponent_map_equiv p e L hL
  have hquasi := hermitian_pComponent_quasisimple (delta : K)
    (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd) p (L.map e.toMonoidHom) hmap
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (L.equivMapOfInjective e.toMonoidHom e.injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

theorem orthogonal_four_nonsplit_actual_p_component_verification (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 4)
    (hno : ¬ ∃ S : Submodule K V, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  let : Fact p.Prime := ⟨hp⟩
  exact orthogonal_four_nonsplit_pComponent_quasisimple hodd Q hQ hdim hno p L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalNonsplitFourComponents
