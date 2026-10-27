module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSimilarity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u v

variable {K : Type u} [Field K]

@[expose] def selfAdjointSymplecticCover (h2 : (2 : K) ≠ 0) :
    (symplecticMultiplier (K := K)).ker →* selfAdjointSymplecticImage h2 :=
  (selfAdjointSymplecticAction h2).rangeRestrict

theorem selfAdjointSymplecticCover_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (selfAdjointSymplecticCover h2) :=
  (selfAdjointSymplecticAction h2).rangeRestrict_surjective

theorem selfAdjointSymplecticCover_kernel_central (h2 : (2 : K) ≠ 0) :
    (selfAdjointSymplecticCover h2).ker ≤
      Subgroup.center (symplecticMultiplier (K := K)).ker := by
  intro A hA
  apply selfAdjointSymplecticAction_kernel_le_center h2
  change selfAdjointSymplecticAction h2 A = 1
  exact congrArg Subtype.val (show selfAdjointSymplecticCover h2 A = 1 from hA)

variable [Finite K]

instance selfAdjointSymplecticImageFinite (h2 : (2 : K) ≠ 0) :
    Finite (selfAdjointSymplecticImage h2) :=
  Finite.of_surjective (selfAdjointSymplecticCover h2)
    (selfAdjointSymplecticCover_surjective h2)

theorem symplecticKernel_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (p : ℕ) (L : Subgroup (symplecticMultiplier (K := K)).ker)
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have hG := symplecticKernel_quasisimple hodd
  have htop := CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hG p L hL
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      (CatalogueBAlternating.quasisimple_iff_native.mp hG))

theorem selfAdjointSymplecticImage_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (selfAdjointSymplecticImage
      (CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let f := selfAdjointSymplecticCover h2
  obtain ⟨J, hJ, hmap, _⟩ := CatalogueBCentralQuotient.pComponent_exists_lift p f
    (selfAdjointSymplecticCover_surjective h2)
    (selfAdjointSymplecticCover_kernel_central h2) L hL
  have hquasi := (CatalogueBCentralQuotient.pComponent_quasisimple_iff f
    (selfAdjointSymplecticCover_kernel_central h2) p J hJ).mp
      (symplecticKernel_pComponent_quasisimple hodd p J hJ)
  exact hmap ▸ hquasi

theorem selfAdjoint_orthogonal_finite (h2 : (2 : K) ≠ 0) :
    Finite (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) := by
  let : Finite (symplecticSimilitudes K) :=
    Finite.of_injective (fun A : symplecticSimilitudes K => A.val.val)
      (Units.val_injective.comp Subtype.val_injective)
  let : Finite Kˣ := Finite.of_injective Units.val Units.val_injective
  exact Finite.of_surjective (selfAdjointFullAction h2) (selfAdjointFullAction_surjective h2)

theorem selfAdjoint_pComponent_quasisimple (hodd : Odd (Nat.card K))
    (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  let : Finite (TauCeti.QuadraticMap.orthogonalGroup (selfAdjointForm K)) :=
    selfAdjoint_orthogonal_finite h2
  exact CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient
    p (selfAdjointSymplecticImage h2)
    (fun J hJ => selfAdjointSymplecticImage_pComponent_quasisimple hodd p J hJ) L hL

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem orthogonal_five_actual_p_component_verification (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5) (p : ℕ) [Fact p.Prime]
    (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  obtain ⟨_, _, e, _, _, _⟩ := finite_odd_five_selfAdjoint_form_similarity hodd Q hQ hdim
  have hmap := CatalogueBAlternating.pComponent_map_equiv p e L hL
  have hquasi := selfAdjoint_pComponent_quasisimple hodd p (L.map e.toMonoidHom) hmap
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (L.equivMapOfInjective e.toMonoidHom e.injective)
      (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
