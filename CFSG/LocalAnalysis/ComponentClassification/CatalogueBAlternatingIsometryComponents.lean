module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryTwo

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBAlternatingIsometry

open LinearMap (BilinForm)

theorem pComponent_eq_top_of_quasisimple {G : Type*} [Group G]
    (hG : CFSG.IsQuasisimple G) (p : ℕ) (L : Subgroup G)
    (hL : CFSG.IsPComponent p L) : L = ⊤ := by
  let : Group.IsPerfect L := CatalogueBAlternating.pComponent_perfect hL
  let : Nontrivial L := CatalogueBAlternating.pComponent_nontrivial hL
  exact (Quasisimple.perfect_subnormal_eq_bot_or_eq_top
    (CatalogueBAlternating.quasisimple_iff_native.mp hG) L
    (Components.chain_of_mathlib_subnormal hL.choose_spec.2.1)).resolve_left
      (L.nontrivial_iff_ne_bot.mp inferInstance)

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

instance isometryGroupFinite (B : BilinForm K V) : Finite (isometryGroup B) :=
  Finite.of_injective
    (fun g : isometryGroup B => basisMatrixEquiv (Module.finBasis K V) g.val)
    ((basisMatrixEquiv (Module.finBasis K V)).injective.comp Subtype.val_injective)

theorem plane_quasisimple (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : Module.finrank K V = 2) (hodd : Odd (Nat.card K)) (hne3 : Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (isometryGroup B) := by
  have hne2 : Nat.card K ≠ 2 := by
    intro h2
    rw [h2] at hodd
    norm_num at hodd
  obtain ⟨e⟩ := exists_planeIsometryEquivSL B hB hnd hd
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv e
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K (by omega)
          (Or.inr hne2) (Or.inr hne3))))

theorem isometry_quasisimple_of_four_le (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hdim : 4 ≤ Module.finrank K V) (hodd : Odd (Nat.card K)) :
    CFSG.IsQuasisimple (isometryGroup B) := by
  obtain ⟨m, hd, ⟨e⟩⟩ := exists_isometryEquiv_symplectic B hB hnd
  have hm : 2 ≤ m := by omega
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv e
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (symplectic_quasisimple K m (by omega) hodd (Or.inl (by omega)))))

theorem isometry_quasisimple (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : 2 ≤ Module.finrank K V) (hodd : Odd (Nat.card K))
    (hexception : Module.finrank K V ≠ 2 ∨ Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (isometryGroup B) := by
  by_cases hd2 : Module.finrank K V = 2
  · exact plane_quasisimple B hB hnd hd2 hodd (hexception.resolve_left (not_not.mpr hd2))
  · obtain ⟨m, hd, _⟩ := exists_symplectic_basis B hB hnd
    exact isometry_quasisimple_of_four_le B hB hnd (by omega) hodd

theorem isometry_pComponent_eq_top (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hdim : 2 ≤ Module.finrank K V) (hodd : Odd (Nat.card K))
    (hexception : Module.finrank K V ≠ 2 ∨ Nat.card K ≠ 3)
    (p : ℕ) (L : Subgroup (isometryGroup B)) (hL : CFSG.IsPComponent p L) : L = ⊤ :=
  pComponent_eq_top_of_quasisimple (isometry_quasisimple B hB hnd hdim hodd hexception) p L hL

theorem isometry_pComponent_quasisimple (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hdim : 2 ≤ Module.finrank K V) (hodd : Odd (Nat.card K))
    (p : ℕ) (L : Subgroup (isometryGroup B)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  by_cases hexception : Module.finrank K V = 2 ∧ Nat.card K = 3
  · exact (plane_fieldThree_no_pComponent B hB hnd hexception.1 hexception.2 p L hL).elim
  · have hretained : Module.finrank K V ≠ 2 ∨ Nat.card K ≠ 3 := not_and_or.mp hexception
    have hG := isometry_quasisimple B hB hnd hdim hodd hretained
    have htop := pComponent_eq_top_of_quasisimple hG p L hL
    exact CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv
        ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
        (CatalogueBAlternating.quasisimple_iff_native.mp hG))

theorem odd_symplectic_isometry_p_components (B : BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hdim : 4 ≤ Module.finrank K V) (hodd : Odd (Nat.card K)) :
    CFSG.IsQuasisimple (isometryGroup B) ∧
      ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup B), CFSG.IsPComponent p L →
        L = ⊤ ∧ CFSG.IsQuasisimple L := by
  have hG := isometry_quasisimple_of_four_le B hB hnd hdim hodd
  refine ⟨hG, fun p _ L hL => ?_⟩
  exact ⟨pComponent_eq_top_of_quasisimple hG p L hL,
    isometry_pComponent_quasisimple B hB hnd (by omega) hodd p L hL⟩

theorem odd_symplectic_all_dimensional_isometry_p_components
    (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : 2 ≤ Module.finrank K V) (hodd : Odd (Nat.card K)) :
    (∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup B), CFSG.IsPComponent p L →
      CFSG.IsQuasisimple L) ∧
    ((Module.finrank K V = 2 ∧ Nat.card K = 3) →
      Group.IsSolvable (isometryGroup B) ∧
        ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup B), ¬ CFSG.IsPComponent p L) ∧
    ((Module.finrank K V ≠ 2 ∨ Nat.card K ≠ 3) →
      CFSG.IsQuasisimple (isometryGroup B) ∧
        ∀ (p : ℕ), p.Prime → ∀ L : Subgroup (isometryGroup B), CFSG.IsPComponent p L → L = ⊤) := by
  refine ⟨fun p _ L hL => isometry_pComponent_quasisimple B hB hnd hdim hodd p L hL,
    fun hsmall => ?_, fun hretained => ?_⟩
  · exact ⟨plane_fieldThree_solvable B hB hnd hsmall.1 hsmall.2,
      fun p _ L => plane_fieldThree_no_pComponent B hB hnd hsmall.1 hsmall.2 p L⟩
  · exact ⟨isometry_quasisimple B hB hnd hdim hodd hretained,
      fun p _ L hL => isometry_pComponent_eq_top B hB hnd hdim hodd hretained p L hL⟩

end CFSG.ComponentClassification.CatalogueBAlternatingIsometry
