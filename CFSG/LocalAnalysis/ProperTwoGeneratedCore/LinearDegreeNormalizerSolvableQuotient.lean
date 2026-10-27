module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerOrder168
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetAction

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

universe u

variable {G : Type u} [Group G]

local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

private theorem translation_one_mul_inversion_ne_zmod_seven :
    translation (ZMod 7) 1 * inversion (ZMod 7) ≠
      inversion (ZMod 7) * translation (ZMod 7) 1 := by
  intro h
  have := congrArg (fun σ : Equiv.Perm (Omega (ZMod 7)) => σ none) h
  simp only [Equiv.Perm.mul_apply, inversion_none, translation_some, translation_none] at this
  exact absurd (Option.some_inj.mp this) (by decide)

theorem cosetNormalizer_quotient_equiv_psl_seven {Δ : Set G} {E : Subgroup G}
    (hE : Subgroup.centralizer Δ = E) (b : Δ ≃ Omega (ZMod 7))
    (hb : (fun σ : Equiv.Perm Δ => b.permCongr σ) '' ((cosetNormalizerPerm Δ).range :
      Set (Equiv.Perm Δ)) = (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7))))) :
    ∃ _ : (E.subgroupOf (Subgroup.normalizer Δ)).Normal,
      Nonempty (Subgroup.normalizer Δ ⧸ E.subgroupOf (Subgroup.normalizer Δ) ≃*
        CFSG.GorensteinWalter.PSL2 (ZMod 7)) := by
  have hker : (cosetNormalizerPerm Δ).ker = E.subgroupOf (Subgroup.normalizer Δ) := by
    rw [cosetNormalizerPerm_ker_eq_entire_centralizer, hE]
  have hmap : (cosetNormalizerPerm Δ).range.map b.permCongrHom.toMonoidHom =
      coordinateG (ZMod 7) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map]
    exact hb
  have hnormal : (E.subgroupOf (Subgroup.normalizer Δ)).Normal :=
    hker ▸ (cosetNormalizerPerm Δ).normal_ker
  refine ⟨hnormal, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange _)).trans
    ((((cosetNormalizerPerm Δ).range.equivMapOfInjective _ b.permCongrHom.injective).trans
      (MulEquiv.subgroupCongr hmap)).trans (pslEquivCoordinateG (ZMod 7)).symm)

theorem cosetNormalizer_quotient_simple_of_projective_seven {Δ : Set G} {E : Subgroup G}
    (hE : Subgroup.centralizer Δ = E) (b : Δ ≃ Omega (ZMod 7))
    (hb : (fun σ : Equiv.Perm Δ => b.permCongr σ) '' ((cosetNormalizerPerm Δ).range :
      Set (Equiv.Perm Δ)) = (coordinateG (ZMod 7) : Set (Equiv.Perm (Omega (ZMod 7))))) :
    ∃ _ : (E.subgroupOf (Subgroup.normalizer Δ)).Normal,
      IsSimpleGroup (Subgroup.normalizer Δ ⧸ E.subgroupOf (Subgroup.normalizer Δ)) ∧
      (∃ x y : Subgroup.normalizer Δ ⧸ E.subgroupOf (Subgroup.normalizer Δ), x * y ≠ y * x) ∧
      Nat.card (Subgroup.normalizer Δ ⧸ E.subgroupOf (Subgroup.normalizer Δ)) = 168 := by
  obtain ⟨hnormal, ⟨e⟩⟩ := cosetNormalizer_quotient_equiv_psl_seven hE b hb
  refine ⟨hnormal, ?_, ?_, ?_⟩
  · have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 (ZMod 7)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; norm_num)
    exact e.isSimpleGroup
  · let e' := e.trans (pslEquivCoordinateG (ZMod 7))
    let x : coordinateG (ZMod 7) := ⟨translation (ZMod 7) 1,
      Subgroup.subset_closure (Set.mem_union_left _ ⟨1, rfl⟩)⟩
    let y : coordinateG (ZMod 7) := ⟨inversion (ZMod 7),
      Subgroup.subset_closure (Set.mem_union_right _ rfl)⟩
    refine ⟨e'.symm x, e'.symm y, fun hxy => translation_one_mul_inversion_ne_zmod_seven ?_⟩
    have := congrArg (fun a => ((e' a : coordinateG (ZMod 7)) :
      Equiv.Perm (Omega (ZMod 7)))) hxy
    simpa only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] using this
  · rw [Nat.card_congr (e.trans (pslEquivCoordinateG (ZMod 7))).toEquiv]
    exact CFSG.ProperTwoGeneratedCore.CosetNormalizer.card_coordinateG_zmod_seven

end CFSG.ProperTwoGeneratedCore.HighRankPair
