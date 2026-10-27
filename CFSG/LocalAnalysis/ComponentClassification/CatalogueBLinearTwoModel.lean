module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoModelMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoNormalizer

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoModel

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

theorem generalizedFitting_semilinear_model_of_equiv {G K : Type*}
    [Group G] [Finite G] [Field K] [Finite K]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (theta : GeneralizedFitting.subgroup G ≃* coordinateG K) :
    ∃ rho : G →* coordinateE K, Function.Injective rho ∧
      (∀ f : GeneralizedFitting.subgroup G, (rho f.val).val = (theta f).val) ∧
      (GeneralizedFitting.subgroup G).map rho = (coordinateG K).subgroupOf (coordinateE K) ∧
      ((coordinateG K).subgroupOf (coordinateE K)).relIndex rho.range =
        (GeneralizedFitting.subgroup G).index := by
  let F := GeneralizedFitting.subgroup G
  let : F.Normal := GeneralizedFitting.normal G
  let a : G →* MulAut F := MulAut.conjNormal
  have ha : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff a).mp
    apply le_bot_iff.mp
    intro g hg
    have hcentral : g ∈ Subgroup.centralizer (F : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro f hf
      have heq := congrArg (fun automorphism : MulAut F =>
        (automorphism (⟨f, hf⟩ : F)).val) hg
      change g * f * g⁻¹ = f at heq
      have hcomm := congrArg (fun x : G => x * g) heq
      have hgf : g * f = f * g := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hcomm
      exact hgf.symm
    rw [CatalogueBAlternating.generalizedFitting_centralizer_eq_bot G hnonab] at hcentral
    exact hcentral
  let c := coordinateConjugationEquiv K
  let rho : G →* coordinateE K :=
    c.symm.toMonoidHom.comp ((MulAut.congr theta).toMonoidHom.comp a)
  have hrho : Function.Injective rho := c.symm.injective.comp
    ((MulAut.congr theta).injective.comp ha)
  have hextends : ∀ f : F, (rho f.val).val = (theta f).val := by
    intro f
    have hinner : (MulAut.congr theta) (a f.val) = MulAut.conj (theta f) := by
      apply MulEquiv.ext
      intro x
      change theta ((a f.val) (theta.symm x)) =
        theta f * x * (theta f)⁻¹
      rw [MulAut.conjNormal_val, MulAut.conj_apply]
      simp only [map_mul, map_inv, theta.apply_symm_apply]
    have heq : rho f.val =
        (⟨theta f, ((coordinateG_le_D K).trans (coordinateD_le_E K))
          (theta f).property⟩ : coordinateE K) := by
      apply c.injective
      change c (c.symm ((MulAut.congr theta) (a f.val))) = _
      rw [c.apply_symm_apply, hinner]
      exact (coordinateConjugation_on_G K (theta f)).symm
    exact congrArg Subtype.val heq
  have hmap : F.map rho = (coordinateG K).subgroupOf (coordinateE K) := by
    apply le_antisymm
    · rintro g ⟨f, hf, rfl⟩
      change (rho f).val ∈ coordinateG K
      rw [hextends (⟨f, hf⟩ : F)]
      exact (theta (⟨f, hf⟩ : F)).property
    · intro g hg
      let f := theta.symm (⟨g.val, hg⟩ : coordinateG K)
      refine ⟨f.val, f.property, ?_⟩
      apply Subtype.ext
      rw [hextends f]
      exact congrArg Subtype.val (theta.apply_symm_apply _)
  have hindex : ((coordinateG K).subgroupOf (coordinateE K)).relIndex rho.range =
      F.index := by
    rw [← hmap]
    have h := Subgroup.relIndex_map_map_of_injective (f := rho) F ⊤ hrho
    simpa only [Subgroup.map_top, Subgroup.relIndex_top_right] using h
  exact ⟨rho, hrho, hextends, hmap, hindex⟩

theorem generalizedFitting_semilinear_model {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (p f : ℕ) [Fact p.Prime]
    (hmodel : Assembly.ComponentType.ClassicalModel (GeneralizedFitting.subgroup G)
      .PSL 2 p f) :
    ∃ rho : G →* coordinateE (GaloisField p f),
      Nat.card (GaloisField p f) = p ^ f ∧ Function.Injective rho ∧
      (GeneralizedFitting.subgroup G).map rho =
        (coordinateG (GaloisField p f)).subgroupOf (coordinateE (GaloisField p f)) ∧
      ((coordinateG (GaloisField p f)).subgroupOf (coordinateE (GaloisField p f))).relIndex
        rho.range = (GeneralizedFitting.subgroup G).index := by
  obtain ⟨hadmissible, ⟨theta⟩⟩ := hmodel
  have hf : f ≠ 0 := by
    have hpositive : 1 ≤ f := hadmissible.2.1
    omega
  let : Finite (GaloisField p f) := Nat.finite_of_card_ne_zero (by
    rw [GaloisField.card p f hf]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨rho, hrho, _hextends, hmap, hindex⟩ :=
    generalizedFitting_semilinear_model_of_equiv hnonab
      (theta.trans (pslModelEquivCoordinateG p f))
  exact ⟨rho, GaloisField.card p f hf, hrho, hmap, hindex⟩

end

end CFSG.ComponentClassification.CatalogueBLinearTwoModel
