module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E1Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E1

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem not_isPGroup_quadratic_field
    (hK : ringChar K ≠ 2) {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) :
    ¬ IsPGroup 2 (↥(fixedSubgroup α) ⧸ pPrimeCore 2 ↥(fixedSubgroup α)) := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (fixedSubgroup β).map (adjointGroup τ K).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ K) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(fixedSubgroup β) ≃* ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  have : Finite (ModGL τ K) := finite_modGL
  refine not_isPGroup_of_mulEquiv (e₁.trans e₂) ?_
  obtain ⟨-, -, -, hJΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K δ
  have hk2 := ringChar_fixSubfield_ne_two hK δ
  have hr : 0 < τ.rank := by cases τ <;> decide
  set β₀ : Fin τ.rank → ℤ := Pi.single ⟨0, hr⟩ 1 with hβ₀
  have hβ₀r : IsRoot τ β₀ := .basis _
  refine not_isPGroup_of_sl2 hk2
    ((baseChangeGL (fixSubfield δ).subtype).comp (rootSL2 τ (fixSubfield δ) β₀))
    ((baseChangeGL_injective _).comp (ExcSelector.rootSL2_injective_of_ne_two hk2 β₀)) ?_
  refine le_trans ?_ hJΓ
  rw [MonoidHom.range_comp, fixedFieldImage, ExcSelector.range_rootSL2_eq hβ₀r]
  exact map_mono (sup_le (rootSubgroup_le_adjointGroup β₀) (rootSubgroup_le_adjointGroup (-β₀)))

theorem not_isPGroup_small_ree
    [CharP K ReeTag.G2.prime] {b : ℕ} (hK : Nat.card K = 3 ^ (2 * b + 1))
    (g : adjointGroup ReeTag.G2.tag K)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1) :
    ¬ IsPGroup 2 (↥(fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) ⧸
      pPrimeCore 2 ↥(fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b))) := by
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
    CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b K hK g hα
  set α := MulAut.conj g * ReeTag.G2.finiteReeAut K b
  have hc : MulAut.congr ψ α = ψ * α * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hfix := ExcSelector.fixedSubgroup_congr ψ α
  rw [hc, hψ] at hfix
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hmap : (fixedSubgroup α).map ((adjointGroup ReeTag.G2.tag K).subtype.comp ψ.toMonoidHom) =
      ReeTag.G2.reeGamma K b := by
    rw [← Subgroup.map_map, ← hfix]
    rfl
  refine not_isPGroup_of_map ((adjointGroup ReeTag.G2.tag K).subtype.comp ψ.toMonoidHom)
    (Subtype.val_injective.comp ψ.injective) ?_
  rw [hmap]
  set Γ := ReeTag.G2.reeGamma K b with hΓ
  obtain ⟨hDs, hnab, -⟩ := CatalogueBSmallRee.small_Ree_whole_group_p_components b K hK
  set D := commutator Γ
  set J := D.map Γ.subtype with hJ
  have eJ : D ≃* J := D.equivMapOfInjective _ Subtype.val_injective
  have : IsSimpleGroup J := (MulEquiv.isSimpleGroup_congr eJ).1 hDs
  have hJF : J ≤ Γ := Subgroup.map_subtype_le D
  have hnabJ : ∃ x y : J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨eJ x, eJ y, fun h => hxy (eJ.injective (by rw [map_mul, map_mul, h]))⟩
  exact not_isPGroup_of_isSimpleGroup hJF hnabJ

end CFSG.ComponentClassification.HarrisLit.L33.E1
