module

public import CFSG.LinearAlgebra.RootGroupSL.ModelBasic
public import CFSG.LinearAlgebra.RootGroupSL.CocycleNat

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k] [CharP k 2]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma modelA1Elt_zero :
    modelA1Elt (0 : V₀ →ₗ[k] VJ) = (1 : SpecialLinearGroup k (VJ × V₀)) := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  simp [modelA1Elt_apply]

private lemma modelA2Elt_zero :
    modelA2Elt (0 : VJ →ₗ[k] V₀) = (1 : SpecialLinearGroup k (VJ × V₀)) := by
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  simp [modelA2Elt_apply]

private lemma exists_blockSLk (g : ↥(modelK1 k VJ V₀)) :
    ∃ B : SpecialLinearGroup k VJ,
      blockSLk k V₀ B = (g : SpecialLinearGroup k (VJ × V₀)) := by
  have hg : (g : SpecialLinearGroup k (VJ × V₀)) ∈
      (blockSLk (VJ := VJ) k V₀).range := by
    rw [← modelK1_eq_range]
    exact g.2
  exact hg

theorem modelA1_h1 (hVJ : 4 ≤ Module.finrank k VJ)
    (δ : ↥(modelK1 k VJ V₀) → ↥(modelA1 k VJ V₀))
    (hδ : ∀ g h : ↥(modelK1 k VJ V₀),
      ((δ (g * h) : ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (δ g : SpecialLinearGroup k (VJ × V₀)) *
          ((g : SpecialLinearGroup k (VJ × V₀)) * (δ h : SpecialLinearGroup k (VJ × V₀)) *
            (g : SpecialLinearGroup k (VJ × V₀))⁻¹)) :
    ∃ a : ↥(modelA1 k VJ V₀), ∀ g : ↥(modelK1 k VJ V₀),
      (δ g : SpecialLinearGroup k (VJ × V₀)) =
        (a : SpecialLinearGroup k (VJ × V₀)) *
          ((g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀))⁻¹ *
            (g : SpecialLinearGroup k (VJ × V₀))⁻¹) := by
  classical
  let b := Module.finBasis k V₀
  let blockK : SpecialLinearGroup k VJ →* ↥(modelK1 k VJ V₀) :=
    { toFun := fun B => ⟨blockSLk k V₀ B, by
        rw [modelK1_eq_range]
        exact ⟨B, rfl⟩⟩
      map_one' := Subtype.ext (map_one (blockSLk k V₀))
      map_mul' := fun B B' => Subtype.ext (map_mul (blockSLk k V₀) B B') }
  have hδ' : ∀ B B' : SpecialLinearGroup k VJ,
      (δ (blockK (B * B')) : SpecialLinearGroup k (VJ × V₀)) =
        (δ (blockK B) : SpecialLinearGroup k (VJ × V₀)) *
          ((blockK B : SpecialLinearGroup k (VJ × V₀)) *
            (δ (blockK B') : SpecialLinearGroup k (VJ × V₀)) *
            (blockK B : SpecialLinearGroup k (VJ × V₀))⁻¹) := by
    intro B B'
    have h := hδ (blockK B) (blockK B')
    rw [← map_mul blockK B B'] at h
    exact h
  let φ : SpecialLinearGroup k VJ → (V₀ →ₗ[k] VJ) := fun B =>
    Classical.choose ((mem_modelA1_iff (δ (blockK B) :
      SpecialLinearGroup k (VJ × V₀))).1 (δ (blockK B)).2)
  have hφ : ∀ B, modelA1Elt (φ B) =
      (δ (blockK B) : SpecialLinearGroup k (VJ × V₀)) := fun B =>
    Classical.choose_spec ((mem_modelA1_iff (δ (blockK B) :
      SpecialLinearGroup k (VJ × V₀))).1 (δ (blockK B)).2)
  have hφc : ∀ B B' : SpecialLinearGroup k VJ,
      φ (B * B') =
        φ B + (SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ B' := by
    intro B B'
    apply modelA1Elt_injective
    rw [modelA1Elt_add, ← blockSLk_mul_modelA1Elt_mul_inv B (φ B'),
      hφ (B * B'), hφ B, hφ B']
    exact hδ' B B'
  let c : Fin (Module.finrank k V₀) → SpecialLinearGroup k VJ → VJ :=
    fun j B => φ B (b j)
  have hc : ∀ j (B B' : SpecialLinearGroup k VJ),
      c j (B * B') = c j B + B (c j B') := by
    intro j B B'
    change (φ (B * B')) (b j) = (φ B) (b j) + B ((φ B') (b j))
    rw [hφc B B']
    rfl
  have hex : ∀ j, ∃ a : VJ, ∀ B, c j B = B a - a :=
    fun j => exists_eq_sub_of_cocycle_natural hVJ (c j) (hc j)
  choose a ha using hex
  let φ₀ : V₀ →ₗ[k] VJ := b.constr k a
  have hφ₀ : ∀ j, φ₀ (b j) = a j := fun j => b.constr_basis k a j
  have hφ_eq : ∀ B : SpecialLinearGroup k VJ,
      φ B = (SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ₀ - φ₀ := by
    intro B
    apply b.ext
    intro j
    change c j B = (SpecialLinearGroup.toLinearEquiv B).toLinearMap (φ₀ (b j)) - φ₀ (b j)
    rw [ha j B, hφ₀ j]
    rfl
  have ha_inv : (modelA1Elt (-φ₀) : SpecialLinearGroup k (VJ × V₀))⁻¹ =
      modelA1Elt φ₀ := by
    have hmul : modelA1Elt (-φ₀) * modelA1Elt φ₀ = 1 := by
      rw [← modelA1Elt_add, neg_add_cancel, modelA1Elt_zero]
    exact inv_eq_of_mul_eq_one_right hmul
  let a₁ : ↥(modelA1 k VJ V₀) :=
    ⟨modelA1Elt (-φ₀), (mem_modelA1_iff _).2 ⟨-φ₀, rfl⟩⟩
  have ha₁_val : (a₁ : SpecialLinearGroup k (VJ × V₀)) = modelA1Elt (-φ₀) := rfl
  refine ⟨a₁, ?_⟩
  intro g
  obtain ⟨B, hB⟩ := exists_blockSLk g
  have hg : g = blockK B := Subtype.ext hB.symm
  have hδg : (δ g : SpecialLinearGroup k (VJ × V₀)) = modelA1Elt (φ B) := by
    rw [hg]
    exact (hφ B).symm
  have hprod : (a₁ : SpecialLinearGroup k (VJ × V₀)) *
      ((g : SpecialLinearGroup k (VJ × V₀)) *
        (a₁ : SpecialLinearGroup k (VJ × V₀))⁻¹ *
        (g : SpecialLinearGroup k (VJ × V₀))⁻¹) = modelA1Elt (φ B) := by
    rw [ha₁_val, ha_inv, hg]
    rw [show (blockK B : SpecialLinearGroup k (VJ × V₀)) = blockSLk k V₀ B from rfl]
    rw [blockSLk_mul_modelA1Elt_mul_inv]
    rw [← modelA1Elt_add]
    congr 1
    rw [hφ_eq B]
    abel
  exact hδg.trans hprod.symm

theorem modelA2_h1 (hVJ : 4 ≤ Module.finrank k VJ)
    (δ : ↥(modelK1 k VJ V₀) → ↥(modelA2 k VJ V₀))
    (hδ : ∀ g h : ↥(modelK1 k VJ V₀),
      ((δ (g * h) : ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (δ g : SpecialLinearGroup k (VJ × V₀)) *
          ((g : SpecialLinearGroup k (VJ × V₀)) * (δ h : SpecialLinearGroup k (VJ × V₀)) *
            (g : SpecialLinearGroup k (VJ × V₀))⁻¹)) :
    ∃ a : ↥(modelA2 k VJ V₀), ∀ g : ↥(modelK1 k VJ V₀),
      (δ g : SpecialLinearGroup k (VJ × V₀)) =
        (a : SpecialLinearGroup k (VJ × V₀)) *
          ((g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀))⁻¹ *
            (g : SpecialLinearGroup k (VJ × V₀))⁻¹) := by
  classical
  let b := Module.finBasis k V₀
  let blockK : SpecialLinearGroup k VJ →* ↥(modelK1 k VJ V₀) :=
    { toFun := fun B => ⟨blockSLk k V₀ B, by
        rw [modelK1_eq_range]
        exact ⟨B, rfl⟩⟩
      map_one' := Subtype.ext (map_one (blockSLk k V₀))
      map_mul' := fun B B' => Subtype.ext (map_mul (blockSLk k V₀) B B') }
  have hδ' : ∀ B B' : SpecialLinearGroup k VJ,
      (δ (blockK (B * B')) : SpecialLinearGroup k (VJ × V₀)) =
        (δ (blockK B) : SpecialLinearGroup k (VJ × V₀)) *
          ((blockK B : SpecialLinearGroup k (VJ × V₀)) *
            (δ (blockK B') : SpecialLinearGroup k (VJ × V₀)) *
            (blockK B : SpecialLinearGroup k (VJ × V₀))⁻¹) := by
    intro B B'
    have h := hδ (blockK B) (blockK B')
    rw [← map_mul blockK B B'] at h
    exact h
  let ψ : SpecialLinearGroup k VJ → (VJ →ₗ[k] V₀) := fun B =>
    Classical.choose ((mem_modelA2_iff (δ (blockK B) :
      SpecialLinearGroup k (VJ × V₀))).1 (δ (blockK B)).2)
  have hψ : ∀ B, modelA2Elt (ψ B) =
      (δ (blockK B) : SpecialLinearGroup k (VJ × V₀)) := fun B =>
    Classical.choose_spec ((mem_modelA2_iff (δ (blockK B) :
      SpecialLinearGroup k (VJ × V₀))).1 (δ (blockK B)).2)
  have hψc : ∀ B B' : SpecialLinearGroup k VJ,
      ψ (B * B') =
        ψ B + ψ B' ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap := by
    intro B B'
    apply modelA2Elt_injective
    rw [modelA2Elt_add, ← blockSLk_mul_modelA2Elt_mul_inv B (ψ B'),
      hψ (B * B'), hψ B, hψ B']
    exact hδ' B B'
  have coord_eq_of_eq : ∀ {f g : VJ →ₗ[k] V₀},
      (∀ i, b.coord i ∘ₗ f = b.coord i ∘ₗ g) → f = g := by
    intro f g h
    ext v
    apply b.ext_elem
    intro i
    have hi := congrArg (fun l : VJ →ₗ[k] k => l v) (h i)
    simpa only [LinearMap.comp_apply, Module.Basis.coord_apply] using hi
  let c : Fin (Module.finrank k V₀) → SpecialLinearGroup k VJ → Module.Dual k VJ :=
    fun j B => b.coord j ∘ₗ ψ B
  have hc : ∀ j (B B' : SpecialLinearGroup k VJ),
      c j (B * B') = c j B + c j B' ∘ₗ
        (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap := by
    intro j B B'
    change b.coord j ∘ₗ ψ (B * B') =
      b.coord j ∘ₗ ψ B + b.coord j ∘ₗ ψ B' ∘ₗ
        (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap
    rw [hψc B B', LinearMap.comp_add, ← LinearMap.comp_assoc]
  have hex : ∀ j, ∃ f : Module.Dual k VJ, ∀ B,
      c j B = f ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap - f :=
    fun j => exists_eq_sub_of_cocycle_dual hVJ (c j) (hc j)
  choose f hf using hex
  let ψ₀ : VJ →ₗ[k] V₀ :=
    b.equivFun.symm.toLinearMap ∘ₗ LinearMap.pi (fun j => f j)
  have hψ₀ : ∀ i, b.coord i ∘ₗ ψ₀ = f i := by
    intro i
    ext v
    have h1 : b.equivFun (ψ₀ v) = fun j => f j v := by
      funext j
      change b.equivFun (b.equivFun.symm ((LinearMap.pi fun j => f j) v)) j = (f j) v
      rw [b.equivFun.apply_symm_apply]
      rfl
    change b.coord i (ψ₀ v) = f i v
    rw [Module.Basis.coord_apply]
    rw [← congrFun (Module.Basis.equivFun_apply b (ψ₀ v)) i]
    exact congrFun h1 i
  have hψ_eq : ∀ B : SpecialLinearGroup k VJ,
      ψ B = ψ₀ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap - ψ₀ := by
    intro B
    apply coord_eq_of_eq
    intro i
    rw [show b.coord i ∘ₗ ψ B = c i B from rfl, hf i B]
    rw [LinearMap.comp_sub, ← LinearMap.comp_assoc, hψ₀ i]
  have ha_inv : (modelA2Elt (-ψ₀) : SpecialLinearGroup k (VJ × V₀))⁻¹ =
      modelA2Elt ψ₀ := by
    have hmul : modelA2Elt (-ψ₀) * modelA2Elt ψ₀ = 1 := by
      rw [← modelA2Elt_add, neg_add_cancel, modelA2Elt_zero]
    exact inv_eq_of_mul_eq_one_right hmul
  let a₂ : ↥(modelA2 k VJ V₀) :=
    ⟨modelA2Elt (-ψ₀), (mem_modelA2_iff _).2 ⟨-ψ₀, rfl⟩⟩
  have ha₂_val : (a₂ : SpecialLinearGroup k (VJ × V₀)) = modelA2Elt (-ψ₀) := rfl
  refine ⟨a₂, ?_⟩
  intro g
  obtain ⟨B, hB⟩ := exists_blockSLk g
  have hg : g = blockK B := Subtype.ext hB.symm
  have hδg : (δ g : SpecialLinearGroup k (VJ × V₀)) = modelA2Elt (ψ B) := by
    rw [hg]
    exact (hψ B).symm
  have hprod : (a₂ : SpecialLinearGroup k (VJ × V₀)) *
      ((g : SpecialLinearGroup k (VJ × V₀)) *
        (a₂ : SpecialLinearGroup k (VJ × V₀))⁻¹ *
        (g : SpecialLinearGroup k (VJ × V₀))⁻¹) = modelA2Elt (ψ B) := by
    rw [ha₂_val, ha_inv, hg]
    rw [show (blockK B : SpecialLinearGroup k (VJ × V₀)) = blockSLk k V₀ B from rfl]
    rw [blockSLk_mul_modelA2Elt_mul_inv]
    rw [← modelA2Elt_add]
    congr 1
    rw [hψ_eq B]
    abel
  exact hδg.trans hprod.symm

end CFSG.LinearAlgebra.RootGroupSL
