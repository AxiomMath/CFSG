module

public import CFSG.LinearAlgebra.RootGroupSL.ModelStructure
public import CFSG.LinearAlgebra.RootGroupSL.SchurSL


public section

namespace CFSG.LinearAlgebra.RootGroupSL

open Module

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀] [Finite k]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

private lemma diagY_inv_dual (y : V₀ ≃ₗ[k] V₀) :
    (diagY (VJ := VJ) y)⁻¹ = diagY (VJ := VJ) y.symm := by
  change (diagY (VJ := VJ) y).symm = diagY (VJ := VJ) y.symm
  rw [diagY, diagY, LinearEquiv.prodCongr_symm, LinearEquiv.refl_symm]

private lemma diagY_apply_dual (y : V₀ ≃ₗ[k] V₀) (v : VJ) (w : V₀) :
    diagY (VJ := VJ) y (v, w) = (v, y w) := by
  rw [diagY, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]

private lemma diagY_symm_apply_dual (y : V₀ ≃ₗ[k] V₀) (v : VJ) (w : V₀) :
    (diagY (VJ := VJ) y)⁻¹ (v, w) = (v, y.symm w) := by
  rw [diagY_inv_dual, diagY_apply_dual]

private noncomputable def a2ToA (ψ : VJ →ₗ[k] V₀) : ↥(modelA2 k VJ V₀) :=
  ⟨modelA2Elt ψ, (mem_modelA2_iff (modelA2Elt ψ)).mpr ⟨ψ, rfl⟩⟩

private lemma a2ToA_coe (ψ : VJ →ₗ[k] V₀) :
    (a2ToA ψ : SpecialLinearGroup k (VJ × V₀)) = modelA2Elt ψ := rfl

private lemma a2ToA_add (ψ ψ' : VJ →ₗ[k] V₀) :
    a2ToA (ψ + ψ') = a2ToA ψ * a2ToA ψ' := by
  apply Subtype.ext
  exact modelA2Elt_add ψ ψ'

private lemma a2ToA_injective : Function.Injective (a2ToA (k := k) (VJ := VJ) (V₀ := V₀)) := by
  intro ψ ψ' h
  exact modelA2Elt_injective (Subtype.ext_iff.mp h)

private noncomputable def a2Preimage (a : ↥(modelA2 k VJ V₀)) : VJ →ₗ[k] V₀ :=
  Classical.choose ((mem_modelA2_iff (a : SpecialLinearGroup k (VJ × V₀))).mp a.2)

private lemma a2ToA_preimage (a : ↥(modelA2 k VJ V₀)) : a2ToA (a2Preimage a) = a := by
  unfold a2Preimage
  apply Subtype.ext
  exact Classical.choose_spec ((mem_modelA2_iff (a : SpecialLinearGroup k (VJ × V₀))).mp a.2)

private noncomputable def a2Transport (γ : MulAut ↥(modelA2 k VJ V₀)) :
    (VJ →ₗ[k] V₀) → (VJ →ₗ[k] V₀) :=
  fun ψ => a2Preimage (γ (a2ToA ψ))

private lemma a2ToA_transport (γ : MulAut ↥(modelA2 k VJ V₀)) (ψ : VJ →ₗ[k] V₀) :
    a2ToA (a2Transport γ ψ) = γ (a2ToA ψ) :=
  a2ToA_preimage (γ (a2ToA ψ))

private lemma a2Transport_add (γ : MulAut ↥(modelA2 k VJ V₀)) (ψ ψ' : VJ →ₗ[k] V₀) :
    a2Transport γ (ψ + ψ') = a2Transport γ ψ + a2Transport γ ψ' := by
  apply a2ToA_injective
  calc a2ToA (a2Transport γ (ψ + ψ')) = γ (a2ToA (ψ + ψ')) := a2ToA_transport γ (ψ + ψ')
    _ = γ (a2ToA ψ * a2ToA ψ') := by rw [a2ToA_add]
    _ = γ (a2ToA ψ) * γ (a2ToA ψ') := map_mul γ _ _
    _ = a2ToA (a2Transport γ ψ) * a2ToA (a2Transport γ ψ') := by
          rw [a2ToA_transport, a2ToA_transport]
    _ = a2ToA (a2Transport γ ψ + a2Transport γ ψ') := (a2ToA_add _ _).symm

private noncomputable def a2TransportHom (γ : MulAut ↥(modelA2 k VJ V₀)) :
    (VJ →ₗ[k] V₀) →+ (VJ →ₗ[k] V₀) :=
  AddMonoidHom.mk' (a2Transport γ) (a2Transport_add γ)

private lemma a2Transport_surjective (γ : MulAut ↥(modelA2 k VJ V₀)) :
    Function.Surjective (a2Transport γ) := by
  intro ψ
  obtain ⟨a, ha⟩ := MulEquiv.surjective γ (a2ToA ψ)
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀, a2ToA ψ₀ = a := ⟨a2Preimage a, a2ToA_preimage a⟩
  have h : γ (a2ToA ψ₀) = a2ToA ψ := by rw [hψ₀]; exact ha
  refine ⟨ψ₀, ?_⟩
  apply a2ToA_injective
  rw [a2ToA_transport, h]

private lemma a2Transport_comp (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (B : SpecialLinearGroup k VJ) (ψ : VJ →ₗ[k] V₀) :
    a2Transport γ (ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) =
      a2Transport γ ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap := by
  apply a2ToA_injective
  have hgmem : blockSLk k V₀ B ∈ modelK1 k VJ V₀ := by
    rw [modelK1_eq_range]; exact ⟨B, rfl⟩
  have hconj : a2ToA (ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) =
      (⟨blockSLk k V₀ B * (a2ToA ψ : SpecialLinearGroup k (VJ × V₀)) * (blockSLk k V₀ B)⁻¹,
        modelK1_conj_mem_modelA2 hgmem (a2ToA ψ).2⟩ : ↥(modelA2 k VJ V₀)) := by
    apply Subtype.ext
    show modelA2Elt (ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) =
      blockSLk k V₀ B * (a2ToA ψ : SpecialLinearGroup k (VJ × V₀)) * (blockSLk k V₀ B)⁻¹
    rw [a2ToA_coe]
    exact (blockSLk_mul_modelA2Elt_mul_inv B ψ).symm
  calc a2ToA (a2Transport γ (ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap))
      = γ (a2ToA (ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap)) :=
        a2ToA_transport γ _
    _ = γ (⟨blockSLk k V₀ B * (a2ToA ψ : SpecialLinearGroup k (VJ × V₀)) *
            (blockSLk k V₀ B)⁻¹,
            modelK1_conj_mem_modelA2 hgmem (a2ToA ψ).2⟩ : ↥(modelA2 k VJ V₀)) := by rw [hconj]
    _ = (⟨blockSLk k V₀ B * (γ (a2ToA ψ) : SpecialLinearGroup k (VJ × V₀)) *
            (blockSLk k V₀ B)⁻¹,
            modelK1_conj_mem_modelA2 hgmem (γ (a2ToA ψ)).2⟩ : ↥(modelA2 k VJ V₀)) := by
          apply Subtype.ext
          exact hγ ⟨blockSLk k V₀ B, hgmem⟩ (a2ToA ψ)
    _ = (⟨blockSLk k V₀ B * (a2ToA (a2Transport γ ψ) : SpecialLinearGroup k (VJ × V₀)) *
            (blockSLk k V₀ B)⁻¹,
            modelK1_conj_mem_modelA2 hgmem (a2ToA (a2Transport γ ψ)).2⟩ :
              ↥(modelA2 k VJ V₀)) := by
          rw [a2ToA_transport]
    _ = a2ToA (a2Transport γ ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) := by
          apply Subtype.ext
          show blockSLk k V₀ B * (a2ToA (a2Transport γ ψ) : SpecialLinearGroup k (VJ × V₀)) *
              (blockSLk k V₀ B)⁻¹ =
            modelA2Elt (a2Transport γ ψ ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap)
          exact blockSLk_mul_modelA2Elt_mul_inv B (a2Transport γ ψ)

private noncomputable def e2Fun {ι : Type*} (b : Basis ι k V₀) (f : Module.Dual k VJ) (j : ι) :
    VJ →ₗ[k] V₀ :=
  f.smulRight (b j)

private lemma e2Fun_add {ι : Type*} (b : Basis ι k V₀) (f f' : Module.Dual k VJ) (j : ι) :
    e2Fun b (f + f') j = e2Fun b f j + e2Fun b f' j := by
  ext v
  simp [e2Fun, LinearMap.smulRight_apply, add_smul]

private lemma sum_e2Fun {ι : Type*} [Fintype ι] (b : Basis ι k V₀) (ψ : VJ →ₗ[k] V₀) :
    (∑ j, e2Fun b (b.coord j ∘ₗ ψ) j) = ψ := by
  ext v
  rw [LinearMap.sum_apply]
  have hv : ψ v = ∑ j, b.coord j (ψ v) • b j := by
    conv_lhs => rw [← b.sum_repr (ψ v)]
    apply Finset.sum_congr rfl
    intro j _
    rw [b.coord_apply]
  rw [hv]
  apply Finset.sum_congr rfl
  intro j _
  simp [e2Fun, LinearMap.smulRight_apply, LinearMap.comp_apply]

private noncomputable def gammaMat2 {ι : Type*} (γ : MulAut ↥(modelA2 k VJ V₀))
    (b : Basis ι k V₀) (i j : ι) : Module.Dual k VJ →+ Module.Dual k VJ :=
  AddMonoidHom.mk' (fun f => b.coord i ∘ₗ a2Transport γ (e2Fun b f j)) (by
    intro f f'
    rw [e2Fun_add, a2Transport_add]
    ext v
    simp [LinearMap.comp_apply, map_add])

private lemma gammaMat2_comm {ι : Type*} (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (b : Basis ι k V₀) (i j : ι) (B : SpecialLinearGroup k VJ) (f : Module.Dual k VJ) :
    gammaMat2 γ b i j (f ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) =
      gammaMat2 γ b i j f ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap := by
  show b.coord i ∘ₗ a2Transport γ (e2Fun b (f ∘ₗ
      (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) j) =
    b.coord i ∘ₗ a2Transport γ (e2Fun b f j) ∘ₗ
      (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap
  have he : e2Fun b (f ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap) j =
      e2Fun b f j ∘ₗ (SpecialLinearGroup.toLinearEquiv B⁻¹).toLinearMap := by
    ext v
    simp [e2Fun, LinearMap.smulRight_apply, LinearMap.comp_apply]
  rw [he, a2Transport_comp γ hγ B (e2Fun b f j)]

private noncomputable def gammaScalar2 {ι : Type*} (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (b : Basis ι k V₀) (i j : ι) : k :=
  Classical.choose (exists_smul_of_commute_specialLinear_dual (F := k) (V := VJ) hV
    (gammaMat2 γ b i j) (fun g f => gammaMat2_comm γ hγ b i j g f))

private lemma gammaScalar2_spec {ι : Type*} (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (b : Basis ι k V₀) (i j : ι) :
    ∀ f, gammaMat2 γ b i j f = gammaScalar2 γ hγ hV b i j • f :=
  Classical.choose_spec (exists_smul_of_commute_specialLinear_dual (F := k) (V := VJ) hV
    (gammaMat2 γ b i j) (fun g f => gammaMat2_comm γ hγ b i j g f))

private noncomputable def mat2 {ι : Type*} [Fintype ι] (b : Basis ι k V₀)
    (m : ι → ι → k) : V₀ →ₗ[k] V₀ :=
  b.constr k (fun j => ∑ i, m i j • b i)

private lemma mat2_basis {ι : Type*} [Fintype ι] (b : Basis ι k V₀) (m : ι → ι → k) (j : ι) :
    mat2 b m (b j) = ∑ i, m i j • b i := by
  rw [mat2, b.constr_basis]

private lemma a2Transport_e2Fun {ι : Type*} [Fintype ι] (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (b : Basis ι k V₀) (f : Module.Dual k VJ) (j : ι) :
    a2Transport γ (e2Fun b f j) = mat2 b (gammaScalar2 γ hγ hV b) ∘ₗ e2Fun b f j := by
  ext v
  have h1 : a2Transport γ (e2Fun b f j) v =
      ∑ i, (gammaScalar2 γ hγ hV b i j * f v) • b i := by
    conv_lhs => rw [← b.sum_repr (a2Transport γ (e2Fun b f j) v)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← b.coord_apply]
    have hs : b.coord i (a2Transport γ (e2Fun b f j) v) =
        gammaScalar2 γ hγ hV b i j * f v := by
      have h := DFunLike.congr_fun (gammaScalar2_spec γ hγ hV b i j f) v
      simpa [gammaMat2, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] using h
    rw [hs]
  have h2 : (mat2 b (gammaScalar2 γ hγ hV b) ∘ₗ e2Fun b f j) v =
      ∑ i, (f v * gammaScalar2 γ hγ hV b i j) • b i := by
    rw [LinearMap.comp_apply]
    show mat2 b (gammaScalar2 γ hγ hV b) (f v • b j) = _
    rw [map_smul, mat2_basis, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_comm]
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

private lemma a2Transport_eq_comp {ι : Type*} [Fintype ι] (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (b : Basis ι k V₀) (ψ : VJ →ₗ[k] V₀) :
    a2Transport γ ψ = mat2 b (gammaScalar2 γ hγ hV b) ∘ₗ ψ := by
  conv_lhs => rw [← sum_e2Fun b ψ]
  calc a2Transport γ (∑ j, e2Fun b (b.coord j ∘ₗ ψ) j)
      = a2TransportHom γ (∑ j, e2Fun b (b.coord j ∘ₗ ψ) j) := rfl
    _ = ∑ j, a2TransportHom γ (e2Fun b (b.coord j ∘ₗ ψ) j) := by rw [map_sum]
    _ = ∑ j, mat2 b (gammaScalar2 γ hγ hV b) ∘ₗ e2Fun b (b.coord j ∘ₗ ψ) j := by
          apply Finset.sum_congr rfl
          intro j _
          exact a2Transport_e2Fun γ hγ hV b (b.coord j ∘ₗ ψ) j
    _ = mat2 b (gammaScalar2 γ hγ hV b) ∘ₗ (∑ j, e2Fun b (b.coord j ∘ₗ ψ) j) := by
          ext v
          simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
    _ = mat2 b (gammaScalar2 γ hγ hV b) ∘ₗ ψ := by rw [sum_e2Fun b ψ]

private lemma mat2_surjective {ι : Type*} [Fintype ι] (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (hVJ : 3 ≤ Module.finrank k VJ) (b : Basis ι k V₀) :
    Function.Surjective (mat2 b (gammaScalar2 γ hγ hV b)) := by
  intro v
  have hpos : 0 < Module.finrank k VJ := by omega
  let bJ : Basis (Fin (Module.finrank k VJ)) k VJ := Module.finBasis k VJ
  let i0 : Fin (Module.finrank k VJ) := ⟨0, hpos⟩
  let η : VJ →ₗ[k] V₀ := (bJ.coord i0).smulRight v
  obtain ⟨ψ, hψ⟩ := a2Transport_surjective γ η
  refine ⟨ψ (bJ i0), ?_⟩
  have h : mat2 b (gammaScalar2 γ hγ hV b) (ψ (bJ i0)) = η (bJ i0) := by
    rw [← LinearMap.comp_apply, ← a2Transport_eq_comp γ hγ hV b ψ, hψ]
  rw [h]
  show η (bJ i0) = v
  simp [η, LinearMap.smulRight_apply]

private lemma mat2_injective {ι : Type*} [Fintype ι] (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (hVJ : 3 ≤ Module.finrank k VJ) (b : Basis ι k V₀) :
    Function.Injective (mat2 b (gammaScalar2 γ hγ hV b)) :=
  LinearMap.injective_iff_surjective.mpr (mat2_surjective γ hγ hV hVJ b)

private lemma diagY_conj_A2 (y : V₀ ≃ₗ[k] V₀) (ψ : VJ →ₗ[k] V₀) :
    diagY (VJ := VJ) y * SpecialLinearGroup.toLinearEquiv (modelA2Elt ψ) *
        (diagY (VJ := VJ) y)⁻¹ =
      SpecialLinearGroup.toLinearEquiv (modelA2Elt ((y : V₀ ≃ₗ[k] V₀).toLinearMap ∘ₗ ψ)) := by
  apply LinearEquiv.ext
  rintro ⟨v, w⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagY_symm_apply_dual,
    SpecialLinearGroup.toLinearEquiv_apply, modelA2Elt_apply, diagY_apply_dual,
    SpecialLinearGroup.toLinearEquiv_apply, modelA2Elt_apply, LinearMap.comp_apply]
  simp [map_add]

theorem modelA2_end (hVJ : 3 ≤ Module.finrank k VJ) (γ : MulAut ↥(modelA2 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA2 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA2 g.2 a.2⟩ :
            ↥(modelA2 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹) :
    ∃ y : V₀ ≃ₗ[k] V₀, ∀ a : ↥(modelA2 k VJ V₀),
      SpecialLinearGroup.toLinearEquiv ((γ a : ↥(modelA2 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) =
        diagY y * SpecialLinearGroup.toLinearEquiv (a : SpecialLinearGroup k (VJ × V₀)) *
          (diagY y)⁻¹ := by
  classical
  have hV : 2 ≤ Module.finrank k VJ := by omega
  let b : Basis (Fin (Module.finrank k V₀)) k V₀ := Module.finBasis k V₀
  let M : V₀ →ₗ[k] V₀ := mat2 b (gammaScalar2 γ hγ hV b)
  have hMinj : Function.Injective M := mat2_injective γ hγ hV hVJ b
  let eM : V₀ ≃ₗ[k] V₀ := LinearEquiv.ofInjectiveEndo M hMinj
  refine ⟨eM, fun a => ?_⟩
  obtain ⟨ψ, hψ⟩ := (mem_modelA2_iff (a : SpecialLinearGroup k (VJ × V₀))).mp a.2
  have ha : a = a2ToA ψ := Subtype.ext hψ.symm
  rw [ha, ← a2ToA_transport γ ψ, a2ToA_coe, a2Transport_eq_comp γ hγ hV b ψ]
  have hMeq : (eM : V₀ →ₗ[k] V₀) = mat2 b (gammaScalar2 γ hγ hV b) := by
    apply LinearMap.ext
    intro v
    show (eM : V₀ →ₗ[k] V₀) v = mat2 b (gammaScalar2 γ hγ hV b) v
    change (LinearEquiv.ofInjectiveEndo M hMinj : V₀ → V₀) v = M v
    rw [LinearEquiv.coe_ofInjectiveEndo]
  rw [← hMeq]
  exact (diagY_conj_A2 eM ψ).symm

end CFSG.LinearAlgebra.RootGroupSL
