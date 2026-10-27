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

private noncomputable def a1ToA (φ : V₀ →ₗ[k] VJ) : ↥(modelA1 k VJ V₀) :=
  ⟨modelA1Elt φ, (mem_modelA1_iff (modelA1Elt φ)).mpr ⟨φ, rfl⟩⟩

private lemma a1ToA_coe (φ : V₀ →ₗ[k] VJ) :
    (a1ToA φ : SpecialLinearGroup k (VJ × V₀)) = modelA1Elt φ := rfl

private lemma a1ToA_add (φ φ' : V₀ →ₗ[k] VJ) :
    a1ToA (φ + φ') = a1ToA φ * a1ToA φ' := by
  apply Subtype.ext
  exact modelA1Elt_add φ φ'

private lemma a1ToA_injective : Function.Injective (a1ToA (k := k) (VJ := VJ) (V₀ := V₀)) := by
  intro φ φ' h
  exact modelA1Elt_injective (Subtype.ext_iff.mp h)

private noncomputable def a1Preimage (a : ↥(modelA1 k VJ V₀)) : V₀ →ₗ[k] VJ :=
  Classical.choose ((mem_modelA1_iff (a : SpecialLinearGroup k (VJ × V₀))).mp a.2)

private lemma a1ToA_preimage (a : ↥(modelA1 k VJ V₀)) : a1ToA (a1Preimage a) = a := by
  unfold a1Preimage
  apply Subtype.ext
  exact Classical.choose_spec ((mem_modelA1_iff (a : SpecialLinearGroup k (VJ × V₀))).mp a.2)

private noncomputable def a1Transport (γ : MulAut ↥(modelA1 k VJ V₀)) :
    (V₀ →ₗ[k] VJ) → (V₀ →ₗ[k] VJ) :=
  fun φ => a1Preimage (γ (a1ToA φ))

private lemma a1ToA_transport (γ : MulAut ↥(modelA1 k VJ V₀)) (φ : V₀ →ₗ[k] VJ) :
    a1ToA (a1Transport γ φ) = γ (a1ToA φ) :=
  a1ToA_preimage (γ (a1ToA φ))

private lemma a1Transport_add (γ : MulAut ↥(modelA1 k VJ V₀)) (φ φ' : V₀ →ₗ[k] VJ) :
    a1Transport γ (φ + φ') = a1Transport γ φ + a1Transport γ φ' := by
  apply a1ToA_injective
  calc a1ToA (a1Transport γ (φ + φ')) = γ (a1ToA (φ + φ')) := a1ToA_transport γ (φ + φ')
    _ = γ (a1ToA φ * a1ToA φ') := by rw [a1ToA_add]
    _ = γ (a1ToA φ) * γ (a1ToA φ') := map_mul γ _ _
    _ = a1ToA (a1Transport γ φ) * a1ToA (a1Transport γ φ') := by
          rw [a1ToA_transport, a1ToA_transport]
    _ = a1ToA (a1Transport γ φ + a1Transport γ φ') := (a1ToA_add _ _).symm

private noncomputable def a1TransportHom (γ : MulAut ↥(modelA1 k VJ V₀)) :
    (V₀ →ₗ[k] VJ) →+ (V₀ →ₗ[k] VJ) :=
  AddMonoidHom.mk' (a1Transport γ) (a1Transport_add γ)

private lemma a1Transport_surjective (γ : MulAut ↥(modelA1 k VJ V₀)) :
    Function.Surjective (a1Transport γ) := by
  intro ψ
  obtain ⟨a, ha⟩ := MulEquiv.surjective γ (a1ToA ψ)
  obtain ⟨φ, hφ⟩ : ∃ φ, a1ToA φ = a := ⟨a1Preimage a, a1ToA_preimage a⟩
  have h : γ (a1ToA φ) = a1ToA ψ := by rw [hφ]; exact ha
  refine ⟨φ, ?_⟩
  apply a1ToA_injective
  rw [a1ToA_transport, h]

private lemma a1Transport_comp (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (B : SpecialLinearGroup k VJ) (φ : V₀ →ₗ[k] VJ) :
    a1Transport γ ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ) =
      (SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ a1Transport γ φ := by
  apply a1ToA_injective
  have hgmem : blockSLk k V₀ B ∈ modelK1 k VJ V₀ := by
    rw [modelK1_eq_range]; exact ⟨B, rfl⟩
  have hconj : a1ToA ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ) =
      (⟨blockSLk k V₀ B * (a1ToA φ : SpecialLinearGroup k (VJ × V₀)) * (blockSLk k V₀ B)⁻¹,
        modelK1_conj_mem_modelA1 hgmem (a1ToA φ).2⟩ : ↥(modelA1 k VJ V₀)) := by
    apply Subtype.ext
    show modelA1Elt ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ) =
      blockSLk k V₀ B * (a1ToA φ : SpecialLinearGroup k (VJ × V₀)) * (blockSLk k V₀ B)⁻¹
    rw [a1ToA_coe]
    exact (blockSLk_mul_modelA1Elt_mul_inv B φ).symm
  calc a1ToA (a1Transport γ ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ))
      = γ (a1ToA ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ φ)) :=
        a1ToA_transport γ _
    _ = γ (⟨blockSLk k V₀ B * (a1ToA φ : SpecialLinearGroup k (VJ × V₀)) * (blockSLk k V₀ B)⁻¹,
            modelK1_conj_mem_modelA1 hgmem (a1ToA φ).2⟩ : ↥(modelA1 k VJ V₀)) := by rw [hconj]
    _ = (⟨blockSLk k V₀ B * (γ (a1ToA φ) : SpecialLinearGroup k (VJ × V₀)) *
            (blockSLk k V₀ B)⁻¹,
            modelK1_conj_mem_modelA1 hgmem (γ (a1ToA φ)).2⟩ : ↥(modelA1 k VJ V₀)) := by
          apply Subtype.ext
          exact hγ ⟨blockSLk k V₀ B, hgmem⟩ (a1ToA φ)
    _ = (⟨blockSLk k V₀ B * (a1ToA (a1Transport γ φ) : SpecialLinearGroup k (VJ × V₀)) *
            (blockSLk k V₀ B)⁻¹,
            modelK1_conj_mem_modelA1 hgmem (a1ToA (a1Transport γ φ)).2⟩ :
              ↥(modelA1 k VJ V₀)) := by
          rw [a1ToA_transport]
    _ = a1ToA ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ a1Transport γ φ) := by
          apply Subtype.ext
          show blockSLk k V₀ B * (a1ToA (a1Transport γ φ) : SpecialLinearGroup k (VJ × V₀)) *
              (blockSLk k V₀ B)⁻¹ =
            modelA1Elt ((SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ a1Transport γ φ)
          exact blockSLk_mul_modelA1Elt_mul_inv B (a1Transport γ φ)

private noncomputable def eFun {ι : Type*} (b : Basis ι k V₀) (x : VJ) (j : ι) :
    V₀ →ₗ[k] VJ :=
  (b.coord j).smulRight x

private lemma eFun_add {ι : Type*} (b : Basis ι k V₀) (x x' : VJ) (j : ι) :
    eFun b (x + x') j = eFun b x j + eFun b x' j := by
  ext w
  simp [eFun, LinearMap.smulRight_apply, smul_add]

private lemma sum_eFun {ι : Type*} [Fintype ι] (b : Basis ι k V₀) (φ : V₀ →ₗ[k] VJ) :
    (∑ j, eFun b (φ (b j)) j) = φ := by
  ext w
  rw [LinearMap.sum_apply]
  have hw : φ w = ∑ j, b.coord j w • φ (b j) := by
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [b.coord_apply, map_smul]
  rw [hw]
  apply Finset.sum_congr rfl
  intro j _
  rw [eFun, LinearMap.smulRight_apply]

private noncomputable def gammaMat {ι : Type*} (γ : MulAut ↥(modelA1 k VJ V₀))
    (b : Basis ι k V₀) (i j : ι) : VJ →+ VJ :=
  AddMonoidHom.mk' (fun x => a1Transport γ (eFun b x j) (b i)) (by
    intro x x'
    rw [eFun_add, a1Transport_add]
    rfl)

private lemma gammaMat_comm {ι : Type*} (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (b : Basis ι k V₀) (i j : ι) (B : SpecialLinearGroup k VJ) (x : VJ) :
    gammaMat γ b i j (B x) = B (gammaMat γ b i j x) := by
  show a1Transport γ (eFun b (B x) j) (b i) = B (a1Transport γ (eFun b x j) (b i))
  have hcomp : eFun b (B x) j =
      (SpecialLinearGroup.toLinearEquiv B).toLinearMap ∘ₗ eFun b x j := by
    ext w
    simp [eFun, LinearMap.smulRight_apply, LinearMap.comp_apply, map_smul]
  rw [hcomp, a1Transport_comp γ hγ B (eFun b x j)]
  rfl

private noncomputable def gammaScalar {ι : Type*} (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (b : Basis ι k V₀) (i j : ι) : k :=
  Classical.choose (exists_smul_of_commute_specialLinear (F := k) (V := VJ) hV
    (gammaMat γ b i j) (fun g x => gammaMat_comm γ hγ b i j g x))

private lemma gammaScalar_spec {ι : Type*} (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (b : Basis ι k V₀) (i j : ι) :
    ∀ x, gammaMat γ b i j x = gammaScalar γ hγ hV b i j • x :=
  Classical.choose_spec (exists_smul_of_commute_specialLinear (F := k) (V := VJ) hV
    (gammaMat γ b i j) (fun g x => gammaMat_comm γ hγ b i j g x))

private noncomputable def mat1 {ι : Type*} [Fintype ι] (b : Basis ι k V₀)
    (m : ι → ι → k) : V₀ →ₗ[k] V₀ :=
  b.constr k (fun i => ∑ j, m i j • b j)

private lemma mat1_basis {ι : Type*} [Fintype ι] (b : Basis ι k V₀) (m : ι → ι → k) (i : ι) :
    mat1 b m (b i) = ∑ j, m i j • b j := by
  rw [mat1, b.constr_basis]

private lemma a1Transport_eq_comp {ι : Type*} [Fintype ι] (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (b : Basis ι k V₀) (φ : V₀ →ₗ[k] VJ) :
    a1Transport γ φ = φ ∘ₗ mat1 b (gammaScalar γ hγ hV b) := by
  apply b.ext
  intro i
  rw [LinearMap.comp_apply, mat1_basis]
  have h1 : a1Transport γ φ (b i) =
      ∑ j, gammaScalar γ hγ hV b i j • φ (b j) := by
    conv_lhs => rw [← sum_eFun b φ]
    calc a1Transport γ (∑ j, eFun b (φ (b j)) j) (b i)
        = (a1TransportHom γ (∑ j, eFun b (φ (b j)) j)) (b i) := rfl
      _ = (∑ j, a1TransportHom γ (eFun b (φ (b j)) j)) (b i) := by rw [map_sum]
      _ = ∑ j, a1TransportHom γ (eFun b (φ (b j)) j) (b i) := by rw [LinearMap.sum_apply]
      _ = ∑ j, gammaScalar γ hγ hV b i j • φ (b j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact gammaScalar_spec γ hγ hV b i j (φ (b j))
  rw [h1, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]

private lemma mat1_eq_zero {ι : Type*} [Fintype ι] (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (hVJ : 3 ≤ Module.finrank k VJ) (b : Basis ι k V₀)
    {v : V₀} (hv : mat1 b (gammaScalar γ hγ hV b) v = 0) : v = 0 := by
  by_contra hne
  have hcoord : ∃ i : ι, b.coord i v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (b.forall_coord_eq_zero_iff.mp h)
  obtain ⟨i0, hi0⟩ := hcoord
  let c : Module.Dual k V₀ := (b.coord i0 v)⁻¹ • b.coord i0
  have hc : c v = 1 := by
    show ((b.coord i0 v)⁻¹ • b.coord i0) v = 1
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hi0]
  have hpos : 0 < Module.finrank k VJ := by omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  let ψ : V₀ →ₗ[k] VJ := c.smulRight x
  obtain ⟨φ, hφ⟩ := a1Transport_surjective γ ψ
  have hψv : ψ v = 0 := by
    rw [← hφ, a1Transport_eq_comp γ hγ hV b φ]
    rw [LinearMap.comp_apply, hv, map_zero]
  have hxv : ψ v = x := by
    show (c.smulRight x) v = x
    rw [LinearMap.smulRight_apply, hc, one_smul]
  rw [hxv] at hψv
  exact hx hψv

private lemma mat1_injective {ι : Type*} [Fintype ι] (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹)
    (hV : 2 ≤ Module.finrank k VJ) (hVJ : 3 ≤ Module.finrank k VJ) (b : Basis ι k V₀) :
    Function.Injective (mat1 b (gammaScalar γ hγ hV b)) := by
  intro v v' h
  have hzero : mat1 b (gammaScalar γ hγ hV b) (v - v') = 0 := by
    rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (mat1_eq_zero γ hγ hV hVJ b hzero)

private lemma diagY_inv (y : V₀ ≃ₗ[k] V₀) :
    (diagY (VJ := VJ) y)⁻¹ = diagY (VJ := VJ) y.symm := by
  change (diagY (VJ := VJ) y).symm = diagY (VJ := VJ) y.symm
  rw [diagY, diagY, LinearEquiv.prodCongr_symm, LinearEquiv.refl_symm]

private lemma diagY_apply (y : V₀ ≃ₗ[k] V₀) (v : VJ) (w : V₀) :
    diagY (VJ := VJ) y (v, w) = (v, y w) := by
  rw [diagY, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]

private lemma diagY_symm_apply (y : V₀ ≃ₗ[k] V₀) (v : VJ) (w : V₀) :
    (diagY (VJ := VJ) y)⁻¹ (v, w) = (v, y.symm w) := by
  rw [diagY_inv, diagY_apply]

private lemma diagY_conj_A1 (y : V₀ ≃ₗ[k] V₀) (φ : V₀ →ₗ[k] VJ) :
    diagY (VJ := VJ) y * SpecialLinearGroup.toLinearEquiv (modelA1Elt φ) *
        (diagY (VJ := VJ) y)⁻¹ =
      SpecialLinearGroup.toLinearEquiv (modelA1Elt (φ ∘ₗ (y.symm : V₀ →ₗ[k] V₀))) := by
  apply LinearEquiv.ext
  rintro ⟨v, w⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagY_symm_apply,
    SpecialLinearGroup.toLinearEquiv_apply, modelA1Elt_apply, diagY_apply,
    SpecialLinearGroup.toLinearEquiv_apply, modelA1Elt_apply, LinearMap.comp_apply]
  simp

theorem modelA1_end (hVJ : 3 ≤ Module.finrank k VJ) (γ : MulAut ↥(modelA1 k VJ V₀))
    (hγ : ∀ (g : ↥(modelK1 k VJ V₀)) (a : ↥(modelA1 k VJ V₀)),
      ((γ ⟨(g : SpecialLinearGroup k (VJ × V₀)) * (a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹, modelK1_conj_mem_modelA1 g.2 a.2⟩ :
            ↥(modelA1 k VJ V₀)) : SpecialLinearGroup k (VJ × V₀)) =
        (g : SpecialLinearGroup k (VJ × V₀)) * (γ a : SpecialLinearGroup k (VJ × V₀)) *
          (g : SpecialLinearGroup k (VJ × V₀))⁻¹) :
    ∃ y : V₀ ≃ₗ[k] V₀, ∀ a : ↥(modelA1 k VJ V₀),
      SpecialLinearGroup.toLinearEquiv ((γ a : ↥(modelA1 k VJ V₀)) :
        SpecialLinearGroup k (VJ × V₀)) =
        diagY y * SpecialLinearGroup.toLinearEquiv (a : SpecialLinearGroup k (VJ × V₀)) *
          (diagY y)⁻¹ := by
  classical
  have hV : 2 ≤ Module.finrank k VJ := by omega
  let b : Basis (Fin (Module.finrank k V₀)) k V₀ := Module.finBasis k V₀
  let M : V₀ →ₗ[k] V₀ := mat1 b (gammaScalar γ hγ hV b)
  have hMinj : Function.Injective M := mat1_injective γ hγ hV hVJ b
  let eM : V₀ ≃ₗ[k] V₀ := LinearEquiv.ofInjectiveEndo M hMinj
  refine ⟨eM.symm, fun a => ?_⟩
  obtain ⟨φ, hφ⟩ := (mem_modelA1_iff (a : SpecialLinearGroup k (VJ × V₀))).mp a.2
  have ha : a = a1ToA φ := Subtype.ext hφ.symm
  rw [ha, ← a1ToA_transport γ φ, a1ToA_coe, a1Transport_eq_comp γ hγ hV b φ]
  have hMeq : mat1 b (gammaScalar γ hγ hV b) = ((eM.symm).symm : V₀ →ₗ[k] V₀) := by
    rw [LinearEquiv.symm_symm]
    apply LinearMap.ext
    intro v
    show (eM : V₀ →ₗ[k] V₀) v = mat1 b (gammaScalar γ hγ hV b) v
    change (LinearEquiv.ofInjectiveEndo M hMinj : V₀ → V₀) v = M v
    rw [LinearEquiv.coe_ofInjectiveEndo]
  rw [hMeq]
  exact (diagY_conj_A1 eM.symm φ).symm

end CFSG.LinearAlgebra.RootGroupSL
