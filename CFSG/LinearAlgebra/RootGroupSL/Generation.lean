module

import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups
public import CFSG.LinearAlgebra.RootGroupSL.Datum
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open Module
open scoped commutatorElement

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]

variable (k X) in
@[expose] def rootNegEquiv (t : E) : DSpace E X ≃ₗ[k] DSpace E X where
  toFun v := (v.1, v.2.1, v.2.2 + t * v.1)
  invFun v := (v.1, v.2.1, v.2.2 - t * v.1)
  map_add' u v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, mul_add] <;> abel
  map_smul' c v := by
    ext <;> simp [smul_add, Algebra.mul_smul_comm]
  left_inv v := by
    ext <;> simp
  right_inv v := by
    ext <;> simp

private def swapE : DSpace E X ≃ₗ[k] DSpace E X where
  toFun v := (v.2.2, v.2.1, v.1)
  invFun v := (v.2.2, v.2.1, v.1)
  map_add' u v := by ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c v := by ext <;> simp
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

variable [Module.Finite k E] [Module.Finite k X] in
variable (k X) in
@[expose] def rootNegElt (t : E) : SpecialLinearGroup k (DSpace E X) :=
  ⟨rootNegEquiv k X t, by
    let sw : DSpace E X ≃ₗ[k] DSpace E X :=
      { toFun := fun v => (v.2.2, v.2.1, v.1)
        invFun := fun v => (v.2.2, v.2.1, v.1)
        map_add' := by intro u v; ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
        map_smul' := by intro c v; ext <;> simp
        left_inv := by intro v; ext <;> simp
        right_inv := by intro v; ext <;> simp }
    have hconj : rootNegEquiv k X t = sw * shearE X (LinearMap.mulLeft k t) * sw⁻¹ := rfl
    rw [hconj, map_mul, map_mul, det_shearE]
    simp⟩

variable [Module.Finite k E] [Module.Finite k X] in
variable (k E X) in
@[expose] def J0SL : Subgroup (SpecialLinearGroup k (DSpace E X)) :=
  Subgroup.closure (Set.range (rootElt k X (E := E)) ∪ Set.range (rootNegElt k X (E := E)))

section GenerationAux

variable [Module.Finite k E] [Module.Finite k X]

private noncomputable def stdBasis (k E X : Type) [Field k] [Field E] [Algebra k E]
    [AddCommGroup X] [Module k X] [Module.Finite k E] [Module.Finite k X] :
    Basis (Fin (Module.finrank k E) ⊕ (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E)))
      k (DSpace E X) :=
  (Module.finBasis k E).prod ((Module.finBasis k X).prod (Module.finBasis k E))

private noncomputable def slIso (k E X : Type) [Field k] [Field E] [Algebra k E]
    [AddCommGroup X] [Module k X] [Module.Finite k E] [Module.Finite k X] :
    Matrix.SpecialLinearGroup
        (Fin (Module.finrank k E) ⊕ (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) k ≃*
      SpecialLinearGroup k (DSpace E X) :=
  Matrix.SpecialLinearGroup.toLin_equiv (stdBasis k E X)

private lemma char2_add1 [CharP k 2] (a b : E) : (a + b) + (b + (a + b)) = b := by
  haveI : CharP E 2 := charP_of_injective_algebraMap (algebraMap k E).injective 2
  rw [show (a + b) + (b + (a + b)) = ((a + b) + b) + (a + b) by abel]
  rw [CharTwo.add_cancel_right a b]
  exact CharTwo.add_cancel_left a b

private lemma char2_add2 [CharP k 2] (a b : E) : b + (a + b) = a := by
  haveI : CharP E 2 := charP_of_injective_algebraMap (algebraMap k E).injective 2
  rw [show b + (a + b) = b + (b + a) by abel]
  exact CharTwo.add_cancel_left b a

private lemma weyl_act [CharP k 2] :
    ((rootElt k X (1 : E) * rootNegElt k X (1 : E) * rootElt k X (1 : E) :
      SpecialLinearGroup k (DSpace E X)) : DSpace E X ≃ₗ[k] DSpace E X) = swapE := by
  change rootEquiv k X 1 * rootNegEquiv k X 1 * rootEquiv k X 1 = swapE
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, x, b⟩ := v
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [LinearEquiv.mul_apply, rootEquiv, rootNegEquiv, shearE, swapE,
      LinearMap.mulLeft_apply, one_mul]
    exact char2_add1 (k := k) a b
  · rfl
  · simp only [LinearEquiv.mul_apply, rootEquiv, rootNegEquiv, shearE, swapE,
      LinearMap.mulLeft_apply, one_mul]
    exact char2_add2 (k := k) a b

private lemma toLin_transvection_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module k V] (b : Basis ι k V) (i j : ι) (c : k) (v : V) :
    Matrix.toLin b b (Matrix.transvection i j c) v = v + c • ((b.repr v j) • b i) := by
  have hmv : Matrix.mulVec (Matrix.transvection i j c) ((b.repr v : ι → k)) =
      (b.repr v : ι → k) + (c * b.repr v j) • Pi.single i (1 : k) := by
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  rw [Matrix.toLin_apply, hmv]
  simp only [Pi.add_apply, add_smul]
  rw [Finset.sum_add_distrib, Basis.sum_repr]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [smul_smul]
  · intro j' _ hj'; simp [Pi.single_apply, hj']
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma transvection_inl_inr_inl (a : Fin (Module.finrank k E))
    (x : Fin (Module.finrank k X)) (c : k) :
    Matrix.toLin (stdBasis k E X) (stdBasis k E X)
        (Matrix.transvection (Sum.inl a) (Sum.inr (Sum.inl x)) c) =
      unipElt ((c • (Module.finBasis k X).coord x).smulRight ((Module.finBasis k E) a)) 0 0 := by
  apply LinearMap.ext
  intro v
  rw [toLin_transvection_apply]
  ext <;> simp [unipElt, stdBasis, Basis.coord_apply, LinearMap.smulRight_apply, smul_smul]

private noncomputable def lowElt (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    DSpace E X ≃ₗ[k] DSpace E X :=
  swapE * unipElt φ χ ψ * swapE⁻¹

private lemma lowElt_apply (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E)
    (v : DSpace E X) :
    lowElt φ χ ψ v = (v.1, v.2.1 + χ v.1, v.2.2 + φ v.2.1 + ψ v.1) :=
  rfl

private lemma det_lowElt (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    LinearEquiv.det (lowElt φ χ ψ) = 1 := by
  rw [lowElt, map_mul, map_mul, det_unipElt]
  simp

private lemma transvection_inl_inr_inr (a b' : Fin (Module.finrank k E)) (c : k) :
    Matrix.toLin (stdBasis k E X) (stdBasis k E X)
        (Matrix.transvection (Sum.inl a) (Sum.inr (Sum.inr b')) c) =
      unipElt (X := X) 0 0
        ((c • (Module.finBasis k E).coord b').smulRight ((Module.finBasis k E) a)) := by
  apply LinearMap.ext
  intro v
  rw [toLin_transvection_apply]
  ext <;> simp [unipElt, stdBasis, Basis.coord_apply, LinearMap.smulRight_apply, smul_smul]

private lemma transvection_inr_inl_inr_inr (x : Fin (Module.finrank k X))
    (b' : Fin (Module.finrank k E)) (c : k) :
    Matrix.toLin (stdBasis k E X) (stdBasis k E X)
        (Matrix.transvection (Sum.inr (Sum.inl x)) (Sum.inr (Sum.inr b')) c) =
      unipElt (X := X) 0
        ((c • (Module.finBasis k E).coord b').smulRight ((Module.finBasis k X) x)) 0 := by
  apply LinearMap.ext
  intro v
  rw [toLin_transvection_apply]
  ext <;> simp [unipElt, stdBasis, Basis.coord_apply, LinearMap.smulRight_apply, smul_smul]

private lemma transvection_inr_inl_inl (x : Fin (Module.finrank k X))
    (a : Fin (Module.finrank k E)) (c : k) :
    Matrix.toLin (stdBasis k E X) (stdBasis k E X)
        (Matrix.transvection (Sum.inr (Sum.inl x)) (Sum.inl a) c) =
      lowElt (X := X) 0
        ((c • (Module.finBasis k E).coord a).smulRight ((Module.finBasis k X) x)) 0 := by
  apply LinearMap.ext
  intro v
  rw [toLin_transvection_apply]
  ext <;> simp [lowElt_apply, stdBasis, Basis.coord_apply, LinearMap.smulRight_apply, smul_smul]

private lemma transvection_inr_inr_inl (b' a : Fin (Module.finrank k E)) (c : k) :
    Matrix.toLin (stdBasis k E X) (stdBasis k E X)
        (Matrix.transvection (Sum.inr (Sum.inr b')) (Sum.inl a) c) =
      lowElt (X := X) 0 0
        ((c • (Module.finBasis k E).coord a).smulRight ((Module.finBasis k E) b')) := by
  apply LinearMap.ext
  intro v
  rw [toLin_transvection_apply]
  ext <;> simp [lowElt_apply, stdBasis, Basis.coord_apply, LinearMap.smulRight_apply, smul_smul]

private lemma transvection_inr_inr_inr_inl (b' : Fin (Module.finrank k E))
    (x : Fin (Module.finrank k X)) (c : k) :
    Matrix.toLin (stdBasis k E X) (stdBasis k E X)
        (Matrix.transvection (Sum.inr (Sum.inr b')) (Sum.inr (Sum.inl x)) c) =
      lowElt (X := X)
        ((c • (Module.finBasis k X).coord x).smulRight ((Module.finBasis k E) b')) 0 0 := by
  apply LinearMap.ext
  intro v
  rw [toLin_transvection_apply]
  ext <;> simp [lowElt_apply, stdBasis, Basis.coord_apply, LinearMap.smulRight_apply, smul_smul]

private lemma unipElt_sl_mem_QK (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    (⟨unipElt φ χ ψ, det_unipElt φ χ ψ⟩ : SpecialLinearGroup k (DSpace E X)) ∈ QK k E X :=
  mem_QK_iff.mpr (unipElt_mem_unipRad φ χ ψ)

private lemma lowElt_sl_mem [CharP k 2] (φ : X →ₗ[k] E) (χ : E →ₗ[k] X)
    (ψ : E →ₗ[k] E) :
    (⟨lowElt φ χ ψ, det_lowElt φ χ ψ⟩ : SpecialLinearGroup k (DSpace E X)) ∈
      QK k E X ⊔ J0SL k E X := by
  let n : SpecialLinearGroup k (DSpace E X) :=
    rootElt k X (1 : E) * rootNegElt k X (1 : E) * rootElt k X (1 : E)
  have hnJ : n ∈ J0SL k E X := by
    have h1 : rootElt k X (1 : E) ∈ J0SL k E X :=
      Subgroup.subset_closure (Or.inl ⟨1, rfl⟩)
    have h2 : rootNegElt k X (1 : E) ∈ J0SL k E X :=
      Subgroup.subset_closure (Or.inr ⟨1, rfl⟩)
    exact (J0SL k E X).mul_mem ((J0SL k E X).mul_mem h1 h2) h1
  have hnS : n ∈ QK k E X ⊔ J0SL k E X := Subgroup.mem_sup_right hnJ
  have hq : (⟨unipElt φ χ ψ, det_unipElt φ χ ψ⟩ : SpecialLinearGroup k (DSpace E X)) ∈
      QK k E X ⊔ J0SL k E X := Subgroup.mem_sup_left (unipElt_sl_mem_QK φ χ ψ)
  have h := (QK k E X ⊔ J0SL k E X).mul_mem
    ((QK k E X ⊔ J0SL k E X).mul_mem hnS hq) ((QK k E X ⊔ J0SL k E X).inv_mem hnS)
  have heq : (⟨lowElt φ χ ψ, det_lowElt φ χ ψ⟩ : SpecialLinearGroup k (DSpace E X)) =
      n * ⟨unipElt φ χ ψ, det_unipElt φ χ ψ⟩ * n⁻¹ := by
    apply Subtype.ext
    show lowElt φ χ ψ = (n : DSpace E X ≃ₗ[k] DSpace E X) *
      (unipElt φ χ ψ) * (n : DSpace E X ≃ₗ[k] DSpace E X)⁻¹
    rw [show (n : DSpace E X ≃ₗ[k] DSpace E X) = swapE from weyl_act]
    rfl
  rw [heq]
  exact h

private lemma slTransvection_coe_eq {i j : Fin (Module.finrank k E) ⊕
    (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))} (hij : i ≠ j) (c : k)
    (u : DSpace E X ≃ₗ[k] DSpace E X)
    (h : Matrix.toLin (stdBasis k E X) (stdBasis k E X) (Matrix.transvection i j c) = u) :
    ((slIso k E X) (Matrix.SpecialLinearGroup.transvection hij c) :
      DSpace E X ≃ₗ[k] DSpace E X) = u := by
  apply LinearEquiv.toLinearMap_injective
  change Matrix.toLin (stdBasis k E X) (stdBasis k E X) (Matrix.transvection i j c) = u
  exact h

private lemma slTransvection_mem_QK {i j : Fin (Module.finrank k E) ⊕
    (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))} (hij : i ≠ j) (c : k)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E)
    (h : Matrix.toLin (stdBasis k E X) (stdBasis k E X) (Matrix.transvection i j c) =
      unipElt φ χ ψ) :
    (slIso k E X) (Matrix.SpecialLinearGroup.transvection hij c) ∈ QK k E X := by
  rw [mem_QK_iff, slTransvection_coe_eq hij c (unipElt φ χ ψ) h]
  exact unipElt_mem_unipRad φ χ ψ

private lemma slTransvection_mem_sup_low [CharP k 2] {i j : Fin (Module.finrank k E) ⊕
    (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))} (hij : i ≠ j) (c : k)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E)
    (h : Matrix.toLin (stdBasis k E X) (stdBasis k E X) (Matrix.transvection i j c) =
      lowElt φ χ ψ) :
    (slIso k E X) (Matrix.SpecialLinearGroup.transvection hij c) ∈ QK k E X ⊔ J0SL k E X := by
  convert lowElt_sl_mem φ χ ψ using 1
  exact Subtype.ext (slTransvection_coe_eq hij c (lowElt φ χ ψ) h)

private lemma commutator_mem_of_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

end GenerationAux

variable [Finite k] [Finite E] [Module.Finite k X] [CharP k 2] in
theorem QK_sup_J0SL_eq_top (hdX : Module.finrank k E ≤ Module.finrank k X) :
    QK k E X ⊔ J0SL k E X = ⊤ := by
  classical
  let e := slIso k E X
  let S : Subgroup (SpecialLinearGroup k (DSpace E X)) := QK k E X ⊔ J0SL k E X
  have hd : 0 < Module.finrank k E := Module.finrank_pos
  have hr : 0 < Module.finrank k X := lt_of_lt_of_le hd hdX
  have htrans : ∀ (i j : Fin (Module.finrank k E) ⊕
      (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E)))
      (hij : i ≠ j) (c : k), e (Matrix.SpecialLinearGroup.transvection hij c) ∈ S := by
    intro i j hij c
    rcases i with a | (x | b') <;> rcases j with a' | (x' | b'')
    ·
      let x₀ : Fin (Module.finrank k X) := ⟨0, hr⟩
      have hij1 : (Sum.inl a : Fin (Module.finrank k E) ⊕
          (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) ≠ Sum.inr (Sum.inl x₀) := by
        simp
      have hjk1 : (Sum.inr (Sum.inl x₀) : Fin (Module.finrank k E) ⊕
          (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) ≠ Sum.inl a' := by
        simp
      have hcomm := CFSG.ClassicalGroups.SpecialLinear.steinberg_commutator
        (i := Sum.inl a) (j := Sum.inr (Sum.inl x₀)) (k := Sum.inl a') hij1 hjk1 hij c (1 : k)
      simp only [mul_one] at hcomm
      have heq : e (Matrix.SpecialLinearGroup.transvection hij c) =
          ⁅e (Matrix.SpecialLinearGroup.transvection hij1 c),
            e (Matrix.SpecialLinearGroup.transvection hjk1 (1 : k))⁆ := by
        rw [← hcomm]
        exact map_commutatorElement (f := e.toMonoidHom) _ _
      rw [heq]
      exact commutator_mem_of_mem
        (Subgroup.mem_sup_left
          (slTransvection_mem_QK hij1 c _ 0 0 (transvection_inl_inr_inl a x₀ c)))
        (slTransvection_mem_sup_low hjk1 (1 : k) _ _ _
          (transvection_inr_inl_inl x₀ a' (1 : k)))
    ·
      exact Subgroup.mem_sup_left
        (slTransvection_mem_QK hij c _ 0 0 (transvection_inl_inr_inl a x' c))
    ·
      exact Subgroup.mem_sup_left
        (slTransvection_mem_QK hij c _ _ _ (transvection_inl_inr_inr a b'' c))
    ·
      exact slTransvection_mem_sup_low hij c _ _ _ (transvection_inr_inl_inl x a' c)
    ·
      let a₀ : Fin (Module.finrank k E) := ⟨0, hd⟩
      have hik : (Sum.inr (Sum.inl x) : Fin (Module.finrank k E) ⊕
          (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) ≠ Sum.inl a₀ := by
        simp
      have hkj : (Sum.inl a₀ : Fin (Module.finrank k E) ⊕
          (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) ≠ Sum.inr (Sum.inl x') := by
        simp
      have hcomm := CFSG.ClassicalGroups.SpecialLinear.steinberg_commutator
        (i := Sum.inr (Sum.inl x)) (j := Sum.inl a₀) (k := Sum.inr (Sum.inl x')) hik hkj hij c
        (1 : k)
      simp only [mul_one] at hcomm
      have heq : e (Matrix.SpecialLinearGroup.transvection hij c) =
          ⁅e (Matrix.SpecialLinearGroup.transvection hik c),
            e (Matrix.SpecialLinearGroup.transvection hkj (1 : k))⁆ := by
        rw [← hcomm]
        exact map_commutatorElement (f := e.toMonoidHom) _ _
      rw [heq]
      exact commutator_mem_of_mem
        (slTransvection_mem_sup_low hik c _ _ _ (transvection_inr_inl_inl x a₀ c))
        (Subgroup.mem_sup_left
          (slTransvection_mem_QK hkj (1 : k) _ 0 0 (transvection_inl_inr_inl a₀ x' (1 : k))))
    ·
      exact Subgroup.mem_sup_left
        (slTransvection_mem_QK hij c _ _ _ (transvection_inr_inl_inr_inr x b'' c))
    ·
      exact slTransvection_mem_sup_low hij c _ _ _ (transvection_inr_inr_inl b' a' c)
    ·
      exact slTransvection_mem_sup_low hij c _ _ _ (transvection_inr_inr_inr_inl b' x' c)
    ·
      let x₀ : Fin (Module.finrank k X) := ⟨0, hr⟩
      have hik : (Sum.inr (Sum.inr b') : Fin (Module.finrank k E) ⊕
          (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) ≠ Sum.inr (Sum.inl x₀) := by
        simp
      have hkj : (Sum.inr (Sum.inl x₀) : Fin (Module.finrank k E) ⊕
          (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) ≠ Sum.inr (Sum.inr b'') := by
        simp
      have hcomm := CFSG.ClassicalGroups.SpecialLinear.steinberg_commutator
        (i := Sum.inr (Sum.inr b')) (j := Sum.inr (Sum.inl x₀)) (k := Sum.inr (Sum.inr b''))
        hik hkj hij c (1 : k)
      simp only [mul_one] at hcomm
      have heq : e (Matrix.SpecialLinearGroup.transvection hij c) =
          ⁅e (Matrix.SpecialLinearGroup.transvection hik c),
            e (Matrix.SpecialLinearGroup.transvection hkj (1 : k))⁆ := by
        rw [← hcomm]
        exact map_commutatorElement (f := e.toMonoidHom) _ _
      rw [heq]
      exact commutator_mem_of_mem
        (slTransvection_mem_sup_low hik c _ _ _ (transvection_inr_inr_inr_inl b' x₀ c))
        (Subgroup.mem_sup_left
          (slTransvection_mem_QK hkj (1 : k) _ _ _
            (transvection_inr_inl_inr_inr x₀ b'' (1 : k))))
  haveI : Nontrivial (Fin (Module.finrank k E) ⊕
      (Fin (Module.finrank k X) ⊕ Fin (Module.finrank k E))) :=
    ⟨Sum.inl ⟨0, hd⟩, Sum.inr (Sum.inl ⟨0, hr⟩), by simp⟩
  have hmap : S.map e.symm.toMonoidHom = ⊤ := by
    apply CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem
    intro i j hij c
    rw [Subgroup.mem_map]
    exact ⟨e (Matrix.SpecialLinearGroup.transvection hij c), htrans i j hij c, by simp⟩
  have hS : S = ⊤ :=
    Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
      (hmap.trans (Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective).symm)
  exact hS

end CFSG.LinearAlgebra.RootGroupSL
