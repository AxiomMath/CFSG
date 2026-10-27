module

public import CFSG.LocalAnalysis.ComponentInitial.LinearDoubleSL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearPairedCentralizer
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

variable {k : Type*} [Field k]

section Form

variable (k) (m : ℕ)

@[expose] def pairedSympForm : LinearMap.BilinForm k (Fin m ⊕ Fin m → k) :=
  Matrix.toBilin' (fromBlocks 0 1 (-1) 0)

@[expose] def pairedSymplecticGroup : Subgroup (GL (Fin m ⊕ Fin m) k) where
  carrier := {A | ∀ u v, pairedSympForm k m (A.val *ᵥ u) (A.val *ᵥ v) = pairedSympForm k m u v}
  one_mem' u v := by simp
  mul_mem' {A B} hA hB u v := by
    change pairedSympForm k m ((A * B).val *ᵥ u) ((A * B).val *ᵥ v) = _
    rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hA, hB]
  inv_mem' {A} hA u v := by
    have h := hA ((A⁻¹).val *ᵥ u) ((A⁻¹).val *ᵥ v)
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec, one_mulVec] at h
    exact h.symm

variable {k m}

theorem mem_pairedSymplecticGroup {A : GL (Fin m ⊕ Fin m) k} :
    A ∈ pairedSymplecticGroup k m ↔
      ∀ u v, pairedSympForm k m (A.val *ᵥ u) (A.val *ᵥ v) = pairedSympForm k m u v :=
  Iff.rfl

theorem pairedSympForm_apply (u v : Fin m ⊕ Fin m → k) :
    pairedSympForm k m u v =
      (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr) - (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inl) := by
  simp [pairedSympForm, toBilin'_apply', dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec,
    sub_eq_add_neg, neg_mulVec, Finset.sum_neg_distrib]

theorem pairedSympForm_self (u : Fin m ⊕ Fin m → k) : pairedSympForm k m u u = 0 := by
  rw [pairedSympForm_apply, dotProduct_comm, sub_self]

theorem mulVec_dotProduct_mulVec_eq (X Y : Matrix (Fin m) (Fin m) k) (a b : Fin m → k) :
    (X *ᵥ a) ⬝ᵥ (Y *ᵥ b) = a ⬝ᵥ ((Xᵀ * Y) *ᵥ b) := by
  conv_rhs => rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

theorem pairedSympForm_fromBlocks (X Y : Matrix (Fin m) (Fin m) k) (u v : Fin m ⊕ Fin m → k) :
    pairedSympForm k m (fromBlocks X 0 0 Y *ᵥ u) (fromBlocks X 0 0 Y *ᵥ v) =
      (u ∘ Sum.inl) ⬝ᵥ ((Xᵀ * Y) *ᵥ (v ∘ Sum.inr)) -
        (u ∘ Sum.inr) ⬝ᵥ ((Yᵀ * X) *ᵥ (v ∘ Sum.inl)) := by
  rw [pairedSympForm_apply]
  simp only [fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl,
    Sum.elim_comp_inr, mulVec_dotProduct_mulVec_eq]

theorem pairedSympForm_fromBlocks_of_transpose_mul {X Y : Matrix (Fin m) (Fin m) k}
    (h : Xᵀ * Y = 1) (u v : Fin m ⊕ Fin m → k) :
    pairedSympForm k m (fromBlocks X 0 0 Y *ᵥ u) (fromBlocks X 0 0 Y *ᵥ v) =
      pairedSympForm k m u v := by
  have h' : Yᵀ * X = 1 := by
    rw [← transpose_transpose X, ← transpose_mul, h, transpose_one]
  rw [pairedSympForm_fromBlocks, h, h', one_mulVec, one_mulVec, pairedSympForm_apply]

theorem pairedSympForm_smul_one (a b : k) (u v : Fin m ⊕ Fin m → k) :
    pairedSympForm k m (fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) *ᵥ u)
      (fromBlocks (a • (1 : Matrix (Fin m) (Fin m) k)) 0 0 (b • 1) *ᵥ v) =
      a * b * pairedSympForm k m u v := by
  rw [pairedSympForm_fromBlocks, pairedSympForm_apply]
  simp only [transpose_smul, transpose_one, smul_mul_smul_comm, mul_one, smul_mulVec, one_mulVec,
    dotProduct_smul, smul_eq_mul]
  ring

theorem pairedSympForm_single (i : Fin m) :
    pairedSympForm k m (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1) = 1 := by
  rw [pairedSympForm_apply]
  simp [dotProduct, Pi.single_apply]

theorem pairedSLHom_range_le_pairedSymplecticGroup :
    (pairedSLHom (RingHom.id k) m).range ≤ pairedSymplecticGroup k m := by
  rintro _ ⟨g, rfl⟩ u v
  rw [pairedSLHom_id_coe]
  refine pairedSympForm_fromBlocks_of_transpose_mul ?_ u v
  rw [← transpose_mul, coe_inv_mul_coe_SL, transpose_one]

theorem pairedSymplectic_centralizer_eq (hm : 3 ≤ m) :
    (Subgroup.centralizer (((pairedSLHom (RingHom.id k) m).range.subgroupOf
        (pairedSymplecticGroup k m)) : Set (pairedSymplecticGroup k m)) :
        Set (pairedSymplecticGroup k m)) =
      {x : pairedSymplecticGroup k m | ∃ a : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((a : k)⁻¹ • 1)} := by
  have hle := pairedSLHom_range_le_pairedSymplecticGroup (k := k) (m := m)
  ext x
  constructor
  · intro hx
    have hGL : (x : GL (Fin m ⊕ Fin m) k) ∈
        Subgroup.centralizer ((pairedSLHom (RingHom.id k) m).range :
          Set (GL (Fin m ⊕ Fin m) k)) := by
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact congrArg Subtype.val (hx ⟨d, hle hd⟩ (Subgroup.mem_subgroupOf.mpr hd))
    obtain ⟨a, b, hab⟩ : ∃ a b : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((b : k) • 1) := by
      have h := (paired_special_linear_geq_three_linear_centralizer (k := k) hm).1
      rw [Set.ext_iff] at h
      exact (h x).mp hGL
    let i₀ : Fin m := ⟨0, by omega⟩
    have h := (mem_pairedSymplecticGroup.mp x.2) (Pi.single (Sum.inl i₀) 1)
      (Pi.single (Sum.inr i₀) 1)
    rw [hab, pairedSympForm_smul_one, pairedSympForm_single, mul_one] at h
    refine ⟨a, ?_⟩
    rw [hab, eq_inv_of_mul_eq_one_right h]
  · rintro ⟨a, hx⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro d hd
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hd
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hx, ← hg, pairedSLHom_coe]
    exact fromBlocks_smul_one_commute _ _ _ _

theorem pairedSympForm_nondegenerate : (pairedSympForm k m).Nondegenerate := by
  refine ⟨fun u hu => ?_, fun v hv => ?_⟩
  · funext i
    rcases i with i | i
    · have h := hu (Pi.single (Sum.inr i) 1)
      rw [pairedSympForm_apply] at h
      simpa [dotProduct, Pi.single_apply] using h
    · have h := hu (Pi.single (Sum.inl i) 1)
      rw [pairedSympForm_apply] at h
      simpa [dotProduct, Pi.single_apply] using h
  · funext i
    rcases i with i | i
    · have h := hv (Pi.single (Sum.inr i) 1)
      rw [pairedSympForm_apply] at h
      simpa [dotProduct, Pi.single_apply] using h
    · have h := hv (Pi.single (Sum.inl i) 1)
      rw [pairedSympForm_apply] at h
      simpa [dotProduct, Pi.single_apply] using h

end Form

section Two

@[expose] def pairedSympTwoEquiv : ((Fin 2 → k) × (Fin 2 → k)) ≃ₗ[k] (Fin 2 ⊕ Fin 2 → k) where
  toFun p := Sum.elim ![p.1 0, p.2 0] ![p.2 1, -p.1 1]
  map_add' p q := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [add_comm]
  map_smul' c p := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp
  invFun v := (![v (Sum.inl 0), -v (Sum.inr 1)], ![v (Sum.inl 1), v (Sum.inr 0)])
  left_inv p := by
    ext i <;> fin_cases i <;> simp
  right_inv v := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp

theorem pairedSympTwoEquiv_doubleNaturalSL2 (g : SpecialLinearGroup (Fin 2) k)
    (p : (Fin 2 → k) × (Fin 2 → k)) :
    pairedSympTwoEquiv ((doubleNaturalSL2 (W := Fin 2 → k) g :
        (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) p) =
      (pairedSLHom (RingHom.id k) 2 g).val *ᵥ pairedSympTwoEquiv p := by
  obtain ⟨x, y⟩ := p
  rw [pairedSLHom_id_coe, SpecialLinearGroup.coe_inv, adjugate_fin_two]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [pairedSympTwoEquiv, mulVec, dotProduct, Fin.sum_univ_two]
  ring

@[expose] def pairedSympTwoConj :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k →* Module.End k ((Fin 2 → k) × (Fin 2 → k)) where
  toFun M := pairedSympTwoEquiv.symm.toLinearMap ∘ₗ M.mulVecLin ∘ₗ pairedSympTwoEquiv.toLinearMap
  map_one' := LinearMap.ext fun p => by simp
  map_mul' M N := LinearMap.ext fun p => by simp [mulVec_mulVec]

theorem pairedSympTwoConj_apply (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)
    (p : (Fin 2 → k) × (Fin 2 → k)) :
    pairedSympTwoConj M p = pairedSympTwoEquiv.symm (M *ᵥ pairedSympTwoEquiv p) :=
  rfl

@[expose] def pairedSympTwoGL :
    GL (Fin 2 ⊕ Fin 2) k →* LinearMap.GeneralLinearGroup k ((Fin 2 → k) × (Fin 2 → k)) :=
  Units.map pairedSympTwoConj

theorem pairedSympTwoGL_apply (A : GL (Fin 2 ⊕ Fin 2) k) (p : (Fin 2 → k) × (Fin 2 → k)) :
    (pairedSympTwoGL A : (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) p =
      pairedSympTwoEquiv.symm (A.val *ᵥ pairedSympTwoEquiv p) :=
  rfl

theorem pairedSympTwoGL_injective : Function.Injective (pairedSympTwoGL (k := k)) := by
  intro A B h
  have h' : ∀ v, A.val *ᵥ v = B.val *ᵥ v := fun v => by
    have := congrArg (fun u : LinearMap.GeneralLinearGroup k ((Fin 2 → k) × (Fin 2 → k)) =>
      (u : (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k))
        (pairedSympTwoEquiv.symm v)) h
    simpa only [pairedSympTwoGL_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_eq] using this
  exact Units.ext (ext_of_mulVec_single fun i => h' _)

theorem pairedSympTwoGL_pairedSLHom (g : SpecialLinearGroup (Fin 2) k) :
    pairedSympTwoGL (pairedSLHom (RingHom.id k) 2 g) = doubleNaturalSL2 (W := Fin 2 → k) g := by
  refine Units.ext (LinearMap.ext fun p => ?_)
  change pairedSympTwoEquiv.symm ((pairedSLHom (RingHom.id k) 2 g).val *ᵥ pairedSympTwoEquiv p) =
    _
  rw [← pairedSympTwoEquiv_doubleNaturalSL2, LinearEquiv.symm_apply_apply]

@[expose] def pairedSympTwoForm : LinearMap.BilinForm k ((Fin 2 → k) × (Fin 2 → k)) :=
  (pairedSympForm k 2).compl₁₂ pairedSympTwoEquiv.toLinearMap pairedSympTwoEquiv.toLinearMap

theorem pairedSympTwoForm_apply (p q : (Fin 2 → k) × (Fin 2 → k)) :
    pairedSympTwoForm p q = pairedSympForm k 2 (pairedSympTwoEquiv p) (pairedSympTwoEquiv q) :=
  rfl

theorem isSolvable_pairedSymplectic_centralizer_two (hk : ringChar k ≠ 2) :
    Group.IsSolvable (Subgroup.centralizer (((pairedSLHom (RingHom.id k) 2).range.subgroupOf
      (pairedSymplecticGroup k 2)) : Set (pairedSymplecticGroup k 2))) := by
  have hle := pairedSLHom_range_le_pairedSymplecticGroup (k := k) (m := 2)
  have hinv : ∀ (g : SpecialLinearGroup (Fin 2) k) (u v : (Fin 2 → k) × (Fin 2 → k)),
      pairedSympTwoForm ((doubleNaturalSL2 (W := Fin 2 → k) g :
          (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) u)
        ((doubleNaturalSL2 (W := Fin 2 → k) g :
          (Fin 2 → k) × (Fin 2 → k) →ₗ[k] (Fin 2 → k) × (Fin 2 → k)) v) =
        pairedSympTwoForm u v := by
    intro g u v
    rw [pairedSympTwoForm_apply, pairedSympTwoForm_apply, pairedSympTwoEquiv_doubleNaturalSL2,
      pairedSympTwoEquiv_doubleNaturalSL2]
    exact hle ⟨g, rfl⟩ _ _
  have halt : (pairedSympTwoForm (k := k)).IsAlt := fun p => pairedSympForm_self _
  have hnd : (pairedSympTwoForm (k := k)).Nondegenerate := by
    refine ⟨fun p hp => ?_, fun q hq => ?_⟩
    · refine pairedSympTwoEquiv.injective ?_
      rw [map_zero]
      refine pairedSympForm_nondegenerate.1 _ fun v => ?_
      have h := hp (pairedSympTwoEquiv.symm v)
      rwa [pairedSympTwoForm_apply, LinearEquiv.apply_symm_apply] at h
    · refine pairedSympTwoEquiv.injective ?_
      rw [map_zero]
      refine pairedSympForm_nondegenerate.2 _ fun u => ?_
      have h := hq (pairedSympTwoEquiv.symm u)
      rwa [pairedSympTwoForm_apply, LinearEquiv.apply_symm_apply] at h
  have hW : Module.finrank k (Fin 2 → k) = 2 := Module.finrank_fin_fun k
  have := double_natural_SL2_symplectic_centralizer_solvable hk hW pairedSympTwoForm hnd halt hinv
  have hiso : ∀ x : pairedSymplecticGroup k 2, pairedSympTwoGL (x : GL (Fin 2 ⊕ Fin 2) k) ∈
      bilinIsometryGroup (pairedSympTwoForm (k := k)) :=
    fun x => mem_bilinIsometryGroup.mpr fun p q => by
      rw [pairedSympTwoGL_apply, pairedSympTwoGL_apply, pairedSympTwoForm_apply,
        pairedSympTwoForm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact (mem_pairedSymplecticGroup.mp x.2) _ _
  let f₀ : pairedSymplecticGroup k 2 →* bilinIsometryGroup (pairedSympTwoForm (k := k)) :=
    (pairedSympTwoGL.comp (pairedSymplecticGroup k 2).subtype).codRestrict _ hiso
  have hf₀ : Function.Injective f₀ := fun x y h =>
    Subtype.ext (pairedSympTwoGL_injective (congrArg Subtype.val h))
  have hcent : ∀ x ∈ Subgroup.centralizer (((pairedSLHom (RingHom.id k) 2).range.subgroupOf
      (pairedSymplecticGroup k 2)) : Set (pairedSymplecticGroup k 2)),
      f₀ x ∈ Subgroup.centralizer
        (((doubleNaturalSL2 (k := k) (W := Fin 2 → k)).range.subgroupOf
          (bilinIsometryGroup pairedSympTwoForm)) :
          Set (bilinIsometryGroup (pairedSympTwoForm (k := k)))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro h hh
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hh
    have hd : (⟨pairedSLHom (RingHom.id k) 2 g, hle ⟨g, rfl⟩⟩ : pairedSymplecticGroup k 2) ∈
        ((pairedSLHom (RingHom.id k) 2).range.subgroupOf (pairedSymplecticGroup k 2)) :=
      Subgroup.mem_subgroupOf.mpr ⟨g, rfl⟩
    have hfd : f₀ ⟨pairedSLHom (RingHom.id k) 2 g, hle ⟨g, rfl⟩⟩ = h :=
      Subtype.ext ((pairedSympTwoGL_pairedSLHom g).trans hg)
    rw [← hfd, ← map_mul, ← map_mul, hx _ hd]
  let f := (f₀.comp (Subgroup.centralizer (((pairedSLHom (RingHom.id k) 2).range.subgroupOf
      (pairedSymplecticGroup k 2)) : Set (pairedSymplecticGroup k 2))).subtype).codRestrict _
    fun x => hcent x x.2
  exact Group.isSolvable_of_isSolvable_injective (f := f) fun x y h =>
    Subtype.ext (hf₀ (congrArg Subtype.val h))

end Two

variable {m : ℕ}

theorem isSolvable_pairedSymplectic_centralizer_of_three_le (hm : 3 ≤ m) :
    Group.IsSolvable (Subgroup.centralizer (((pairedSLHom (RingHom.id k) m).range.subgroupOf
      (pairedSymplecticGroup k m)) : Set (pairedSymplecticGroup k m))) := by
  have hset := pairedSymplectic_centralizer_eq (k := k) hm
  have hform : ∀ x : Subgroup.centralizer (((pairedSLHom (RingHom.id k) m).range.subgroupOf
      (pairedSymplecticGroup k m)) : Set (pairedSymplecticGroup k m)), ∃ a : kˣ,
      ((x : pairedSymplecticGroup k m) : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((a : k)⁻¹ • 1) := fun x => by
    have h := x.2
    rw [← SetLike.mem_coe, hset] at h
    exact h
  refine Group.isSolvable_of_comm fun x y => ?_
  obtain ⟨a, hx⟩ := hform x
  obtain ⟨b, hy⟩ := hform y
  refine Subtype.ext (Subtype.ext (Units.ext ?_))
  simp only [Subgroup.coe_mul, Units.val_mul, hx, hy, fromBlocks_multiply]
  simp [smul_smul, mul_comm]

theorem pairedSymplectic_centralizer_solvable (hk : ringChar k ≠ 2) (hm : 2 ≤ m) :
    (pairedSLHom (RingHom.id k) m).range ≤ pairedSymplecticGroup k m ∧
    Group.IsSolvable (Subgroup.centralizer
      (((pairedSLHom (RingHom.id k) m).range.subgroupOf (pairedSymplecticGroup k m)) :
        Set (pairedSymplecticGroup k m))) ∧
    (3 ≤ m → (Subgroup.centralizer
      (((pairedSLHom (RingHom.id k) m).range.subgroupOf (pairedSymplecticGroup k m)) :
        Set (pairedSymplecticGroup k m)) : Set (pairedSymplecticGroup k m)) =
      {x : pairedSymplecticGroup k m | ∃ a : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((a : k)⁻¹ • 1)}) := by
  refine ⟨pairedSLHom_range_le_pairedSymplecticGroup, ?_, pairedSymplectic_centralizer_eq⟩
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · exact isSolvable_pairedSymplectic_centralizer_two hk
  · exact isSolvable_pairedSymplectic_centralizer_of_three_le hm3

theorem paired_symplectic_special_linear_centralizer_solvable [Finite k] (hk : ringChar k ≠ 2)
    (hm : 2 ≤ m) :
    (pairedSLHom (RingHom.id k) m).range ≤ pairedSymplecticGroup k m ∧
    Group.IsSolvable (Subgroup.centralizer
      (((pairedSLHom (RingHom.id k) m).range.subgroupOf (pairedSymplecticGroup k m)) :
        Set (pairedSymplecticGroup k m))) ∧
    (3 ≤ m → (Subgroup.centralizer
      (((pairedSLHom (RingHom.id k) m).range.subgroupOf (pairedSymplecticGroup k m)) :
        Set (pairedSymplecticGroup k m)) : Set (pairedSymplecticGroup k m)) =
      {x : pairedSymplecticGroup k m | ∃ a : kˣ, (x : GL (Fin m ⊕ Fin m) k).val =
        fromBlocks ((a : k) • (1 : Matrix (Fin m) (Fin m) k)) 0 0 ((a : k)⁻¹ • 1)}) :=
  pairedSymplectic_centralizer_solvable hk hm

end CFSG.LocalAnalysis.ComponentInitial
