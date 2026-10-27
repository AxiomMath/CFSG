module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalStar
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplit
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCModel

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ComponentClassification
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Star

variable {F : Type} [Field F] {m : ℕ}

@[expose] noncomputable def spStar (F : Type) [Field F] (m : ℕ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F →ₗ[F] Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F where
  toFun M := -(gram F m * Mᵀ * gram F m)
  map_add' a b := by
    simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]
  map_smul' c a := by
    simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply,
      smul_neg]

theorem spStar_apply (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    spStar F m M = -(gram F m * Mᵀ * gram F m) := rfl

theorem spStar_mul (a b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    spStar F m (a * b) = spStar F m b * spStar F m a := by
  have hJ : gram F m * gram F m = -1 := gram_mul_gram
  simp only [spStar_apply, Matrix.transpose_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  calc -(gram F m * (bᵀ * aᵀ) * gram F m)
      = gram F m * bᵀ * (-(1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F)) * aᵀ * gram F m := by
        noncomm_ring
    _ = gram F m * bᵀ * (gram F m * gram F m) * aᵀ * gram F m := by rw [hJ]
    _ = gram F m * bᵀ * gram F m * (gram F m * aᵀ * gram F m) := by noncomm_ring

theorem spStar_mat_mul (x : StatedSp m F) : spStar F m (mat m F x) * mat m F x = 1 := by
  have hJ : gram F m * gram F m = -1 := gram_mul_gram
  have h := mat_transpose_mul_gram_mul x
  rw [spStar_apply, Matrix.neg_mul]
  calc -(gram F m * (mat m F x)ᵀ * gram F m * mat m F x)
      = -(gram F m * ((mat m F x)ᵀ * gram F m * mat m F x)) := by noncomm_ring
    _ = 1 := by rw [h, hJ, neg_neg]

end Star

section Involution

variable {F : Type} [Field F] {m : ℕ}

theorem spStar_one : spStar F m (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) = 1 := by
  have hJ : gram F m * gram F m = -1 := gram_mul_gram
  rw [spStar_apply, Matrix.transpose_one, Matrix.mul_one, hJ, neg_neg]

theorem symp_of_spStar {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F}
    (h : spStar F m M * M = 1) : Mᵀ * gram F m * M = gram F m := by
  have hJ : gram F m * gram F m = -1 := gram_mul_gram
  rw [spStar_apply] at h
  have hX : gram F m * (Mᵀ * gram F m * M) = -1 := by
    have h' : -(gram F m * (Mᵀ * gram F m * M)) = 1 := by
      calc -(gram F m * (Mᵀ * gram F m * M)) = -(gram F m * Mᵀ * gram F m) * M := by noncomm_ring
        _ = 1 := h
    exact neg_eq_iff_eq_neg.mp h'
  calc Mᵀ * gram F m * M = (-(gram F m * gram F m)) * (Mᵀ * gram F m * M) := by
        rw [hJ, neg_neg, Matrix.one_mul]
    _ = -(gram F m * (gram F m * (Mᵀ * gram F m * M))) := by noncomm_ring
    _ = gram F m := by rw [hX]; simp

variable {z : StatedSp m F}

theorem mat_mul_self_of_mul_self (hz : z * z = 1) : mat m F z * mat m F z = 1 := by
  rw [← map_mul, hz, map_one]

theorem spStar_mat_of_mul_self (hz : z * z = 1) : spStar F m (mat m F z) = mat m F z := by
  have h1 := spStar_mat_mul z
  have hD := mat_mul_self_of_mul_self hz
  calc spStar F m (mat m F z) = spStar F m (mat m F z) * (mat m F z * mat m F z) := by
        rw [hD, Matrix.mul_one]
    _ = (spStar F m (mat m F z) * mat m F z) * mat m F z := (Matrix.mul_assoc _ _ _).symm
    _ = mat m F z := by rw [h1, Matrix.one_mul]

theorem spStar_eMinus (hz : z * z = 1) :
    spStar F m (eMinus (mat m F z)) = eMinus (mat m F z) := by
  unfold eMinus
  rw [map_smul, map_sub, spStar_one, spStar_mat_of_mul_self hz]

theorem spStar_ePlus (hz : z * z = 1) :
    spStar F m (ePlus (mat m F z)) = ePlus (mat m F z) := by
  unfold ePlus
  rw [map_smul, map_add, spStar_one, spStar_mat_of_mul_self hz]

end Involution

section Groups

variable {F : Type} [Field F] {m : ℕ} {z : StatedSp m F}

theorem mem_longRootGroup_iff_mat (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : StatedSp m F} :
    x ∈ longRootGroup z ↔ mat m F x * ePlus (mat m F z) = ePlus (mat m F z) := by
  have hD := mat_mul_self_of_mul_self hz
  constructor
  · intro hx
    ext r c
    have hmem : ∀ w, ePlus (mat m F z) *ᵥ w ∈ fixSpace z := fun w => by
      rw [mem_fixSpace, Matrix.mulVec_mulVec, mul_ePlus hD]
    have h1 := hx _ (hmem (Pi.single c 1))
    have e1 : (mat m F x * ePlus (mat m F z)) r c =
        (mat m F x *ᵥ (ePlus (mat m F z) *ᵥ Pi.single c 1)) r := by
      rw [Matrix.mulVec_mulVec, mulVec_single_one_apply]
    have e2 : ePlus (mat m F z) r c = (ePlus (mat m F z) *ᵥ Pi.single c (1 : F)) r :=
      (mulVec_single_one_apply _ c r).symm
    rw [e1, h1, ← e2]
  · intro hx v hv
    have hv' : ePlus (mat m F z) *ᵥ v = v := ePlus_mulVec_of_mulVec_eq h2 (mem_fixSpace.mp hv)
    calc mat m F x *ᵥ v = mat m F x *ᵥ (ePlus (mat m F z) *ᵥ v) := by rw [hv']
      _ = (mat m F x * ePlus (mat m F z)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [hx, hv']

theorem mem_complGroup_iff_mat (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : StatedSp m F} :
    x ∈ complGroup z ↔ mat m F x * eMinus (mat m F z) = eMinus (mat m F z) := by
  have hD := mat_mul_self_of_mul_self hz
  constructor
  · intro hx
    ext r c
    have hmem : ∀ w, eMinus (mat m F z) *ᵥ w ∈ minusSpace z := fun w => by
      rw [mem_minusSpace, Matrix.mulVec_mulVec, mul_eMinus hD, Matrix.neg_mulVec]
    have h1 := hx _ (hmem (Pi.single c 1))
    have e1 : (mat m F x * eMinus (mat m F z)) r c =
        (mat m F x *ᵥ (eMinus (mat m F z) *ᵥ Pi.single c 1)) r := by
      rw [Matrix.mulVec_mulVec, mulVec_single_one_apply]
    have e2 : eMinus (mat m F z) r c = (eMinus (mat m F z) *ᵥ Pi.single c (1 : F)) r :=
      (mulVec_single_one_apply _ c r).symm
    rw [e1, h1, ← e2]
  · intro hx v hv
    have hv' : eMinus (mat m F z) *ᵥ v = v := eMinus_mulVec_of_mulVec_eq h2 (mem_minusSpace.mp hv)
    calc mat m F x *ᵥ v = mat m F x *ᵥ (eMinus (mat m F z) *ᵥ v) := by rw [hv']
      _ = (mat m F x * eMinus (mat m F z)) *ᵥ v := by rw [Matrix.mulVec_mulVec]
      _ = v := by rw [hx, hv']

theorem comm_of_mem_longRootGroup (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : StatedSp m F}
    (hx : x ∈ longRootGroup z) : x * z = z * x := by
  have hxe := (mem_longRootGroup_iff_mat h2 hz).mp hx
  have h1 : ePlus (mat m F z) * mat m F x = ePlus (mat m F z) :=
    fixes_comm (spStar F m).toAddMonoidHom (fun a b => spStar_mul a b) (spStar_ePlus hz) hxe
      (spStar_mat_mul x)
  have h3 : mat m F x * ePlus (mat m F z) = ePlus (mat m F z) * mat m F x := by rw [hxe, h1]
  apply mat_injective
  rw [map_mul, map_mul]
  exact commute_of_commute_ePlus h2 h3

theorem comm_of_mem_complGroup (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : StatedSp m F}
    (hx : x ∈ complGroup z) : x * z = z * x := by
  have hxe := (mem_complGroup_iff_mat h2 hz).mp hx
  have h1 : eMinus (mat m F z) * mat m F x = eMinus (mat m F z) :=
    fixes_comm (spStar F m).toAddMonoidHom (fun a b => spStar_mul a b) (spStar_eMinus hz) hxe
      (spStar_mat_mul x)
  have h3 : mat m F x * eMinus (mat m F z) = eMinus (mat m F z) * mat m F x := by rw [hxe, h1]
  apply mat_injective
  rw [map_mul, map_mul]
  exact commute_of_commute_eMinus h2 h3

theorem mat_eq_of_mem_longRootGroup (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : StatedSp m F}
    (hx : x ∈ longRootGroup z) :
    mat m F x = eMinus (mat m F z) * mat m F x * eMinus (mat m F z) + ePlus (mat m F z) := by
  have hD := mat_mul_self_of_mul_self hz
  have hxD : mat m F x * mat m F z = mat m F z * mat m F x := by
    rw [← map_mul, ← map_mul, comm_of_mem_longRootGroup h2 hz hx]
  have hxf := (mem_longRootGroup_iff_mat h2 hz).mp hx
  have hfx : ePlus (mat m F z) * mat m F x = ePlus (mat m F z) :=
    fixes_comm (spStar F m).toAddMonoidHom (fun a b => spStar_mul a b) (spStar_ePlus hz) hxf
      (spStar_mat_mul x)
  have key := eq_add_of_commute (eMinus_add_ePlus h2) (eMinus_mul_ePlus hD) (ePlus_mul_eMinus hD)
    (commute_eMinus' hxD) (commute_ePlus' hxD)
  have hff := idem_right (eMinus_add_ePlus h2) (ePlus_mul_eMinus hD)
  conv_lhs => rw [key]
  rw [mul_assoc (ePlus (mat m F z)), hxf, hff]

theorem mat_eq_of_mem_complGroup (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {y : StatedSp m F}
    (hy : y ∈ complGroup z) :
    mat m F y = eMinus (mat m F z) + ePlus (mat m F z) * mat m F y * ePlus (mat m F z) := by
  have hD := mat_mul_self_of_mul_self hz
  have hyD : mat m F y * mat m F z = mat m F z * mat m F y := by
    rw [← map_mul, ← map_mul, comm_of_mem_complGroup h2 hz hy]
  have hye := (mem_complGroup_iff_mat h2 hz).mp hy
  have hey : eMinus (mat m F z) * mat m F y = eMinus (mat m F z) :=
    fixes_comm (spStar F m).toAddMonoidHom (fun a b => spStar_mul a b) (spStar_eMinus hz) hye
      (spStar_mat_mul y)
  have key := eq_add_of_commute (eMinus_add_ePlus h2) (eMinus_mul_ePlus hD) (ePlus_mul_eMinus hD)
    (commute_eMinus' hyD) (commute_ePlus' hyD)
  have he := idem_left (eMinus_add_ePlus h2) (eMinus_mul_ePlus hD)
  conv_lhs => rw [key]
  rw [mul_assoc (eMinus (mat m F z)), hye, he]

theorem commute_of_mem_longRootGroup_of_mem_complGroup (h2 : (2 : F) ≠ 0) (hz : z * z = 1)
    {x y : StatedSp m F} (hx : x ∈ longRootGroup z) (hy : y ∈ complGroup z) : x * y = y * x := by
  have hD := mat_mul_self_of_mul_self hz
  apply mat_injective
  rw [map_mul, map_mul]
  exact commute_of_fix (eMinus_add_ePlus h2) (eMinus_mul_ePlus hD) (ePlus_mul_eMinus hD)
    (mat_eq_of_mem_longRootGroup h2 hz hx) (mat_eq_of_mem_complGroup h2 hz hy)

theorem exists_mul_of_commute (h2 : (2 : F) ≠ 0) (hz : z * z = 1) {x : StatedSp m F}
    (hx : x * z = z * x) :
    ∃ a ∈ longRootGroup z, ∃ b ∈ complGroup z, x = a * b := by
  have hD := mat_mul_self_of_mul_self hz
  have hxD : mat m F x * mat m F z = mat m F z * mat m F x := by
    rw [← map_mul, ← map_mul, hx]
  have hsum := eMinus_add_ePlus h2 (D := mat m F z)
  have hsum' : ePlus (mat m F z) + eMinus (mat m F z) = 1 := (add_comm _ _).trans hsum
  have hef := eMinus_mul_ePlus hD
  have hfe := ePlus_mul_eMinus hD
  have h1 : (spStar F m).toAddMonoidHom
      (partOn (eMinus (mat m F z)) (ePlus (mat m F z)) (mat m F x)) *
      partOn (eMinus (mat m F z)) (ePlus (mat m F z)) (mat m F x) = 1 :=
    star_partOn_mul_partOn _ (fun a b => spStar_mul a b) hsum hef hfe (spStar_eMinus hz)
      (spStar_ePlus hz) (commute_eMinus' hxD) (spStar_mat_mul x)
  have h1' : (spStar F m).toAddMonoidHom
      (partOn (ePlus (mat m F z)) (eMinus (mat m F z)) (mat m F x)) *
      partOn (ePlus (mat m F z)) (eMinus (mat m F z)) (mat m F x) = 1 :=
    star_partOn_mul_partOn _ (fun a b => spStar_mul a b) hsum' hfe hef (spStar_ePlus hz)
      (spStar_eMinus hz) (commute_ePlus' hxD) (spStar_mat_mul x)
  refine ⟨ofSymplecticMat _ (symp_of_spStar h1), ?_, ofSymplecticMat _ (symp_of_spStar h1'), ?_, ?_⟩
  · rw [mem_longRootGroup_iff_mat h2 hz]
    exact partOn_mul_right hef hfe hsum _
  · rw [mem_complGroup_iff_mat h2 hz]
    exact partOn_mul_right hfe hef hsum' _
  · apply mat_injective
    rw [map_mul]
    exact (partOn_mul_partOn hsum hef hfe (commute_eMinus' hxD) (commute_ePlus' hxD)).symm

theorem mem_longRootGroup_self (h2 : (2 : F) ≠ 0) (hz : z * z = 1) : z ∈ longRootGroup z := by
  rw [mem_longRootGroup_iff_mat h2 hz]
  exact mul_ePlus (mat_mul_self_of_mul_self hz)

theorem eq_one_of_mem_complGroup_self (h2 : (2 : F) ≠ 0) (hz : z * z = 1)
    (h : z ∈ complGroup z) : z = 1 := by
  have hD := mat_mul_self_of_mul_self hz
  have h1 := (mem_complGroup_iff_mat h2 hz).mp h
  rw [mul_eMinus hD] at h1
  have h3 : (2 : F) • eMinus (mat m F z) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h1]
    exact neg_add_cancel _
  have h4 : eMinus (mat m F z) = 0 := by
    have := smul_right_injective _ h2 (h3.trans (smul_zero (2 : F)).symm)
    exact this
  have h5 : (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) - mat m F z = 0 := by
    rw [one_sub_eq_smul_eMinus h2, h4, smul_zero]
  apply mat_injective
  rw [map_one]
  exact (sub_eq_zero.mp h5).symm

end Groups

section Frames

variable {F : Type} [Field F] {m : ℕ}

@[expose] def stdSign (F : Type) [Field F] {m : ℕ} (S : Finset (Fin m)) : Fin m ⊕ Fin m → F :=
  Sum.elim (fun k => if k ∈ S then -1 else 1) (fun k => if k ∈ S then -1 else 1)

theorem stdSign_par (S : Finset (Fin m)) (a : Fin m ⊕ Fin m) :
    stdSign F S (par a) = stdSign F S a := by
  cases a <;> rfl

theorem stdSign_mul_self (S : Finset (Fin m)) (a : Fin m ⊕ Fin m) :
    stdSign F S a * stdSign F S a = 1 := by
  cases a <;> simp only [stdSign, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp

theorem diagonal_stdSign_symplectic (S : Finset (Fin m)) :
    (Matrix.diagonal (stdSign F S))ᵀ * gram F m * Matrix.diagonal (stdSign F S) = gram F m := by
  ext a b
  rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
  by_cases h : b = par a
  · subst h
    simp only [↓reduceIte, stdSign_par]
    calc stdSign F S a * sgn F a * stdSign F S a = sgn F a * (stdSign F S a * stdSign F S a) := by
          ring
      _ = sgn F a := by rw [stdSign_mul_self, mul_one]
  · simp [h]

@[expose] noncomputable def stdInv (F : Type) [Field F] {m : ℕ} (S : Finset (Fin m)) :
    StatedSp m F :=
  ofSymplecticMat (Matrix.diagonal (stdSign F S)) (diagonal_stdSign_symplectic S)

theorem mat_stdInv (S : Finset (Fin m)) : mat m F (stdInv F S) = Matrix.diagonal (stdSign F S) :=
  rfl

theorem stdInv_mul_self (S : Finset (Fin m)) : stdInv F S * stdInv F S = 1 := by
  apply mat_injective
  rw [map_mul, mat_stdInv, Matrix.diagonal_mul_diagonal, map_one, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact stdSign_mul_self S a

theorem form_eq_zero_of_mem_minus_fix (h2 : (2 : F) ≠ 0) {z : StatedSp m F}
    {v w : Fin m ⊕ Fin m → F} (hv : v ∈ minusSpace z) (hw : w ∈ fixSpace z) : form v w = 0 := by
  have h1 : form (mat m F z *ᵥ v) (mat m F z *ᵥ w) = form v w := form_mulVec z v w
  rw [mem_minusSpace.mp hv, mem_fixSpace.mp hw] at h1
  have h3 : form (-v) w = -form v w := by
    rw [← neg_one_smul F v, form_smul_left]
    ring
  rw [h3] at h1
  have h4 : (2 : F) * form v w = 0 := by linear_combination (-1 : F) * h1
  exact (mul_eq_zero.mp h4).resolve_left h2

theorem exists_mul_eq_stdInv (h2 : (2 : F) ≠ 0) {z : StatedSp m F} (hz : z * z = 1) :
    ∃ (S : Finset (Fin m)) (g : StatedSp m F), z * g = g * stdInv F S := by
  classical
  have hD := mat_mul_self_of_mul_self hz
  set B : LinearMap.BilinForm F (Fin m ⊕ Fin m → F) := Matrix.toBilin' (Matrix.J (Fin m) F)
    with hB
  have hAlt : B.IsAlt := isAlt_toBilin'_J
  have hnd : B.Nondegenerate := nondegenerate_toBilin'_J
  have hBform : ∀ u v, B u v = -form u v := fun u v => toBilin'_J_apply u v
  let W : Bool → Submodule F (Fin m ⊕ Fin m → F) := fun i => cond i (fixSpace z) (minusSpace z)
  have hW : ⨆ i, W i = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u = (eMinus (mat m F z) *ᵥ u) + (ePlus (mat m F z) *ᵥ u) := by
      rw [← Matrix.add_mulVec, eMinus_add_ePlus h2, Matrix.one_mulVec]
    rw [hu]
    refine Submodule.add_mem _ (Submodule.mem_iSup_of_mem false ?_)
      (Submodule.mem_iSup_of_mem true ?_)
    · show eMinus (mat m F z) *ᵥ u ∈ minusSpace z
      rw [mem_minusSpace, Matrix.mulVec_mulVec, mul_eMinus hD, Matrix.neg_mulVec]
    · show ePlus (mat m F z) *ᵥ u ∈ fixSpace z
      rw [mem_fixSpace, Matrix.mulVec_mulVec, mul_ePlus hD]
  have horth : ∀ i j : Bool, j ≠ id i → ∀ v ∈ W i, ∀ w ∈ W j, B v w = 0 := by
    intro i j hij v hv w hw
    rw [hBform]
    cases i <;> cases j
    · exact absurd rfl hij
    · rw [form_eq_zero_of_mem_minus_fix h2 hv hw, neg_zero]
    · rw [form_antisymm, form_eq_zero_of_mem_minus_fix h2 hw hv]
      simp
    · exact absurd rfl hij
  obtain ⟨m', b, hb, hbW⟩ := hAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top hnd (σ := id)
    (fun _ => rfl) hW horth
  have hm' : m' = m := by
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_pi] at this
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm'
  have hb' : ∀ x y, form (b x) (b y) = gram F m' x y := fun x y => by
    have := congrFun (congrFun hb x) y
    rw [LinearMap.BilinForm.toMatrix_apply, hBform] at this
    rw [gram_eq_neg_J, Matrix.neg_apply, ← this, neg_neg]
  have hcls : ∀ x, b x ∈ minusSpace z ∨ b x ∈ fixSpace z := fun x => by
    obtain ⟨i, hi⟩ := hbW x
    cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hnot : ∀ x, ¬ b x ∈ minusSpace z → b x ∈ fixSpace z := fun x hx =>
    (hcls x).resolve_left hx
  have hpair : ∀ k : Fin m', b (Sum.inr k) ∈ minusSpace z ↔ b (Sum.inl k) ∈ minusSpace z := by
    intro k
    have h1 : form (b (Sum.inl k)) (b (Sum.inr k)) = 1 := by
      rw [hb', CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
      simp
    constructor
    · intro hr
      by_contra hl
      have hl' := hnot _ hl
      have h0 : form (b (Sum.inl k)) (b (Sum.inr k)) = 0 := by
        rw [form_antisymm (b (Sum.inr k)) (b (Sum.inl k)),
          form_eq_zero_of_mem_minus_fix h2 hr hl', neg_zero]
      rw [h1] at h0
      exact one_ne_zero h0
    · intro hl
      by_contra hr
      have h0 : form (b (Sum.inl k)) (b (Sum.inr k)) = 0 :=
        form_eq_zero_of_mem_minus_fix h2 hl (hnot _ hr)
      rw [h1] at h0
      exact one_ne_zero h0
  let S : Finset (Fin m') := Finset.univ.filter (fun k => b (Sum.inl k) ∈ minusSpace z)
  have heig : ∀ x, mat m' F z *ᵥ b x = stdSign F S x • b x := by
    intro x
    rcases x with k | k
    · by_cases hk : b (Sum.inl k) ∈ minusSpace z
      · have : stdSign F S (Sum.inl k) = -1 := by simp [stdSign, S, hk]
        rw [this, neg_one_smul]
        exact mem_minusSpace.mp hk
      · have : stdSign F S (Sum.inl k) = 1 := by simp [stdSign, S, hk]
        rw [this, one_smul]
        exact mem_fixSpace.mp (hnot _ hk)
    · by_cases hk : b (Sum.inr k) ∈ minusSpace z
      · have hl := (hpair k).mp hk
        have : stdSign F S (Sum.inr k) = -1 := by simp [stdSign, S, hl]
        rw [this, neg_one_smul]
        exact mem_minusSpace.mp hk
      · have hl : ¬ b (Sum.inl k) ∈ minusSpace z := fun hl => hk ((hpair k).mpr hl)
        have : stdSign F S (Sum.inr k) = 1 := by simp [stdSign, S, hl]
        rw [this, one_smul]
        exact mem_fixSpace.mp (hnot _ hk)
  refine ⟨S, ofSymplecticBasis b hb', ?_⟩
  apply mat_injective
  rw [map_mul, map_mul, mat_stdInv, mat_ofSymplecticBasis]
  ext r c
  rw [Matrix.mul_diagonal]
  have h5 := congrFun (heig c) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h5
  simp only [Matrix.mul_apply, basisMat, Matrix.of_apply]
  rw [h5]
  ring

end Frames

section Standard

variable {F : Type} [Field F] {m : ℕ}

@[expose] def cS (S : Finset (Fin m)) : Set (Fin m ⊕ Fin m) := {t | Sum.elim id id t ∈ S}

theorem parClosed_cS (S : Finset (Fin m)) : ParClosed (cS S) := fun a ha => by
  cases a <;> exact ha

theorem stdSign_of_mem {S : Finset (Fin m)} {t : Fin m ⊕ Fin m} (ht : t ∈ cS S) :
    stdSign F S t = -1 := by
  rcases t with k | k <;>
  · have hk : k ∈ S := ht
    simp [stdSign, hk]

theorem stdSign_of_not_mem {S : Finset (Fin m)} {t : Fin m ⊕ Fin m} (ht : t ∉ cS S) :
    stdSign F S t = 1 := by
  rcases t with k | k <;>
  · have hk : k ∉ S := ht
    simp [stdSign, hk]

theorem mem_fixSpace_stdInv (h2 : (2 : F) ≠ 0) (S : Finset (Fin m))
    {v : Fin m ⊕ Fin m → F} :
    v ∈ fixSpace (stdInv F S) ↔ ∀ t ∈ cS S, v t = 0 := by
  rw [mem_fixSpace, mat_stdInv, mulVec_diagonal_eq]
  constructor
  · intro h t ht
    have h1 := congrFun h t
    rw [stdSign_of_mem ht] at h1
    have h' : (2 : F) * v t = 0 := by linear_combination -h1
    exact (mul_eq_zero.1 h').resolve_left h2
  · intro h
    funext t
    by_cases ht : t ∈ cS S
    · simp [h t ht]
    · simp [stdSign_of_not_mem ht]

theorem mem_minusSpace_stdInv (h2 : (2 : F) ≠ 0) (S : Finset (Fin m))
    {v : Fin m ⊕ Fin m → F} :
    v ∈ minusSpace (stdInv F S) ↔ ∀ t ∉ cS S, v t = 0 := by
  rw [mem_minusSpace, mat_stdInv, mulVec_diagonal_eq]
  constructor
  · intro h t ht
    have h1 := congrFun h t
    rw [stdSign_of_not_mem ht] at h1
    have h' : (2 : F) * v t = 0 := by
      simp only [one_mul, Pi.neg_apply] at h1
      linear_combination h1
    exact (mul_eq_zero.1 h').resolve_left h2
  · intro h
    funext t
    by_cases ht : t ∈ cS S
    · simp [stdSign_of_mem ht]
    · simp [h t ht]

theorem longRootGroup_stdInv (h2 : (2 : F) ≠ 0) (S : Finset (Fin m)) :
    longRootGroup (stdInv F S) = suppGroup (cS S) := by
  rw [← fixing_supported_eq (parClosed_cS S), longRootGroup]
  congr 1
  ext v
  exact mem_fixSpace_stdInv h2 S

theorem complGroup_stdInv (h2 : (2 : F) ≠ 0) (S : Finset (Fin m)) :
    complGroup (stdInv F S) = suppGroup (cS S)ᶜ := by
  rw [← fixing_supported_eq (parClosed_cS S).compl, complGroup]
  congr 1
  ext v
  exact mem_minusSpace_stdInv h2 S

theorem range_sum_map_orderEmbOfFin (S : Finset (Fin m)) {a : ℕ} (ha : S.card = a) :
    Set.range (Sum.map (S.orderEmbOfFin ha) (S.orderEmbOfFin ha)) = cS S := by
  have hr : Set.range (S.orderEmbOfFin ha) = (S : Set (Fin m)) := Finset.range_orderEmbOfFin S ha
  have hmem : ∀ k, (∃ l, S.orderEmbOfFin ha l = k) ↔ k ∈ S := fun k => by
    rw [← Set.mem_range, hr]
    exact Finset.mem_coe
  ext t
  rcases t with k | k <;> simp [cS, Sum.exists, hmem]


theorem compl_cS (S : Finset (Fin m)) : (cS S)ᶜ = cS Sᶜ := by
  ext t
  rcases t with k | k <;> simp [cS]

theorem nonempty_mulEquiv_suppGroup_cS (T : Finset (Fin m)) {a : ℕ} (ha : T.card = a) :
    Nonempty (StatedSp a F ≃* suppGroup (K := F) (cS T)) := by
  have hσ : Function.Injective (T.orderEmbOfFin ha) := (T.orderEmbOfFin ha).injective
  have hrange : (spEmbed (K := F) (T.orderEmbOfFin ha) hσ).range = suppGroup (K := F) (cS T) := by
    rw [range_spEmbed, range_sum_map_orderEmbOfFin T ha]
  exact ⟨(MonoidHom.ofInjective (spEmbed_injective hσ)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem nonempty_mulEquiv_longRootGroup_sp (h2 : (2 : F) ≠ 0) {S : Finset (Fin m)}
    {g z : StatedSp m F} (hzg : z = g * stdInv F S * g⁻¹) :
    Nonempty (StatedSp S.card F ≃* longRootGroup z) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_suppGroup_cS (F := F) S rfl
  exact ⟨e.trans ((Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr
      (by rw [hzg, longRootGroup_conj, longRootGroup_stdInv h2])))⟩

theorem nonempty_mulEquiv_complGroup_sp (h2 : (2 : F) ≠ 0) {S : Finset (Fin m)}
    {g z : StatedSp m F} (hzg : z = g * stdInv F S * g⁻¹) :
    Nonempty (StatedSp (Sᶜ).card F ≃* complGroup z) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_suppGroup_cS (F := F) Sᶜ rfl
  exact ⟨e.trans ((Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr
      (by rw [hzg, complGroup_conj, complGroup_stdInv h2, compl_cS])))⟩


end Standard

section TwoInvolutions

theorem false_of_two_commuting_involutions {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {L : Type} [Group L] [Finite L]
    (e : L ⧸ classicalInvolutionOddCore L ≃* SL(2, F)) {a b : L} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) : False := by
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have hnot : ∀ x : L, orderOf x = 2 → x ∉ classicalInvolutionOddCore L := fun x hx hxO => by
    have h1 := Subgroup.orderOf_dvd_natCard (classicalInvolutionOddCore L) hxO
    rw [hx] at h1
    obtain ⟨k, hk⟩ := hOodd
    omega
  have himg : ∀ x : L, orderOf x = 2 →
      e (QuotientGroup.mk' (classicalInvolutionOddCore L) x) = -1 := fun x hx => by
    refine (sl2_orderOf_eq_two_iff hodd _).mp ?_
    rw [MulEquiv.orderOf_eq]
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx, pow_two] at this
    have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore L) x) ^ 2 = 1 := by
      rw [← map_pow, pow_two, hx2, map_one]
    have h2 : QuotientGroup.mk' (classicalInvolutionOddCore L) x ≠ 1 := fun h => hnot x hx (by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h)
    exact orderOf_eq_prime h1 h2
  have h1 := himg a ha
  have h2 := himg b hb
  have hq : QuotientGroup.mk' (classicalInvolutionOddCore L) a =
      QuotientGroup.mk' (classicalInvolutionOddCore L) b := e.injective (h1.trans h2.symm)
  have hmem : a⁻¹ * b ∈ classicalInvolutionOddCore L := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hq
    exact hq
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  have hb2 : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, pow_two] at this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  rw [hainv] at hmem
  apply hnot (a * b) _ hmem
  have hsq : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * b * (a * b) := pow_two _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hne1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rwa [inv_eq_of_mul_eq_one_right hb2] at this)
  exact orderOf_eq_prime hsq hne1

end TwoInvolutions



section Main

variable {p f : ℕ} [Fact p.Prime]

theorem open_isQuasisimple_statedSp (hq : 5 ≤ p ^ f) {a : ℕ} (ha : 1 ≤ a) :
    CFSG.Open.IsQuasisimple (StatedSp a (GaloisField p f)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcard]; omega
    exact Components.quasisimple_of_equiv (longBlockEquivOne (K := GaloisField p f)).symm
      (isQuasisimple_specialLinearGroup_two h4)
  · have hadm : StatedLieAdmissible .PSp a p f := ⟨Fact.out, by omega, h, fun h' => by
      have := congrArg Prod.snd h'
      simp only at this
      omega⟩
    exact open_isQuasisimple
      (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible a (GaloisField p f) hadm hcard)

theorem subsingleton_statedSp_zero {F : Type} [Field F] : Subsingleton (StatedSp 0 F) :=
  ⟨fun _ _ => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩

theorem stdInv_empty {F : Type} [Field F] {m : ℕ} : stdInv F (∅ : Finset (Fin m)) = 1 := by
  apply mat_injective
  rw [mat_stdInv, map_one, ← Matrix.diagonal_one]
  congr 1
  funext t
  exact stdSign_of_not_mem (fun h => by simp [cS] at h)

theorem stdInv_singleton {F : Type} [Field F] {m : ℕ} (k : Fin m) :
    stdInv F {k} = longInv F m k := by
  apply mat_injective
  rw [mat_stdInv, mat_longInv]
  congr 1
  funext t
  by_cases ht : t ∈ coords k
  · have : t ∈ cS ({k} : Finset (Fin m)) := by
      rcases mem_coords.1 ht with rfl | rfl <;> simp [cS]
    rw [stdSign_of_mem this]
    simp [ht]
  · have : t ∉ cS ({k} : Finset (Fin m)) := by
      intro h
      apply ht
      rcases t with j | j
      · have : j = k := by simpa [cS] using h
        subst this
        exact inl_mem_coords j
      · have : j = k := by simpa [cS] using h
        subst this
        exact inr_mem_coords j
    rw [stdSign_of_not_mem this]
    simp [ht]

theorem coords_subset_cS {m : ℕ} {S : Finset (Fin m)} {k : Fin m} (hk : k ∈ S) :
    coords k ⊆ cS S := by
  intro t ht
  rcases mem_coords.1 ht with rfl | rfl <;> simpa [cS] using hk

theorem isLongRootSp2_of_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ}
    {L : Subgroup (StatedSp m (GaloisField p f))} {z : StatedSp m (GaloisField p f)}
    (h : IsClassicalMember p f L z) : IsLongRootSp2 L z := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  set F := GaloisField p f with hFdef
  have hcard : Nat.card F = p ^ f := GaloisField.card p f hf
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have : ringChar F ∣ 2 := ringChar.dvd (by simpa using h0)
    rw [ringChar.eq F p] at this
    have := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this
    exact hp2 this
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := h.ne_one
  obtain ⟨S, g, hg⟩ := exists_mul_eq_stdInv h2 hzz
  have hzg : z = g * stdInv F S * g⁻¹ := by rw [← hg]; group
  have hLC : ∀ x ∈ L, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
  have hLsup : L ≤ longRootGroup z ⊔ complGroup z := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute h2 hzz (hLC x hx)
    exact Subgroup.mul_mem_sup ha hb
  have hcomm : ∀ x ∈ longRootGroup z, ∀ y ∈ complGroup z, x * y = y * x :=
    fun x hx y hy => commute_of_mem_longRootGroup_of_mem_complGroup h2 hzz hx hy
  have hzAp : z ∉ complGroup z := fun hz => hz1 (eq_one_of_mem_complGroup_self h2 hzz hz)
  have hAmC : longRootGroup z ≤ Subgroup.centralizer ({z} : Set (StatedSp m F)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroup h2 hzz hx)
  have hSa : 1 ≤ S.card := by
    by_contra hlt
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS
    rw [stdInv_empty, mul_one] at hg
    exact hz1 (mul_right_cancel (hg.trans (one_mul g).symm))
  obtain ⟨eAm⟩ := nonempty_mulEquiv_longRootGroup_sp h2 hzg
  obtain ⟨eAp⟩ := nonempty_mulEquiv_complGroup_sp h2 hzg
  have hAmq : CFSG.Open.IsQuasisimple ↥(longRootGroup z) :=
    Components.quasisimple_of_equiv eAm.symm (open_isQuasisimple_statedSp hq hSa)
  have hBq : complGroup z = ⊥ ∨ CFSG.Open.IsQuasisimple ↥(complGroup z) := by
    by_cases hb : 1 ≤ (Sᶜ).card
    · exact Or.inr (Components.quasisimple_of_equiv eAp.symm (open_isQuasisimple_statedSp hq hb))
    · left
      have hb0 : (Sᶜ).card = 0 := by omega
      have : Subsingleton (StatedSp (Sᶜ).card F) := by
        rw [hb0]
        exact subsingleton_statedSp_zero
      have : Subsingleton (complGroup z) := eAp.surjective.subsingleton
      exact Subgroup.eq_bot_of_subsingleton _
  have hLeq : L = longRootGroup z :=
    eq_of_le_sup_of_isClassicalMember (by omega) h hcomm hLsup hzAp hAmC hAmq hBq
  have hS1 : S.card = 1 := by
    by_contra hne
    have h2le : 2 ≤ S.card := by omega
    obtain ⟨k₁, hk₁, k₂, hk₂, hk12⟩ := Finset.one_lt_card.mp h2le
    have hmem : ∀ k ∈ S, g * longInv F m k * g⁻¹ ∈ L := fun k hk => by
      rw [hLeq, hzg, longRootGroup_conj, longRootGroup_stdInv h2]
      refine ⟨longInv F m k, suppGroup_mono (K := F) (coords_subset_cS hk) ?_, rfl⟩
      rw [← range_longBlock]
      exact longInv_mem_longRootSp2 k
    have hord : ∀ k, orderOf (g * longInv F m k * g⁻¹) = 2 := fun k => by
      rw [orderOf_conj_eq]
      exact (isClassicalSL2_longRootSp2 h2 k).orderOf_eq_two
    obtain ⟨e2⟩ := h.nonempty_equiv
    refine false_of_two_commuting_involutions hodd e2
      (a := ⟨g * longInv F m k₁ * g⁻¹, hmem k₁ hk₁⟩) (b := ⟨g * longInv F m k₂ * g⁻¹, hmem k₂ hk₂⟩)
      (by rw [Subgroup.orderOf_mk]; exact hord k₁) (by rw [Subgroup.orderOf_mk]; exact hord k₂)
      ?_ ?_
    · apply Subtype.ext
      show g * longInv F m k₁ * g⁻¹ * (g * longInv F m k₂ * g⁻¹) =
        g * longInv F m k₂ * g⁻¹ * (g * longInv F m k₁ * g⁻¹)
      have hc : longInv F m k₁ * longInv F m k₂ = longInv F m k₂ * longInv F m k₁ := by
        apply mat_injective
        rw [map_mul, map_mul, mat_longInv, mat_longInv, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal]
        congr 1
        funext t
        exact mul_comm _ _
      calc g * longInv F m k₁ * g⁻¹ * (g * longInv F m k₂ * g⁻¹)
          = g * (longInv F m k₁ * longInv F m k₂) * g⁻¹ := by group
        _ = g * (longInv F m k₂ * longInv F m k₁) * g⁻¹ := by rw [hc]
        _ = g * longInv F m k₂ * g⁻¹ * (g * longInv F m k₁ * g⁻¹) := by group
    · intro hab
      have := congrArg Subtype.val hab
      simp only at this
      have h3 : longInv F m k₁ = longInv F m k₂ := by simpa using this
      exact longInv_ne_of_ne h2 hk12 h3
  obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp hS1
  rw [stdInv_singleton] at hzg
  refine ⟨k, g, ?_, hzg⟩
  rw [hLeq, hzg, longRootGroup_conj, longRootGroup_longInv h2, longRootSp2_eq_suppGroup]

theorem classicalMembersFundamental_psp (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ}
    (hadm : StatedLieAdmissible .PSp m p f) : ClassicalMembersFundamental p f .PSp m f hp := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h0
    have : ringChar (GaloisField p f) ∣ 2 := ringChar.dvd (by simpa using h0)
    rw [ringChar.eq (GaloisField p f) p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  intro L z hL
  obtain ⟨P, hP, hLP⟩ := (exists_isLongRootSp2_iff h2 L).mp
    ⟨z, isLongRootSp2_of_isClassicalMember hp2 hq hL⟩
  exact (mem_fundamentalSubgroups_PSp_iff hadm L).mpr ⟨P, hP, hLP⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts
