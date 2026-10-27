module

public import CFSG.GH74.Generic.Front.InvolutionLA
public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.Assembly.LowTwoRank Module Matrix
open scoped MatrixGroups

section Dim

variable {F : Type*} [Field F]

theorem rinv_toLin_involutive {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι F)
    (ht : T * T = 1) : ∀ v, Matrix.toLin' T (Matrix.toLin' T v) = v := fun v => by
  have : Matrix.toLin' T (Matrix.toLin' T v) = (T * T).mulVec v := by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
  rw [this, ht, Matrix.one_mulVec]

theorem rinv_dim_two_or_four (h2 : (2 : F) ≠ 0) (t : Matrix (Fin 5) (Fin 5) F)
    (ht : t * t = 1) (hdet : t.det = 1) (h1 : t ≠ 1) :
    finrank F (LinearMap.ker (Matrix.toLin' t + LinearMap.id)) = 2 ∨
      finrank F (LinearMap.ker (Matrix.toLin' t + LinearMap.id)) = 4 := by
  classical
  let f := Matrix.toLin' t
  have hf : ∀ v, f (f v) = v := rinv_toLin_involutive t ht
  have hsum := involution_finrank_add h2 f hf
  have h5 : finrank F (Fin 5 → F) = 5 := by simp
  have hdet' := involution_det h2 t ht
  rw [hdet] at hdet'
  have hneg : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    have : (2 : F) = 1 - -1 := by norm_num
    rw [this, h]; simp
  have hev : Even (finrank F (LinearMap.ker (f + LinearMap.id))) := by
    rw [← neg_one_pow_eq_one_iff_even hneg]
    exact hdet'.symm
  set a := finrank F (LinearMap.ker (f + LinearMap.id)) with ha
  set b := finrank F (LinearMap.ker (f - LinearMap.id)) with hb
  have hab : a + b = 5 := by rw [hsum, h5]
  obtain ⟨m, hm⟩ := hev
  have hcases : a = 0 ∨ a = 2 ∨ a = 4 := by omega
  rcases hcases with h0 | h2' | h4'
  · exfalso
    have hb5 : b = 5 := by omega
    have htop : LinearMap.ker (f - LinearMap.id) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [← hb, hb5, h5])
    apply h1
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker (f - LinearMap.id) := by rw [htop]; trivial
    have : f v - v = 0 := by simpa using hv
    show f v = (Matrix.toLin' (1 : Matrix (Fin 5) (Fin 5) F)) v
    rw [Matrix.toLin'_apply (1 : Matrix (Fin 5) (Fin 5) F), Matrix.one_mulVec]
    exact sub_eq_zero.1 this
  · exact Or.inl h2'
  · exact Or.inr h4'

end Dim

section BasisMatrix

variable {F : Type*} [Field F] {n a b : ℕ}

@[expose] def rinvIdx (hab : a + b = n) : Fin a ⊕ Fin b ≃ Fin n :=
  finSumFinEquiv.trans (finCongr hab)

theorem rinvIdx_inl (hab : a + b = n) (i : Fin a) :
    ((rinvIdx hab (Sum.inl i) : Fin n) : ℕ) = i := by
  simp [rinvIdx]

theorem rinvIdx_inr (hab : a + b = n) (j : Fin b) :
    ((rinvIdx hab (Sum.inr j) : Fin n) : ℕ) = a + j := by
  simp [rinvIdx]

@[expose] def rinvSign (F : Type*) [Field F] (n a : ℕ) : Fin n → F :=
  fun j => if (j : ℕ) < a then -1 else 1

@[expose] noncomputable def rinvMat (hab : a + b = n) (B : Basis (Fin a ⊕ Fin b) F (Fin n → F)) :
    Matrix (Fin n) (Fin n) F :=
  (Pi.basisFun F (Fin n)).toMatrix (B.reindex (rinvIdx hab))

theorem rinvMat_apply (hab : a + b = n) (B : Basis (Fin a ⊕ Fin b) F (Fin n → F)) (i j : Fin n) :
    rinvMat hab B i j = B ((rinvIdx hab).symm j) i := by
  simp [rinvMat, Basis.toMatrix_apply]

theorem rinvMat_isUnit (hab : a + b = n) (B : Basis (Fin a ⊕ Fin b) F (Fin n → F)) :
    IsUnit (rinvMat hab B) := by
  have := Basis.invertibleToMatrix (Pi.basisFun F (Fin n)) (B.reindex (rinvIdx hab))
  exact isUnit_of_invertible ((Pi.basisFun F (Fin n)).toMatrix (B.reindex (rinvIdx hab)))

theorem rinvMat_mul_eq (hab : a + b = n) (B : Basis (Fin a ⊕ Fin b) F (Fin n → F))
    (T : Matrix (Fin n) (Fin n) F) (h1 : ∀ i, T *ᵥ B (Sum.inl i) = -B (Sum.inl i))
    (h2 : ∀ j, T *ᵥ B (Sum.inr j) = B (Sum.inr j)) :
    T * rinvMat hab B = rinvMat hab B * Matrix.diagonal (rinvSign F n a) := by
  ext i j
  obtain ⟨x, rfl⟩ := (rinvIdx hab).surjective j
  have hcol : T *ᵥ B x = (rinvSign F n a (rinvIdx hab x)) • B x := by
    rcases x with x | x
    · rw [h1, rinvSign, rinvIdx_inl, ite_eq_left x.2]
      simp
    · rw [h2, rinvSign, rinvIdx_inr, ite_eq_right (by omega)]
      simp
  have e1 : (T * rinvMat hab B) i (rinvIdx hab x) = (T *ᵥ B x) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, rinvMat_apply]
  rw [e1, hcol]
  simp [Matrix.mul_diagonal, rinvMat_apply, mul_comm]

end BasisMatrix

section Lin

variable {F : Type*} [Field F]

theorem rinvSign_two : rinvSign F 5 2 = ![-1, -1, 1, 1, 1] := by
  funext j
  fin_cases j <;> simp [rinvSign]

theorem rinvSign_four : rinvSign F 5 4 = ![-1, -1, -1, -1, 1] := by
  funext j
  fin_cases j <;> simp [rinvSign]

theorem rinv_det_diagonal_sign_two : (Matrix.diagonal (rinvSign F 5 2)).det = 1 := by
  rw [rinvSign_two]
  simp [Matrix.det_diagonal, Fin.prod_univ_five]

theorem rinv_det_diagonal_sign_four : (Matrix.diagonal (rinvSign F 5 4)).det = 1 := by
  rw [rinvSign_four]
  simp [Matrix.det_diagonal, Fin.prod_univ_five]

@[expose] def rinvFirst (d : F) : Matrix (Fin 5) (Fin 5) F :=
  Matrix.diagonal fun i => if i = 0 then d else 1

theorem rinv_det_first (d : F) : (rinvFirst d).det = d := by
  simp [rinvFirst, Matrix.det_diagonal]

theorem rinvFirst_mul_diagonal_comm (d : F) (ε : Fin 5 → F) :
    rinvFirst d * Matrix.diagonal ε = Matrix.diagonal ε * rinvFirst d := by
  simp only [rinvFirst, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem rinv_group_conj {G : Type*} [Group G] {t P D : G} (h : t * P = P * D) :
    ∃ g : G, g * t * g⁻¹ = D :=
  ⟨P⁻¹, by rw [inv_inv, mul_assoc, h, inv_mul_cancel_left]⟩

theorem rinv_exists_det_one (h2 : (2 : F) ≠ 0) (T : Matrix (Fin 5) (Fin 5) F) (hT : T * T = 1)
    (hdet : T.det = 1) (h1 : T ≠ 1) :
    ∃ a : ℕ, (a = 2 ∨ a = 4) ∧ ∃ P : Matrix (Fin 5) (Fin 5) F, P.det = 1 ∧
      T * P = P * Matrix.diagonal (rinvSign F 5 a) := by
  classical
  have hf : ∀ v, Matrix.toLin' T (Matrix.toLin' T v) = v := rinv_toLin_involutive T hT
  have hsum := involution_finrank_add h2 (Matrix.toLin' T) hf
  have h5 : finrank F (Fin 5 → F) = 5 := by simp
  obtain ⟨a, ha⟩ : ∃ a, finrank F (LinearMap.ker (Matrix.toLin' T + LinearMap.id)) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, finrank F (LinearMap.ker (Matrix.toLin' T - LinearMap.id)) = b := ⟨_, rfl⟩
  have hab : a + b = 5 := by rw [← ha, ← hb, hsum, h5]
  have ha24 := rinv_dim_two_or_four h2 T hT hdet h1
  rw [ha] at ha24
  obtain ⟨B, hB1, hB2⟩ := exists_basis_involution' h2 (Matrix.toLin' T) hf a b ha hb
  have hB1' : ∀ i, T *ᵥ B (Sum.inl i) = -B (Sum.inl i) := fun i => by
    simpa [Matrix.toLin'_apply] using hB1 i
  have hB2' : ∀ j, T *ᵥ B (Sum.inr j) = B (Sum.inr j) := fun j => by
    simpa [Matrix.toLin'_apply] using hB2 j
  have hTP := rinvMat_mul_eq hab B T hB1' hB2'
  have hu := rinvMat_isUnit hab B
  have hd0 : (rinvMat hab B).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  refine ⟨a, ha24, rinvMat hab B * rinvFirst (rinvMat hab B).det⁻¹, ?_, ?_⟩
  · rw [Matrix.det_mul, rinv_det_first, mul_inv_cancel₀ hd0]
  · rw [← Matrix.mul_assoc, hTP, Matrix.mul_assoc, Matrix.mul_assoc, rinvFirst_mul_diagonal_comm]

end Lin

theorem invClasses_lin {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ d₂ d₄ : SL(5, F), ∀ t : SL(5, F), t * t = 1 → t ≠ 1 →
      (∃ g : SL(5, F), g * t * g⁻¹ = d₂) ∨ ∃ g : SL(5, F), g * t * g⁻¹ = d₄ := by
  obtain ⟨D₂, hD₂⟩ : ∃ D : SL(5, F), (D : Matrix (Fin 5) (Fin 5) F) =
      Matrix.diagonal (rinvSign F 5 2) := ⟨⟨_, rinv_det_diagonal_sign_two⟩, rfl⟩
  obtain ⟨D₄, hD₄⟩ : ∃ D : SL(5, F), (D : Matrix (Fin 5) (Fin 5) F) =
      Matrix.diagonal (rinvSign F 5 4) := ⟨⟨_, rinv_det_diagonal_sign_four⟩, rfl⟩
  refine ⟨D₂, D₄, ?_⟩
  intro t htt ht1
  have hT : (t : Matrix (Fin 5) (Fin 5) F) * (t : Matrix (Fin 5) (Fin 5) F) = 1 := by
    have := congrArg (fun x : SL(5, F) => (x : Matrix (Fin 5) (Fin 5) F)) htt
    simpa using this
  have hT1 : (t : Matrix (Fin 5) (Fin 5) F) ≠ 1 := fun h => ht1 (Subtype.ext (by simpa using h))
  obtain ⟨a, ha, P, hPdet, hTP⟩ := rinv_exists_det_one h2 (t : Matrix (Fin 5) (Fin 5) F) hT t.2 hT1
  obtain ⟨Pm, hPm⟩ : ∃ Pm : SL(5, F), (Pm : Matrix (Fin 5) (Fin 5) F) = P := ⟨⟨P, hPdet⟩, rfl⟩
  rcases ha with rfl | rfl
  · left
    refine rinv_group_conj (P := Pm) ?_
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD₂, hPm]
    exact congrFun (congrFun hTP i) j
  · right
    refine rinv_group_conj (P := Pm) ?_
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD₄, hPm]
    exact congrFun (congrFun hTP i) j

section Uni

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F] {p f : ℕ}

theorem rinvFirst_mul (d e : F) : rinvFirst d * rinvFirst e = rinvFirst (d * e) := by
  simp only [rinvFirst, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases hi : i = 0 <;> simp [hi]

theorem rinvFirst_one : rinvFirst (1 : F) = 1 := by
  simp [rinvFirst]

theorem rinvFirst_map (σ : F →+* F) (d : F) : (rinvFirst d).map σ = rinvFirst (σ d) := by
  rw [rinvFirst, Matrix.diagonal_map (map_zero σ), rinvFirst]
  congr 1
  ext i
  by_cases hi : i = 0 <;> simp [hi]

theorem rinv_orthonormal_basis {n : ℕ} (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    (T : Matrix (Fin n) (Fin n) F) (hT : T * T = 1) (hU : (T.map h.bar)ᵀ * T = 1) (a b : ℕ)
    (ha : finrank F (LinearMap.ker (Matrix.toLin' T + LinearMap.id)) = a)
    (hb : finrank F (LinearMap.ker (Matrix.toLin' T - LinearMap.id)) = b) :
    ∃ Bs : Basis (Fin a ⊕ Fin b) F (Fin n → F),
      (∀ i, T *ᵥ Bs (Sum.inl i) = -Bs (Sum.inl i)) ∧ (∀ j, T *ᵥ Bs (Sum.inr j) = Bs (Sum.inr j)) ∧
      ∀ x y, gramForm h (1 : Matrix (Fin n) (Fin n) F) (Bs x) (Bs y) = if x = y then 1 else 0 := by
  classical
  have hf : ∀ v, Matrix.toLin' T (Matrix.toLin' T v) = v := rinv_toLin_involutive T hT
  have hc : IsCompl (LinearMap.ker (Matrix.toLin' T + LinearMap.id))
      (LinearMap.ker (Matrix.toLin' T - LinearMap.id)) := involution_isCompl h2 _ hf
  have hWm : ∀ v, v ∈ LinearMap.ker (Matrix.toLin' T + LinearMap.id) ↔ T *ᵥ v = -v := fun v => by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Matrix.toLin'_apply, LinearMap.id_apply]
    exact eq_neg_iff_add_eq_zero.symm
  have hWp : ∀ v, v ∈ LinearMap.ker (Matrix.toLin' T - LinearMap.id) ↔ T *ᵥ v = v := fun v => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply]
    exact sub_eq_zero
  set B := gramForm h (1 : Matrix (Fin n) (Fin n) F) with hBdef
  have hB : B.IsSymm := gramForm_isSymm h (by simp)
  have hBl : B.SeparatingLeft := gramForm_separatingLeft h (by simp)
  have hiso : ∀ x y, B (T *ᵥ x) (T *ᵥ y) = B x y :=
    (gramForm_isometry_iff h 1 T).2 (by rw [Matrix.mul_one]; exact hU)
  have horth : ∀ u v, T *ᵥ u = -u → T *ᵥ v = v → B u v = 0 := by
    intro u v hu hv
    have h1 := hiso u v
    rw [hu, hv] at h1
    have h3 : (2 : F) * B u v = 0 := by
      have : B (-u) v = -B u v := by simp
      rw [this] at h1
      linear_combination -h1
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hsep : ∀ {W W' : Submodule F (Fin n → F)}, IsCompl W W' →
      (∀ w ∈ W, ∀ w' ∈ W', B w w' = 0) → (B.domRestrict₁₂ W W).SeparatingLeft := by
    intro W W' hcW horthW x hx
    have hxz : ∀ z, B (x : Fin n → F) z = 0 := by
      intro z
      have hz : z ∈ W ⊔ W' := by rw [hcW.sup_eq_top]; trivial
      obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.1 hz
      have h1 : B (x : Fin n → F) y = 0 := hx ⟨y, hy⟩
      rw [map_add, h1, horthW x x.2 y' hy', add_zero]
    exact Subtype.ext (hBl _ hxz)
  have horthm : ∀ w ∈ LinearMap.ker (Matrix.toLin' T + LinearMap.id),
      ∀ w' ∈ LinearMap.ker (Matrix.toLin' T - LinearMap.id), B w w' = 0 :=
    fun w hw w' hw' => horth w w' ((hWm w).1 hw) ((hWp w').1 hw')
  have horthp : ∀ w ∈ LinearMap.ker (Matrix.toLin' T - LinearMap.id),
      ∀ w' ∈ LinearMap.ker (Matrix.toLin' T + LinearMap.id), B w w' = 0 := by
    intro w hw w' hw'
    rw [← hB.eq w' w, horthm w' hw' w hw, map_zero]
  obtain ⟨em, hem⟩ := h.exists_orthonormal_basis
    (B := B.domRestrict₁₂ (LinearMap.ker (Matrix.toLin' T + LinearMap.id))
      (LinearMap.ker (Matrix.toLin' T + LinearMap.id)))
    (hB.domRestrict _) (hsep hc horthm)
  obtain ⟨ep, hep⟩ := h.exists_orthonormal_basis
    (B := B.domRestrict₁₂ (LinearMap.ker (Matrix.toLin' T - LinearMap.id))
      (LinearMap.ker (Matrix.toLin' T - LinearMap.id)))
    (hB.domRestrict _) (hsep hc.symm horthp)
  let em' := em.reindex (finCongr ha)
  let ep' := ep.reindex (finCongr hb)
  set Bs := (em'.prod ep').map (Submodule.prodEquivOfIsCompl _ _ hc) with hBs
  have e1 : ∀ i, Bs (Sum.inl i) = (em' i : Fin n → F) := fun i => by
    rw [hBs, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  have e2 : ∀ j, Bs (Sum.inr j) = (ep' j : Fin n → F) := fun j => by
    rw [hBs, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  refine ⟨Bs, fun i => ?_, fun j => ?_, ?_⟩
  · rw [e1]
    exact (hWm _).1 (em' i).2
  · rw [e2]
    exact (hWp _).1 (ep' j).2
  · intro x y
    rcases x with i | i <;> rcases y with j | j
    · rw [e1, e1]
      have := hem ((finCongr ha).symm i) ((finCongr ha).symm j)
      simp only [LinearMap.domRestrict₁₂_apply] at this
      simpa [em', Basis.reindex_apply] using this
    · rw [e1, e2, horthm _ (em' i).2 _ (ep' j).2]
      simp
    · rw [e2, e1, horthp _ (ep' i).2 _ (em' j).2]
      simp
    · rw [e2, e2]
      have := hep ((finCongr hb).symm i) ((finCongr hb).symm j)
      simp only [LinearMap.domRestrict₁₂_apply] at this
      simpa [ep', Basis.reindex_apply] using this

theorem rinvMat_unitary {n a b : ℕ} (h : UnitaryFieldData p f F) (hab : a + b = n)
    (B : Basis (Fin a ⊕ Fin b) F (Fin n → F))
    (hon : ∀ x y, gramForm h (1 : Matrix (Fin n) (Fin n) F) (B x) (B y) = if x = y then 1 else 0) :
    ((rinvMat hab B).map h.bar)ᵀ * rinvMat hab B = 1 := by
  ext j k
  obtain ⟨x, rfl⟩ := (rinvIdx hab).surjective j
  obtain ⟨y, rfl⟩ := (rinvIdx hab).surjective k
  have h1 := hon x y
  rw [gramForm_apply, Matrix.one_mulVec] at h1
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply, rinvMat_apply, Equiv.symm_apply_apply,
    (rinvIdx hab).injective.eq_iff]
  rw [← h1]
  rfl

theorem rinv_det_map_bar (h : UnitaryFieldData p f F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ((M.map h.bar)ᵀ).det = h.bar M.det := by
  rw [Matrix.det_transpose]
  have := RingHom.map_det h.bar M
  simpa [RingHom.mapMatrix_apply] using this.symm

theorem rinv_exists_unitary_det_one (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    (T : Matrix (Fin 5) (Fin 5) F) (hT : T * T = 1) (hU : (T.map h.bar)ᵀ * T = 1)
    (hdet : T.det = 1) (h1 : T ≠ 1) :
    ∃ a : ℕ, (a = 2 ∨ a = 4) ∧ ∃ P : Matrix (Fin 5) (Fin 5) F, P.det = 1 ∧
      (P.map h.bar)ᵀ * P = 1 ∧ T * P = P * Matrix.diagonal (rinvSign F 5 a) := by
  classical
  have hf : ∀ v, Matrix.toLin' T (Matrix.toLin' T v) = v := rinv_toLin_involutive T hT
  have hsum := involution_finrank_add h2 (Matrix.toLin' T) hf
  have h5 : finrank F (Fin 5 → F) = 5 := by simp
  obtain ⟨a, ha⟩ : ∃ a, finrank F (LinearMap.ker (Matrix.toLin' T + LinearMap.id)) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, finrank F (LinearMap.ker (Matrix.toLin' T - LinearMap.id)) = b := ⟨_, rfl⟩
  have hab : a + b = 5 := by rw [← ha, ← hb, hsum, h5]
  have ha24 := rinv_dim_two_or_four h2 T hT hdet h1
  rw [ha] at ha24
  obtain ⟨B, hB1, hB2, hon⟩ := rinv_orthonormal_basis h h2 T hT hU a b ha hb
  have hTP := rinvMat_mul_eq hab B T hB1 hB2
  have hPU := rinvMat_unitary h hab B hon
  have hd : h.bar (rinvMat hab B).det * (rinvMat hab B).det = 1 := by
    have := congrArg Matrix.det hPU
    rwa [Matrix.det_mul, rinv_det_map_bar, Matrix.det_one] at this
  have hd0 : (rinvMat hab B).det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hd
    exact zero_ne_one hd
  refine ⟨a, ha24, rinvMat hab B * rinvFirst (rinvMat hab B).det⁻¹, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, rinv_det_first, mul_inv_cancel₀ hd0]
  · calc ((rinvMat hab B * rinvFirst (rinvMat hab B).det⁻¹).map h.bar)ᵀ *
          (rinvMat hab B * rinvFirst (rinvMat hab B).det⁻¹)
        = ((rinvFirst (rinvMat hab B).det⁻¹).map h.bar)ᵀ *
            (((rinvMat hab B).map h.bar)ᵀ * rinvMat hab B) * rinvFirst (rinvMat hab B).det⁻¹ := by
          rw [Matrix.map_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hPU, Matrix.mul_one, rinvFirst_map, rinvFirst, Matrix.diagonal_transpose,
            ← rinvFirst, rinvFirst_mul, map_inv₀, ← mul_inv, hd, inv_one, rinvFirst_one]
  · rw [← Matrix.mul_assoc, hTP, Matrix.mul_assoc, Matrix.mul_assoc, rinvFirst_mul_diagonal_comm]

theorem rinv_exists_unitaryFieldData {q : ℕ} [Finite F] (hF : Nat.card F = q ^ 2) :
    ∃ p f : ℕ, UnitaryFieldData p f F ∧ q = p ^ f := by
  obtain ⟨p, f, hp, -, rfl⟩ := CFSG.GH74.L5U5.exists_prime_pow_of_card_eq_sq hF
  have hf : 1 ≤ f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    subst hf0'
    have : 1 < Nat.card F := Finite.one_lt_card
    simp at hF
    omega
  exact ⟨p, f, ⟨hp.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩, rfl⟩

end Uni

theorem invClasses_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : Odd q) :
    ∃ d₂ d₄ : ↥(StatedSU 5 q F), ∀ t : ↥(StatedSU 5 q F), t * t = 1 → t ≠ 1 →
      (∃ g : ↥(StatedSU 5 q F), g * t * g⁻¹ = d₂) ∨ ∃ g : ↥(StatedSU 5 q F), g * t * g⁻¹ = d₄ := by
  obtain ⟨p, f, h, rfl⟩ := rinv_exists_unitaryFieldData hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact hq.pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  have key : ∀ P : Matrix (Fin 5) (Fin 5) F, P.det = 1 → (P.map h.bar)ᵀ * P = 1 →
      ∃ Pm : ↥(StatedSU 5 (p ^ f) F), (((Pm : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) = P :=
    fun P hdet hP => ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P (by rw [hdet]; exact one_ne_zero),
      (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).2 ⟨hdet, hP⟩⟩, rfl⟩
  have hD2 : (Matrix.diagonal (rinvSign F 5 2)).det = 1 ∧
      ((Matrix.diagonal (rinvSign F 5 2)).map h.bar)ᵀ * Matrix.diagonal (rinvSign F 5 2) = 1 := by
    refine ⟨rinv_det_diagonal_sign_two, ?_⟩
    rw [rinvSign_two, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  have hD4 : (Matrix.diagonal (rinvSign F 5 4)).det = 1 ∧
      ((Matrix.diagonal (rinvSign F 5 4)).map h.bar)ᵀ * Matrix.diagonal (rinvSign F 5 4) = 1 := by
    refine ⟨rinv_det_diagonal_sign_four, ?_⟩
    rw [rinvSign_four, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  obtain ⟨D₂, hD₂⟩ := key _ hD2.1 hD2.2
  obtain ⟨D₄, hD₄⟩ := key _ hD4.1 hD4.2
  refine ⟨D₂, D₄, ?_⟩
  intro t htt ht1
  have hT : ((t : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
      ((t : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 := by
    have := congrArg (fun x : ↥(StatedSU 5 (p ^ f) F) =>
      ((x : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) htt
    simpa using this
  have hT1 : ((t : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) ≠ 1 := fun h' =>
    ht1 (Subtype.ext (Units.ext (by simpa using h')))
  obtain ⟨hdet, hU⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 t.2
  obtain ⟨a, ha, P, hPdet, hPU, hTP⟩ := rinv_exists_unitary_det_one h h2 _ hT hU hdet hT1
  obtain ⟨Pm, hPm⟩ := key P hPdet hPU
  have hmul : ∀ D : ↥(StatedSU 5 (p ^ f) F),
      ((t : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * P =
          P * ((D : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) → t * Pm = Pm * D :=
    fun D hD => by
      refine Subtype.ext (Units.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hPm]
      exact hD
  rcases ha with rfl | rfl
  · left
    exact rinv_group_conj (hmul D₂ (by rw [hD₂]; exact hTP))
  · right
    exact rinv_group_conj (hmul D₄ (by rw [hD₄]; exact hTP))

end CFSG.GH74.Generic.S1
