module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

namespace CFSG.QuasithinUnique.Setup.X7

open scoped Matrix

section Iso

variable {G H : Type*} [Group G] [Group H] {k : Type*} [Field k] {κ κ' κ'' : Type*}
  [Fintype κ] [Fintype κ'] [Fintype κ''] [DecidableEq κ] [DecidableEq κ'] [DecidableEq κ'']

structure MatIso (R : G →* Matrix κ κ k) (R' : G →* Matrix κ' κ' k) (P : Matrix κ' κ k)
    (Q : Matrix κ κ' k) : Prop where
  mul_inv : P * Q = 1
  inv_mul : Q * P = 1
  comm : ∀ g, P * R g = R' g * P

theorem MatIso.refl (R : G →* Matrix κ κ k) : MatIso R R 1 1 :=
  ⟨by simp, by simp, fun g => by simp⟩

theorem MatIso.symm {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k} {P : Matrix κ' κ k}
    {Q : Matrix κ κ' k} (h : MatIso R R' P Q) : MatIso R' R Q P :=
  ⟨h.inv_mul, h.mul_inv, fun g => by
    have h1 : Q * (P * R g) * Q = Q * (R' g * P) * Q := by rw [h.comm g]
    have h2 : Q * (P * R g) * Q = R g * Q := by
      rw [← Matrix.mul_assoc Q P (R g), h.inv_mul, Matrix.one_mul]
    have h3 : Q * (R' g * P) * Q = Q * R' g := by
      rw [Matrix.mul_assoc Q (R' g * P) Q, Matrix.mul_assoc (R' g) P Q, h.mul_inv, Matrix.mul_one]
    exact (h3.symm.trans h1.symm).trans h2⟩

theorem MatIso.trans {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k}
    {R'' : G →* Matrix κ'' κ'' k} {P : Matrix κ' κ k} {Q : Matrix κ κ' k} {P' : Matrix κ'' κ' k}
    {Q' : Matrix κ' κ'' k} (h : MatIso R R' P Q) (h' : MatIso R' R'' P' Q') :
    MatIso R R'' (P' * P) (Q * Q') :=
  ⟨by
    rw [Matrix.mul_assoc P' P (Q * Q'), ← Matrix.mul_assoc P Q Q', h.mul_inv, Matrix.one_mul,
      h'.mul_inv],
    by
    rw [Matrix.mul_assoc Q Q' (P' * P), ← Matrix.mul_assoc Q' P' P, h'.inv_mul, Matrix.one_mul,
      h.inv_mul],
    fun g => by
    rw [Matrix.mul_assoc P' P (R g), h.comm g, ← Matrix.mul_assoc P' (R' g) P, h'.comm g,
      Matrix.mul_assoc (R'' g) P' P]⟩

theorem MatIso.comp {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k} {P : Matrix κ' κ k}
    {Q : Matrix κ κ' k} (h : MatIso R R' P Q) (α : H →* G) :
    MatIso (R.comp α) (R'.comp α) P Q :=
  ⟨h.mul_inv, h.inv_mul, fun g => h.comm (α g)⟩

@[expose] def dualMat (R : G →* Matrix κ κ k) : G →* Matrix κ κ k where
  toFun g := (R g⁻¹)ᵀ
  map_one' := by simp
  map_mul' g h := by simp [mul_inv_rev, Matrix.transpose_mul]

theorem dualMat_apply (R : G →* Matrix κ κ k) (g : G) : dualMat R g = (R g⁻¹)ᵀ := rfl

theorem MatIso.dual {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k} {P : Matrix κ' κ k}
    {Q : Matrix κ κ' k} (h : MatIso R R' P Q) : MatIso (dualMat R') (dualMat R) Pᵀ Qᵀ :=
  ⟨by rw [← Matrix.transpose_mul, h.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, h.mul_inv, Matrix.transpose_one],
    fun g => by
      rw [dualMat_apply, dualMat_apply, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
        h.comm g⁻¹]⟩

theorem dualMat_dualMat (R : G →* Matrix κ κ k) : dualMat (dualMat R) = R := by
  ext g i j
  simp [dualMat_apply]

@[expose] def matMap {k' : Type*} [Field k'] (θ : k →+* k') (R : G →* Matrix κ κ k) :
    G →* Matrix κ κ k' :=
  (θ.mapMatrix : Matrix κ κ k →+* Matrix κ κ k').toMonoidHom.comp R

theorem matMap_apply {k' : Type*} [Field k'] (θ : k →+* k') (R : G →* Matrix κ κ k) (g : G) :
    matMap θ R g = (R g).map θ := rfl

theorem MatIso.map {k' : Type*} [Field k'] (θ : k →+* k') {R : G →* Matrix κ κ k}
    {R' : G →* Matrix κ' κ' k} {P : Matrix κ' κ k} {Q : Matrix κ κ' k} (h : MatIso R R' P Q) :
    MatIso (matMap θ R) (matMap θ R') (P.map θ) (Q.map θ) :=
  ⟨by rw [← Matrix.map_mul, h.mul_inv, Matrix.map_one θ (map_zero θ) (map_one θ)],
    by rw [← Matrix.map_mul, h.inv_mul, Matrix.map_one θ (map_zero θ) (map_one θ)],
    fun g => by rw [matMap_apply, matMap_apply, ← Matrix.map_mul, ← Matrix.map_mul, h.comm g]⟩

theorem MatIso.equiv {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k} {P : Matrix κ' κ k}
    {Q : Matrix κ κ' k} (h : MatIso R R' P Q) : Nonempty ((matRep R).Equiv (matRep R')) :=
  ⟨Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (Matrix.mulVecLin P) (Matrix.mulVecLin Q)
      (by rw [← Matrix.mulVecLin_mul, h.mul_inv, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, h.inv_mul, Matrix.mulVecLin_one]))
    (fun g => by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofLinearMap,
        matRep_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h.comm g])⟩

theorem MatIso.card_eq {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k} {P : Matrix κ' κ k}
    {Q : Matrix κ κ' k} (h : MatIso R R' P Q) : Fintype.card κ = Fintype.card κ' := by
  have e : (κ → k) ≃ₗ[k] (κ' → k) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin P) (Matrix.mulVecLin Q)
      (by rw [← Matrix.mulVecLin_mul, h.mul_inv, Matrix.mulVecLin_one])
      (by rw [← Matrix.mulVecLin_mul, h.inv_mul, Matrix.mulVecLin_one])
  simpa using e.finrank_eq

theorem MatIso.trace_eq {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k} {P : Matrix κ' κ k}
    {Q : Matrix κ κ' k} (h : MatIso R R' P Q) (g : G) : (R' g).trace = (R g).trace := by
  have h1 : R' g = P * R g * Q := by
    rw [h.comm g, Matrix.mul_assoc (R' g) P Q, h.mul_inv, Matrix.mul_one]
  rw [h1, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, h.inv_mul, Matrix.mul_one]

theorem MatIso.exists_of_equiv {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k}
    (e : (matRep R).Equiv (matRep R')) :
    ∃ (P : Matrix κ' κ k) (Q : Matrix κ κ' k), MatIso R R' P Q := by
  let L : (κ → k) ≃ₗ[k] (κ' → k) := e.toLinearEquiv
  have hcomp1 : L.toLinearMap ∘ₗ L.symm.toLinearMap = LinearMap.id := L.comp_symm
  have hcomp2 : L.symm.toLinearMap ∘ₗ L.toLinearMap = LinearMap.id := L.symm_comp
  refine ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap, ?_, ?_,
    fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hcomp1, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, hcomp2, LinearMap.toMatrix'_id]
  · have hg : L.toLinearMap ∘ₗ matRep R g = matRep R' g ∘ₗ L.toLinearMap := e.isIntertwining' g
    have h1 : LinearMap.toMatrix' (matRep R g) = R g := by
      show LinearMap.toMatrix' (Matrix.mulVecLin (R g)) = R g
      rw [← Matrix.toLin'_apply']
      exact LinearMap.toMatrix'_toLin' _
    have h2 : LinearMap.toMatrix' (matRep R' g) = R' g := by
      show LinearMap.toMatrix' (Matrix.mulVecLin (R' g)) = R' g
      rw [← Matrix.toLin'_apply']
      exact LinearMap.toMatrix'_toLin' _
    rw [← h1, ← h2, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' hg

@[expose] def permMat (k : Type*) [Zero k] [One k] (e : κ ≃ κ') : Matrix κ' κ k :=
  Matrix.of fun y x => if e x = y then 1 else 0

omit [Fintype κ'] [DecidableEq κ] [Fintype κ''] [DecidableEq κ''] in
theorem permMat_sum (e : κ ≃ κ') (c : κ → k) (y : κ') :
    ∑ i, (if e i = y then c i else 0) = c (e.symm y) := by
  classical
  have : ∀ i, (if e i = y then c i else 0) = if i = e.symm y then c i else 0 := by
    intro i
    simp only [(Equiv.eq_symm_apply e).symm]
  simp_rw [this]
  simp

omit [Fintype κ'] [DecidableEq κ] [Fintype κ''] [DecidableEq κ''] in
theorem permMat_mulVec_apply (e : κ ≃ κ') (v : κ → k) (y : κ') :
    (permMat k e).mulVec v y = v (e.symm y) := by
  simp only [permMat, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  exact permMat_sum e v y

omit [Fintype κ'] [DecidableEq κ] [Fintype κ''] [DecidableEq κ''] in
theorem permMat_mul_apply (e : κ ≃ κ') (M : Matrix κ κ'' k) (y : κ') (x : κ'') :
    (permMat k e * M) y x = M (e.symm y) x := by
  simp only [permMat, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  exact permMat_sum e (fun j => M j x) y

omit [Fintype κ] [DecidableEq κ] [Fintype κ''] [DecidableEq κ''] in
theorem mul_permMat_apply (e : κ ≃ κ') (M : Matrix κ'' κ' k) (y : κ'') (x : κ) :
    (M * permMat k e) y x = M y (e x) := by
  simp [permMat, Matrix.mul_apply]

omit [Fintype κ'] [Fintype κ''] [DecidableEq κ''] in
theorem permMat_mul_permMat (e : κ ≃ κ') : permMat k e * permMat k e.symm = 1 := by
  ext y y'
  rw [permMat_mul_apply]
  simp [permMat, Matrix.one_apply, eq_comm]

theorem matIso_of_reindex {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k} (e : κ ≃ κ')
    (h : ∀ g x' x, R' g (e x') (e x) = R g x' x) :
    MatIso R R' (permMat k e) (permMat k e.symm) := by
  refine ⟨permMat_mul_permMat e, ?_, fun g => ?_⟩
  · have := permMat_mul_permMat (k := k) e.symm
    rwa [Equiv.symm_symm] at this
  · ext y x
    rw [permMat_mul_apply, mul_permMat_apply]
    have := h g (e.symm y) x
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

theorem MatIso.span_orbit_top {R : G →* Matrix κ κ k} {R' : G →* Matrix κ' κ' k}
    {P : Matrix κ' κ k} {Q : Matrix κ κ' k} (h : MatIso R R' P Q) (Pm : Subgroup G)
    (v : κ' → k) (hspan : Submodule.span k (Set.range fun u : Pm => matRep R' u v) = ⊤) :
    Submodule.span k (Set.range fun u : Pm => matRep R u (Q.mulVec v)) = ⊤ := by
  set S := Submodule.span k (Set.range fun u : Pm => matRep R u (Q.mulVec v)) with hS
  have hcomm : ∀ g, Q * R' g = R g * Q := fun g => h.symm.comm g
  have key : ∀ x ∈ Submodule.span k (Set.range fun u : Pm => matRep R' u v), Q.mulVec x ∈ S := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => Q.mulVec x ∈ S) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨u, rfl⟩
      have : Q.mulVec (matRep R' (u : G) v) = matRep R (u : G) (Q.mulVec v) := by
        rw [matRep_apply, matRep_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm]
      rw [this]
      exact Submodule.subset_span ⟨u, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [Matrix.mulVec_add]
      exact S.add_mem hx hy
    · intro c x _ hx
      rw [Matrix.mulVec_smul]
      exact S.smul_mem c hx
  rw [eq_top_iff]
  intro w _
  have hPw : P.mulVec w ∈ Submodule.span k (Set.range fun u : Pm => matRep R' u v) := by
    rw [hspan]
    exact Submodule.mem_top
  have := key _ hPw
  rwa [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec] at this


end Iso

end CFSG.QuasithinUnique.Setup.X7
