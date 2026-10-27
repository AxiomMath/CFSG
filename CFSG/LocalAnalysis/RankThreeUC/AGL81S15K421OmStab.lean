module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421OmModel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421OmProof

open CFSG.Open Matrix

section Polar

variable {F : Type} [Field F] [CharP F 2] (b c : F)

abbrev uI : OmI := Sum.inr (Sum.inr 0)

abbrev vI : OmI := Sum.inr (Sum.inr 1)

@[expose] def polar8 (z z' : OmI → F) : F :=
  StatedQuadMinus 4 F b c (z + z') - StatedQuadMinus 4 F b c z - StatedQuadMinus 4 F b c z'

theorem polar8_apply (z z' : OmI → F) :
    polar8 b c z z' = ∑ k : Fin 3, (z (.inl k) * z' (.inr (.inl k)) +
      z' (.inl k) * z (.inr (.inl k))) + b * (z uI * z' vI + z' uI * z vI) := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  unfold polar8
  simp only [quadMinus_apply, Pi.add_apply, Fin.sum_univ_three]
  linear_combination (z uI * z' uI + c * z vI * z' vI) * h2

theorem polar8_eU (z : OmI → F) : polar8 b c z eU = b * z vI := by
  rw [polar8_apply]
  simp [eU, Pi.single_apply]

end Polar

section Stab

variable {F : Type} [Field F] [CharP F 2] {b c : F}

@[expose] def stabW (F : Type) [Field F] (b c : F) : Subgroup (GL OmI F) where
  carrier := {A | A ∈ isoGrp (StatedQuadMinus 4 F b c) ∧ (A : Matrix OmI OmI F) *ᵥ eU = eU}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := fun {A B} hA hB =>
    ⟨Subgroup.mul_mem _ hA.1 hB.1, by rw [Units.val_mul, ← Matrix.mulVec_mulVec, hB.2, hA.2]⟩
  inv_mem' := fun {A} hA => ⟨Subgroup.inv_mem _ hA.1, by
    have h := congrArg (fun v => ((A⁻¹ : GL OmI F) : Matrix OmI OmI F) *ᵥ v) hA.2
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm⟩

theorem stabW_iso {A : GL OmI F} (hA : A ∈ stabW F b c) (v : OmI → F) :
    StatedQuadMinus 4 F b c ((A : Matrix OmI OmI F) *ᵥ v) = StatedQuadMinus 4 F b c v :=
  hA.1 v

theorem stabW_eU {A : GL OmI F} (hA : A ∈ stabW F b c) : (A : Matrix OmI OmI F) *ᵥ eU = eU :=
  hA.2

theorem polar8_mulVec {A : GL OmI F} (hA : A ∈ stabW F b c) (z z' : OmI → F) :
    polar8 b c ((A : Matrix OmI OmI F) *ᵥ z) ((A : Matrix OmI OmI F) *ᵥ z') = polar8 b c z z' := by
  unfold polar8
  rw [← Matrix.mulVec_add, stabW_iso hA, stabW_iso hA, stabW_iso hA]

theorem stabW_vcoord (hb : b ≠ 0) {A : GL OmI F} (hA : A ∈ stabW F b c) (z : OmI → F) :
    ((A : Matrix OmI OmI F) *ᵥ z) vI = z vI := by
  have h := polar8_mulVec hA z eU
  rw [stabW_eU hA, polar8_eU, polar8_eU] at h
  exact mul_left_cancel₀ hb h

theorem stabW_col_u {A : GL OmI F} (hA : A ∈ stabW F b c) (i : OmI) :
    (A : Matrix OmI OmI F) i uI = if i = uI then 1 else 0 := by
  have h := congrFun (stabW_eU hA) i
  have h1 : ((A : Matrix OmI OmI F) *ᵥ eU) i = (A : Matrix OmI OmI F) i uI := by
    rw [eU, Matrix.mulVec_single]
    simp
  rw [h1] at h
  rw [h]
  simp [eU, Pi.single_apply]

theorem stabW_row_v (hb : b ≠ 0) {A : GL OmI F} (hA : A ∈ stabW F b c) (j : OmI) :
    (A : Matrix OmI OmI F) vI j = if j = vI then 1 else 0 := by
  have h := stabW_vcoord hb hA (Pi.single j 1)
  have h1 : ((A : Matrix OmI OmI F) *ᵥ Pi.single j 1) vI = (A : Matrix OmI OmI F) vI j := by
    rw [Matrix.mulVec_single]
    simp
  rw [h1] at h
  rw [h]
  simp [Pi.single_apply, eq_comm]

end Stab

section Block

variable {F : Type} [Field F] [CharP F 2] {b c : F}

@[expose] def e6 : Fin 3 ⊕ Fin 3 → OmI := Sum.elim Sum.inl (fun i => Sum.inr (Sum.inl i))

theorem e6_injective : Function.Injective e6 := by
  rintro (i | i) (j | j) h <;> simp_all [e6]

theorem e6_ne_uI (p : Fin 3 ⊕ Fin 3) : e6 p ≠ uI := by
  rcases p with i | i <;> simp [e6]

theorem e6_ne_vI (p : Fin 3 ⊕ Fin 3) : e6 p ≠ vI := by
  rcases p with i | i <;> simp [e6]

@[expose] def zblk (A : Matrix OmI OmI F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  A.submatrix e6 e6

theorem zblk_one : zblk (1 : Matrix OmI OmI F) = 1 :=
  Matrix.submatrix_one e6 e6_injective

theorem zblk_mul {A B : Matrix OmI OmI F} (hA : ∀ p, A (e6 p) uI = 0)
    (hB : ∀ q, B vI (e6 q) = 0) : zblk (A * B) = zblk A * zblk B := by
  ext p q
  simp only [zblk, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hu := hA p
  have hv := hB q
  simp only [Fin.sum_univ_two]
  have e1 : (Sum.inr (Sum.inr 0) : OmI) = uI := rfl
  have e2 : (Sum.inr (Sum.inr 1) : OmI) = vI := rfl
  rw [e1, e2, hu, hv]
  simp [e6]

@[expose] def rho0 (hb : b ≠ 0) :
    ↥(stabW F b c) →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F where
  toFun A := zblk ((A : GL OmI F) : Matrix OmI OmI F)
  map_one' := zblk_one
  map_mul' A B := by
    rw [Subgroup.coe_mul, Units.val_mul]
    exact zblk_mul (fun p => by rw [stabW_col_u A.2, if_neg (e6_ne_uI p)])
      (fun q => by rw [stabW_row_v hb B.2, if_neg (e6_ne_vI q)])

@[expose] def rho (hb : b ≠ 0) : ↥(stabW F b c) →* GL (Fin 3 ⊕ Fin 3) F :=
  (rho0 hb).toHomUnits

theorem rho_val (hb : b ≠ 0) (A : ↥(stabW F b c)) :
    ((rho hb A : GL (Fin 3 ⊕ Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      zblk ((A : GL OmI F) : Matrix OmI OmI F) := rfl

end Block

section Symp

variable {F : Type} [Field F] [CharP F 2] {b c : F}

@[expose] def emb (z : Fin 3 ⊕ Fin 3 → F) : OmI → F :=
  Sum.elim (fun i => z (Sum.inl i)) (Sum.elim (fun i => z (Sum.inr i)) (fun _ => 0))

theorem emb_uI (z : Fin 3 ⊕ Fin 3 → F) : emb z uI = 0 := rfl

theorem emb_vI (z : Fin 3 ⊕ Fin 3 → F) : emb z vI = 0 := rfl

@[expose] def bil (z z' : Fin 3 ⊕ Fin 3 → F) : F :=
  ∑ k : Fin 3, (z (.inl k) * z' (.inr k) + z' (.inl k) * z (.inr k))

theorem polar8_emb (z z' : Fin 3 ⊕ Fin 3 → F) : polar8 b c (emb z) (emb z') = bil z z' := by
  rw [polar8_apply]
  simp only [emb_uI, emb_vI, mul_zero, zero_mul, add_zero]
  simp [bil, emb]

theorem mulVec_emb (z : Fin 3 ⊕ Fin 3 → F) (A : Matrix OmI OmI F) (p : Fin 3 ⊕ Fin 3) :
    (A *ᵥ emb z) (e6 p) = (zblk A *ᵥ z) p := by
  simp only [Matrix.mulVec, dotProduct, zblk, Matrix.submatrix_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type (fun q => A (e6 p) (e6 q) * z q)]
  simp [emb, e6, Fin.sum_univ_two]

theorem polar8_mulVec_emb (hb : b ≠ 0) {A : GL OmI F} (hA : A ∈ stabW F b c)
    (z z' : Fin 3 ⊕ Fin 3 → F) :
    polar8 b c ((A : Matrix OmI OmI F) *ᵥ emb z) ((A : Matrix OmI OmI F) *ᵥ emb z') =
      bil (zblk (A : Matrix OmI OmI F) *ᵥ z) (zblk (A : Matrix OmI OmI F) *ᵥ z') := by
  rw [polar8_apply, stabW_vcoord hb hA, stabW_vcoord hb hA, emb_vI, emb_vI]
  have h1 : ∀ (w : Fin 3 ⊕ Fin 3 → F) (k : Fin 3),
      ((A : Matrix OmI OmI F) *ᵥ emb w) (.inl k) = (zblk (A : Matrix OmI OmI F) *ᵥ w) (.inl k) :=
    fun w k => mulVec_emb w _ (.inl k)
  have h2 : ∀ (w : Fin 3 ⊕ Fin 3 → F) (k : Fin 3),
      ((A : Matrix OmI OmI F) *ᵥ emb w) (.inr (.inl k)) =
        (zblk (A : Matrix OmI OmI F) *ᵥ w) (.inr k) :=
    fun w k => mulVec_emb w _ (.inr k)
  simp only [h1, h2, bil, mul_zero, zero_mul, add_zero]

theorem bil_zblk (hb : b ≠ 0) {A : GL OmI F} (hA : A ∈ stabW F b c) (z z' : Fin 3 ⊕ Fin 3 → F) :
    bil (zblk (A : Matrix OmI OmI F) *ᵥ z) (zblk (A : Matrix OmI OmI F) *ᵥ z') = bil z z' := by
  rw [← polar8_mulVec_emb hb hA, polar8_mulVec hA, polar8_emb]

theorem toLinearMap₂'_J (z z' : Fin 3 ⊕ Fin 3 → F) :
    Matrix.toLinearMap₂' F (Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) F) 1 (-1) 0) z z' =
      bil z z' := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  simp only [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, bil]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Finset.sum_add_distrib,
    mul_add, Finset.sum_neg_distrib]
  rw [CharTwo.neg_eq, add_comm]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

theorem mat_eq_of_form {n : Type} [Fintype n] [DecidableEq n] (J g : Matrix n n F)
    (h : ∀ x y, Matrix.toLinearMap₂' F J (g *ᵥ x) (g *ᵥ y) = Matrix.toLinearMap₂' F J x y) :
    gᵀ * J * g = J := by
  have key : ∀ x y, Matrix.toLinearMap₂' F J (g *ᵥ x) (g *ᵥ y) =
      Matrix.toLinearMap₂' F (gᵀ * J * g) x y := by
    intro x y
    rw [← Matrix.toLinearMap₂'_comp]
    simp [Matrix.toLin'_apply]
  have h2 : (Matrix.toLinearMap₂' F (gᵀ * J * g) : (n → F) →ₗ[F] (n → F) →ₗ[F] F) =
      Matrix.toLinearMap₂' F J := by
    apply LinearMap.ext₂
    intro x y
    rw [← key, h]
  have h3 := congrArg (LinearMap.toMatrix₂' F) h2
  rwa [LinearMap.toMatrix'_toLinearMap₂', LinearMap.toMatrix'_toLinearMap₂'] at h3

theorem rho_mem_statedSp (hb : b ≠ 0) (A : ↥(stabW F b c)) : rho hb A ∈ StatedSp 3 F := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff, rho_val]
  apply mat_eq_of_form
  intro x y
  rw [toLinearMap₂'_J, toLinearMap₂'_J]
  exact bil_zblk hb A.2 x y

end Symp

section Reflection

variable {F : Type} [Field F] [CharP F 2] {b c : F}

@[expose] def rWmat (b : F) : Matrix OmI OmI F := 1 + Matrix.single uI vI b

theorem rWmat_mul_self : rWmat b * rWmat b = 1 := by
  have h2 : b + b = 0 := by
    have := K421SpProof.two_eq_zero_F F
    linear_combination b * this
  have huv : (vI : OmI) ≠ uI := by decide
  simp only [rWmat, add_mul, mul_add, one_mul, mul_one]
  rw [Matrix.single_mul_single_of_ne b uI vI uI huv b, add_zero, add_assoc, ← Matrix.single_add,
    h2, Matrix.single_zero, add_zero]

@[expose] def rWGL (b : F) : GL OmI F := ⟨rWmat b, rWmat b, rWmat_mul_self, rWmat_mul_self⟩

theorem rWmat_apply (b : F) (i j : OmI) :
    rWmat b i j = (if i = j then 1 else 0) + (if uI = i ∧ vI = j then b else 0) := by
  simp [rWmat, Matrix.single, Matrix.one_apply]

theorem rWmat_mulVec (b : F) (z : OmI → F) (i : OmI) :
    (rWmat b *ᵥ z) i = z i + (if i = uI then b * z vI else 0) := by
  simp only [rWmat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, Pi.add_apply,
    Function.update_apply]
  simp

end Reflection

section Kernel

variable {F : Type} [Field F] [CharP F 2] {b c : F}

theorem OmI_cases (i : OmI) : (∃ p, i = e6 p) ∨ i = uI ∨ i = vI := by
  rcases i with k | k | t
  · exact Or.inl ⟨Sum.inl k, rfl⟩
  · exact Or.inl ⟨Sum.inr k, rfl⟩
  · fin_cases t
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem quadMinus_of_coords (z : OmI → F) :
    StatedQuadMinus 4 F b c z = z (.inl 0) * z (.inr (.inl 0)) + z (.inl 1) * z (.inr (.inl 1)) +
      z (.inl 2) * z (.inr (.inl 2)) + z uI ^ 2 + b * z uI * z vI + c * z vI ^ 2 := by
  rw [quadMinus_apply, Fin.sum_univ_three]

theorem eq_one_or_rWGL (hb : b ≠ 0) {A : GL OmI F} (hA : A ∈ stabW F b c)
    (hz : zblk (A : Matrix OmI OmI F) = 1) : A = 1 ∨ A = rWGL b := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  set M : Matrix OmI OmI F := (A : Matrix OmI OmI F) with hM
  have hcol : ∀ i, M i uI = if i = uI then 1 else 0 := stabW_col_u hA
  have hrow : ∀ j, M vI j = if j = vI then 1 else 0 := stabW_row_v hb hA
  have hzz : ∀ p q, M (e6 p) (e6 q) = if p = q then 1 else 0 := fun p q => by
    have := congrFun (congrFun hz p) q
    simpa [zblk, Matrix.one_apply] using this
  have hiso : ∀ j, StatedQuadMinus 4 F b c (fun i => M i j) =
      StatedQuadMinus 4 F b c (Pi.single j 1) := by
    intro j
    have := stabW_iso hA (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at this
    exact this
  have hiso2 : ∀ q, StatedQuadMinus 4 F b c ((fun i => M i (e6 q)) + (fun i => M i vI)) =
      StatedQuadMinus 4 F b c (Pi.single (e6 q) 1 + Pi.single vI 1) := by
    intro q
    have := stabW_iso hA (Pi.single (e6 q) 1 + Pi.single vI 1)
    rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    exact this
  have hx : ∀ (q : Fin 3 ⊕ Fin 3) (k : Fin 3), M (.inl k) (e6 q) =
      if (Sum.inl k : Fin 3 ⊕ Fin 3) = q then 1 else 0 := fun q k => hzz (.inl k) q
  have hy : ∀ (q : Fin 3 ⊕ Fin 3) (k : Fin 3), M (.inr (.inl k)) (e6 q) =
      if (Sum.inr k : Fin 3 ⊕ Fin 3) = q then 1 else 0 := fun q k => hzz (.inr k) q
  have hv : ∀ q : Fin 3 ⊕ Fin 3, M vI (e6 q) = 0 := fun q => by
    rw [hrow, if_neg (e6_ne_vI q)]
  have hell : ∀ q, M uI (e6 q) = 0 := by
    intro q
    have h := hiso (e6 q)
    rw [quadMinus_of_coords, quadMinus_of_coords] at h
    simp only [hx, hy, hv] at h
    rcases q with i | i <;> fin_cases i <;> simpa [Pi.single_apply, e6, uI, vI] using h
  have hvv : M vI vI = 1 := by rw [hrow, if_pos rfl]
  have h3 : M (.inl 0) vI * M (.inr (.inl 0)) vI + M (.inl 1) vI * M (.inr (.inl 1)) vI +
      M (.inl 2) vI * M (.inr (.inl 2)) vI + M uI vI ^ 2 + b * M uI vI = 0 := by
    have h := hiso vI
    rw [quadMinus_of_coords, quadMinus_of_coords] at h
    simp only [hvv] at h
    simp [Pi.single_apply, uI, vI] at h
    linear_combination h
  have ha : ∀ p, M (e6 p) vI = 0 := by
    intro p
    have key : ∀ q : Fin 3 ⊕ Fin 3,
        StatedQuadMinus 4 F b c ((fun i => M i (e6 q)) + (fun i => M i vI)) =
          StatedQuadMinus 4 F b c (Pi.single (e6 q) 1 + Pi.single vI 1) := hiso2
    rcases p with i | i
    · have h := key (.inr i)
      rw [quadMinus_of_coords, quadMinus_of_coords] at h
      simp only [Pi.add_apply, hx, hy, hv, hell, hvv] at h
      fin_cases i <;> simp [Pi.single_apply, e6, uI, vI] at h ⊢ <;> linear_combination h - h3
    · have h := key (.inl i)
      rw [quadMinus_of_coords, quadMinus_of_coords] at h
      simp only [Pi.add_apply, hx, hy, hv, hell, hvv] at h
      fin_cases i <;> simp [Pi.single_apply, e6, uI, vI] at h ⊢ <;> linear_combination h - h3
  have hmb : M uI vI = 0 ∨ M uI vI = b := by
    have e0 : M (.inl 0) vI = 0 := ha (.inl 0)
    have e1 : M (.inl 1) vI = 0 := ha (.inl 1)
    have e2 : M (.inl 2) vI = 0 := ha (.inl 2)
    have hm0 : M uI vI * (M uI vI + b) = 0 := by
      rw [e0, e1, e2] at h3
      linear_combination h3
    rcases mul_eq_zero.1 hm0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h0 - b * h2)
  have huv : (uI : OmI) ≠ vI := by decide
  have key : ∀ i j, M i j = (if i = j then 1 else 0) + (if uI = i ∧ vI = j then M uI vI else 0) := by
    intro i j
    have n1 : ∀ p, ¬ uI = e6 p := fun p h => e6_ne_uI p h.symm
    have n2 : ∀ p, ¬ vI = e6 p := fun p h => e6_ne_vI p h.symm
    rcases OmI_cases i with ⟨p, rfl⟩ | rfl | rfl <;> rcases OmI_cases j with ⟨q, rfl⟩ | rfl | rfl
    · simp [hzz, e6_injective.eq_iff, n1]
    · simp [hcol, e6_ne_uI, n1]
    · simp [ha, e6_ne_vI, n1]
    · simp [hell, e6_ne_uI, Ne.symm (e6_ne_uI q), n2]
    · simp [hcol]
    · simp
    · simp [hv, e6_ne_vI, n2, Ne.symm (e6_ne_vI q)]
    · simp [hrow, huv, huv.symm]
    · simp [hvv]
  rcases hmb with h0 | hb'
  · left
    apply Units.ext
    ext i j
    rw [show ((A : GL OmI F) : Matrix OmI OmI F) i j = M i j from rfl, key, h0]
    simp [Matrix.one_apply]
  · right
    apply Units.ext
    ext i j
    rw [show ((A : GL OmI F) : Matrix OmI OmI F) i j = M i j from rfl, key, hb']
    show _ = rWmat b i j
    rw [rWmat_apply]

end Kernel

end K421OmProof

end CFSG.LocalAnalysis.RankThreeUC.S15
