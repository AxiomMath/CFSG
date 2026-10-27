module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Heis

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

section Mat

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

@[expose] def uMat (x : UHeis h) : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  blk3 1 (of fun _ _ => x.a) (of fun _ _ => x.c) 1 (of fun _ _ => -h.bar x.a) 1

@[simp] theorem uMat_ee (x : UHeis h) : uMat x (.inl 0) (.inl 0) = 1 := by simp [uMat]
@[simp] theorem uMat_ez (x : UHeis h) : uMat x (.inl 0) (.inr (.inl 0)) = x.a := rfl
@[simp] theorem uMat_ef (x : UHeis h) : uMat x (.inl 0) (.inr (.inr 0)) = x.c := rfl
@[simp] theorem uMat_ze (x : UHeis h) : uMat x (.inr (.inl 0)) (.inl 0) = 0 := rfl
@[simp] theorem uMat_zz (x : UHeis h) : uMat x (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by
  simp [uMat]
@[simp] theorem uMat_zf (x : UHeis h) :
    uMat x (.inr (.inl 0)) (.inr (.inr 0)) = -h.bar x.a := rfl
@[simp] theorem uMat_fe (x : UHeis h) : uMat x (.inr (.inr 0)) (.inl 0) = 0 := rfl
@[simp] theorem uMat_fz (x : UHeis h) : uMat x (.inr (.inr 0)) (.inr (.inl 0)) = 0 := rfl
@[simp] theorem uMat_ff (x : UHeis h) : uMat x (.inr (.inr 0)) (.inr (.inr 0)) = 1 := by
  simp [uMat]

omit [Field K] in
theorem matrix_ext_hyp {A B : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (h11 : A (.inl 0) (.inl 0) = B (.inl 0) (.inl 0))
    (h12 : A (.inl 0) (.inr (.inl 0)) = B (.inl 0) (.inr (.inl 0)))
    (h13 : A (.inl 0) (.inr (.inr 0)) = B (.inl 0) (.inr (.inr 0)))
    (h21 : A (.inr (.inl 0)) (.inl 0) = B (.inr (.inl 0)) (.inl 0))
    (h22 : A (.inr (.inl 0)) (.inr (.inl 0)) = B (.inr (.inl 0)) (.inr (.inl 0)))
    (h23 : A (.inr (.inl 0)) (.inr (.inr 0)) = B (.inr (.inl 0)) (.inr (.inr 0)))
    (h31 : A (.inr (.inr 0)) (.inl 0) = B (.inr (.inr 0)) (.inl 0))
    (h32 : A (.inr (.inr 0)) (.inr (.inl 0)) = B (.inr (.inr 0)) (.inr (.inl 0)))
    (h33 : A (.inr (.inr 0)) (.inr (.inr 0)) = B (.inr (.inr 0)) (.inr (.inr 0))) : A = B := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    (obtain rfl := Subsingleton.elim i 0) <;> (obtain rfl := Subsingleton.elim j 0) <;> assumption

theorem uMat_mul (x y : UHeis h) : uMat (x * y) = uMat x * uMat y := by
  simp only [uMat, blk3_mul]
  congr 1 <;> ext i j <;> (obtain rfl := Subsingleton.elim i 0) <;>
    (obtain rfl := Subsingleton.elim j 0) <;> simp [Matrix.mul_apply] <;> ring

theorem uMat_one : uMat (1 : UHeis h) = 1 := by
  refine matrix_ext_hyp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

theorem det_uMat (x : UHeis h) : (uMat x).det = 1 := by
  simp [uMat, det_blk3]

theorem uMat_gram (x : UHeis h) :
    ((uMat x).map h.bar)ᵀ * hypGram 1 1 K * uMat x = hypGram 1 1 K := by
  refine (blk3_gram_iff h _ _ _ _ _ _).mpr ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    (obtain rfl := Subsingleton.elim i 0) <;> (obtain rfl := Subsingleton.elim j 0) <;>
    simp [Matrix.mul_apply, h.bar_bar]
  linear_combination x.hc

@[expose] def uSU : UHeis h →* hypSU h 1 1 where
  toFun x := mkHypSU h (uMat x) (uMat_gram x) (det_uMat x)
  map_one' := Subtype.ext (Units.ext uMat_one)
  map_mul' x y := Subtype.ext (Units.ext (uMat_mul x y))

theorem coe_uSU (x : UHeis h) :
    (((uSU x : hypSU h 1 1) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      uMat x := rfl

theorem uSU_injective : Function.Injective (uSU (h := h)) := by
  intro x y hxy
  have h' := congrArg (fun g : hypSU h 1 1 =>
    ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hxy
  simp only [coe_uSU] at h'
  have h1 := congrFun (congrFun h' (.inl 0)) (.inr (.inl 0))
  have h2 := congrFun (congrFun h' (.inl 0)) (.inr (.inr 0))
  simp only [uMat_ez, uMat_ef] at h1 h2
  exact UHeis.ext h1 h2

theorem uSU_mem (x : UHeis h) : uSU x ∈ hypUnitriangular h 1 1 := by
  refine mem_hypUnitriangular.mpr ⟨?_, ?_⟩
  · exact blockTriangular_blk3 (blockTriangular_one : (1 : Matrix (Fin 1) (Fin 1) K).BlockTriangular id)
      (blockTriangular_one : (1 : Matrix (Fin 1) (Fin 1) K).BlockTriangular id)
      (blockTriangular_one : (1 : Matrix (Fin 1) (Fin 1) K).BlockTriangular OrderDual.toDual) _ _ _
  · intro a
    rcases a with i | k | i
    · obtain rfl := Subsingleton.elim i 0
      exact uMat_ee x
    · obtain rfl := Subsingleton.elim k 0
      exact uMat_zz x
    · obtain rfl := Subsingleton.elim i 0
      exact uMat_ff x

theorem exists_uSU_of_mem {g : hypSU h 1 1} (hg : g ∈ hypUnitriangular h 1 1) :
    ∃ x : UHeis h, uSU x = g := by
  obtain ⟨hBT, hdiag⟩ := mem_hypUnitriangular.mp hg
  have hgram := (mem_hypSU.mp g.2).1
  obtain ⟨M, hMg⟩ : ∃ M : Matrix (HypIndex 1 1) (HypIndex 1 1) K,
      ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = M := ⟨_, rfl⟩
  rw [hMg] at hBT hdiag hgram
  have hze : M (.inr (.inl 0)) (.inl 0) = 0 := hBT (by simp)
  have hfe : M (.inr (.inr 0)) (.inl 0) = 0 := hBT (by simp)
  have hfz : M (.inr (.inr 0)) (.inr (.inl 0)) = 0 := hBT (by simp)
  have hee := hdiag (.inl 0)
  have hzz := hdiag (.inr (.inl 0))
  have hff := hdiag (.inr (.inr 0))
  have e1 := congrFun (congrFun hgram (.inr (.inl 0))) (.inr (.inr 0))
  have e2 := congrFun (congrFun hgram (.inr (.inr 0))) (.inr (.inr 0))
  rw [conjTranspose_hypGram_mul_apply] at e1 e2
  simp [Fintype.sum_sum_type, hfz, hzz, hff] at e1 e2
  have hzf : M (.inr (.inl 0)) (.inr (.inr 0)) = -h.bar (M (.inl 0) (.inr (.inl 0))) := by
    linear_combination e1
  refine ⟨⟨M (.inl 0) (.inr (.inl 0)), M (.inl 0) (.inr (.inr 0)), ?_⟩, ?_⟩
  · rw [hzf] at e2
    simp only [map_neg, h.bar_bar] at e2
    linear_combination e2
  · apply Subtype.ext
    apply Units.ext
    rw [coe_uSU, hMg]
    refine matrix_ext_hyp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [hze, hfe, hfz, hee, hzz, hff, hzf]

@[expose] def uEquivU : UHeis h ≃* hypUnitriangular h 1 1 :=
  MulEquiv.ofBijective (uSU.codRestrict (hypUnitriangular h 1 1) uSU_mem)
    ⟨fun x y hxy => uSU_injective (congrArg Subtype.val hxy), fun g => by
      obtain ⟨x, hx⟩ := exists_uSU_of_mem g.2
      exact ⟨x, Subtype.ext hx⟩⟩

variable (h) in
@[expose] def uProjEquiv : hypUnitriangular h 1 1 ≃* hypProjUnitriangular h 1 1 :=
  MulEquiv.ofBijective ((hypProj h 1 1).subgroupMap (hypUnitriangular h 1 1))
    ⟨hypProj_injective_on h le_rfl le_rfl, MonoidHom.subgroupMap_surjective _ _⟩

@[expose] def uBarEquiv : UHeis h ≃* hypProjUnitriangular h 1 1 :=
  uEquivU.trans (uProjEquiv h)

theorem exists_sylow_hypProjUnitriangular :
    ∃ S : Sylow p (hypPSU h 1 1), (S : Subgroup (hypPSU h 1 1)) = hypProjUnitriangular h 1 1 := by
  obtain ⟨-, -, -, -, hS, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  exact hS

end Mat

end CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3
