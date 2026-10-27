module

public import CFSG.GH74.Generic.Front.SpNFDefs
public import CFSG.GH74.Generic.Front.DataSp

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.LinearGroups Matrix Subgroup
open scoped MatrixGroups

section TensorH

variable {F : Type} [Field F]

@[expose] def tensM (h : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks (h 0 0 • 1) (h 0 1 • 1) (h 1 0 • 1) (h 1 1 • 1)

theorem tensM_mul (h h' : Matrix (Fin 2) (Fin 2) F) : tensM (h * h') = tensM h * tensM h' := by
  simp only [tensM, fromBlocks_multiply, Matrix.mul_apply, Fin.sum_univ_two, smul_mul_smul]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>
    (ext i j; simp [Matrix.add_apply, Matrix.smul_apply]; ring)

theorem tensM_one : tensM (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  simp [tensM, fromBlocks_one]

theorem tensM_transpose (h : Matrix (Fin 2) (Fin 2) F) : (tensM h)ᵀ = tensM hᵀ := by
  simp [tensM, fromBlocks_transpose]

theorem tensM_comm (h a : Matrix (Fin 2) (Fin 2) F) :
    tensM h * fromBlocks a 0 0 a = fromBlocks a 0 0 a * tensM h := by
  simp only [tensM, fromBlocks_multiply]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem tensM_gram (h G : Matrix (Fin 2) (Fin 2) F) (hdet : h.det = 1) :
    (tensM h)ᵀ * fromBlocks 0 G (-G) 0 * tensM h = fromBlocks 0 G (-G) 0 := by
  rw [tensM_transpose]
  simp only [tensM, fromBlocks_multiply, Matrix.transpose_apply]
  rw [Matrix.det_fin_two] at hdet
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.smul_apply]; ring
  · ext i j; simp [Matrix.smul_apply]; linear_combination (G i j) * hdet
  · ext i j; simp [Matrix.smul_apply]; linear_combination (-G i j) * hdet
  · ext i j; simp [Matrix.smul_apply]; ring

@[expose] def tensHom : SL(2, F) →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F where
  toFun h := tensM (h : Matrix (Fin 2) (Fin 2) F)
  map_one' := by simp [tensM_one]
  map_mul' h h' := by simp [tensM_mul]

theorem tensHom_toHomUnits_val (h : SL(2, F)) :
    ((tensHom.toHomUnits h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      tensM (h : Matrix (Fin 2) (Fin 2) F) := rfl

theorem tensConj_mem (P : GL (Fin 2 ⊕ Fin 2) F) (G : Matrix (Fin 2) (Fin 2) F)
    (hPJ : ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * sp2Gram F *
      ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        fromBlocks 0 G (-G) 0) (h : SL(2, F)) :
    P * tensHom.toHomUnits h * P⁻¹ ∈ StatedSp 2 F := by
  refine Subgroup.subset_closure ?_
  show (((P * tensHom.toHomUnits h * P⁻¹ : GL (Fin 2 ⊕ Fin 2) F)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 *
      ((P * tensHom.toHomUnits h * P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 0 1 (-1) 0
  have hPP : ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by simp
  have hX := tensM_gram (h : Matrix (Fin 2) (Fin 2) F) G h.2
  rw [Units.val_mul, Units.val_mul, tensHom_toHomUnits_val]
  generalize ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Pm at *
  generalize ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Pi at *
  generalize tensM (h : Matrix (Fin 2) (Fin 2) F) = X at *
  have h1 : (Pm * X * Pi)ᵀ * fromBlocks 0 1 (-1) 0 * (Pm * X * Pi) =
      Piᵀ * (Xᵀ * (Pmᵀ * fromBlocks 0 1 (-1) 0 * Pm) * X) * Pi := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [h1, hPJ, hX, ← hPJ]
  have h2 : Piᵀ * (Pmᵀ * fromBlocks 0 1 (-1) 0 * Pm) * Pi =
      (Pm * Pi)ᵀ * fromBlocks 0 1 (-1) 0 * (Pm * Pi) := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [h2, hPP]
  simp

theorem tensM_neg_one : tensM (-1 : Matrix (Fin 2) (Fin 2) F) = -1 := by
  simp only [tensM, Matrix.neg_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq,
    Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, Fin.one_eq_zero_iff,
    neg_zero, zero_smul, neg_smul, one_smul]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

theorem det_neg_one_fin2 : (-1 : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Matrix.det_neg, Matrix.det_one]
  simp

@[expose] def negOneSL : SL(2, F) := ⟨-1, det_neg_one_fin2⟩

theorem tensConj_val (P : GL (Fin 2 ⊕ Fin 2) F) (s : SL(2, F)) :
    ((P * tensHom.toHomUnits s * P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        tensM (s : Matrix (Fin 2) (Fin 2) F) *
        ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  rw [Units.val_mul, Units.val_mul, tensHom_toHomUnits_val]

theorem tensConj_comm (P : GL (Fin 2 ⊕ Fin 2) F) (a : Matrix (Fin 2) (Fin 2) F)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hAP : A * ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * fromBlocks a 0 0 a)
    (s : SL(2, F)) :
    A * ((P * tensHom.toHomUnits s * P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((P * tensHom.toHomUnits s * P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * A := by
  rw [tensConj_val]
  have hPPi : ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by simp
  have hPiP : ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by simp
  have hXB := tensM_comm (s : Matrix (Fin 2) (Fin 2) F) a
  generalize ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Pm at *
  generalize ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Pi at *
  generalize tensM (s : Matrix (Fin 2) (Fin 2) F) = X at *
  generalize fromBlocks a 0 0 a = Ba at *
  have hA : A = Pm * Ba * Pi := by
    rw [← hAP, Matrix.mul_assoc, hPPi, Matrix.mul_one]
  have key1 : Pm * Ba * Pi * (Pm * X * Pi) = Pm * (Ba * X) * Pi := by
    calc Pm * Ba * Pi * (Pm * X * Pi) = Pm * Ba * (Pi * Pm) * (X * Pi) := by
          simp only [Matrix.mul_assoc]
      _ = Pm * Ba * 1 * (X * Pi) := by rw [hPiP]
      _ = Pm * (Ba * X) * Pi := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  have key2 : Pm * X * Pi * (Pm * Ba * Pi) = Pm * (X * Ba) * Pi := by
    calc Pm * X * Pi * (Pm * Ba * Pi) = Pm * X * (Pi * Pm) * (Ba * Pi) := by
          simp only [Matrix.mul_assoc]
      _ = Pm * X * 1 * (Ba * Pi) := by rw [hPiP]
      _ = Pm * (X * Ba) * Pi := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hA, key1, key2, hXB]

theorem tensConj_neg_one (P : GL (Fin 2 ⊕ Fin 2) F) :
    ((P * tensHom.toHomUnits negOneSL * P⁻¹ :
      GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 := by
  rw [tensConj_val]
  have hPPi : ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((P⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by simp
  change _ * tensM (-1 : Matrix (Fin 2) (Fin 2) F) * _ = _
  rw [tensM_neg_one, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hPPi]

variable [Finite F]

theorem goodSub_range_sl2 (hF : Odd (Nat.card F)) (ι : SL(2, F) →* StatedSp 2 F) :
    GoodSub (ThreeModel ↥(StatedSp 2 F)) ι.range := by
  by_cases h4 : 4 ≤ Nat.card F
  · left
    have hSL : Group.IsPerfect SL(2, F) := CFSG.ClassicalInvolution.sl2_isPerfect h4
    exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range ι)
  · right
    have hcard2 : 2 ≤ Nat.card F := Finite.one_lt_card
    have h3 : Nat.card F = 3 := by
      obtain ⟨m, hm⟩ := hF
      omega
    refine ⟨?_, ⟨F, inferInstance, inferInstance, h3, Or.inr ⟨MulEquiv.refl _⟩⟩⟩
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 (fun g hg => hg.1)
    · set S : Set (StatedSp 2 F) := {g | g ∈ ι.range ∧ Odd (orderOf g)} with hS
      rintro _ ⟨s, rfl⟩
      exact map_mem_closure_of_elementary ι S
        (fun e he => ⟨⟨e, rfl⟩, odd_orderOf_map_elementary hF ι he⟩) s

omit [Finite F] in
theorem center_statedSp2_eq (z : StatedSp 2 F) (hz : z ∈ Subgroup.center ↥(StatedSp 2 F)) :
    ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 ∨
      ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 := by
  have hz' := hz
  rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hz'
  obtain ⟨c, hc⟩ := hz'
  have hc2 : (c : F) ^ 2 = 1 := by
    have h := statedSp_gram z
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at h
    have h' := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
    simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal] at h'
    linear_combination h'
  have hc3 : (c : F) * c = 1 := by rw [← sq]; exact hc2
  rcases mul_self_eq_one_iff.1 hc3 with h1 | h1
  · left
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, h1]
    simp
  · right
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, h1]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

@[expose] noncomputable def tensConjHom (P : GL (Fin 2 ⊕ Fin 2) F) (G : Matrix (Fin 2) (Fin 2) F)
    (hPJ : ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * sp2Gram F *
      ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        fromBlocks 0 G (-G) 0) : SL(2, F) →* StatedSp 2 F where
  toFun s := ⟨P * tensHom.toHomUnits s * P⁻¹, tensConj_mem P G hPJ s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s s' := Subtype.ext (by simp only [Subgroup.coe_mul, map_mul]; group)

omit [Finite F] in
theorem tensConjHom_val (P : GL (Fin 2 ⊕ Fin 2) F) (G : Matrix (Fin 2) (Fin 2) F)
    (hPJ : ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * sp2Gram F *
      ((P : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        fromBlocks 0 G (-G) 0) (s : SL(2, F)) :
    ((tensConjHom P G hPJ s : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      P * tensHom.toHomUnits s * P⁻¹ := rfl

theorem exists_good_of_tensorNF (hF : Odd (Nat.card F))
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hNF : TensorNF A) :
    ∃ H : Subgroup ↥(StatedSp 2 F),
      (∀ h ∈ H, A * (((h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (((h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          A) ∧
      (∀ z ∈ Subgroup.center ↥(StatedSp 2 F), z ∈ H) ∧ GoodSub (ThreeModel ↥(StatedSp 2 F)) H := by
  obtain ⟨P, a, G, hPu, hAP, hPJ⟩ := hNF
  obtain ⟨Pu, hPu_val⟩ : ∃ Pu : GL (Fin 2 ⊕ Fin 2) F,
      ((Pu : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = P :=
    ⟨Matrix.GeneralLinearGroup.mk'' P hPu, rfl⟩
  have hPJ' : ((Pu : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ *
      sp2Gram F * ((Pu : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        fromBlocks 0 G (-G) 0 := by rw [hPu_val]; exact hPJ
  have hAP' : A * ((Pu : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((Pu : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        fromBlocks a 0 0 a := by rw [hPu_val]; exact hAP
  refine ⟨(tensConjHom Pu G hPJ').range, ?_, ?_, goodSub_range_sl2 hF _⟩
  · rintro _ ⟨s, rfl⟩
    rw [tensConjHom_val]
    exact tensConj_comm Pu a A hAP' s
  · intro z hz
    rcases center_statedSp2_eq z hz with h1 | h1
    · have : z = 1 := Subtype.ext (Units.ext (by rw [h1]; rfl))
      rw [this]
      exact one_mem _
    · refine ⟨negOneSL, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rw [tensConjHom_val, tensConj_neg_one, h1]

end TensorH

end CFSG.GH74.Generic
