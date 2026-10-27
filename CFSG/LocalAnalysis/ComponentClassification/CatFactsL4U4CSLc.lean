module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace CSL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL

variable {F : Type} [Field F]

theorem mul_conj_mul_inv {X : Type*} [Group X] (φ : MulAut X) (x : X) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
    map_mul, map_inv, MulAut.apply_inv_self]

theorem neg_one_ne_zero' : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero

@[expose] def kSL : SpecialLinearGroup (Fin 4) F :=
  ⟨kZero (-1), by rw [det_kZero]; norm_num⟩

@[expose] def sSL : SpecialLinearGroup (Fin 4) F := ⟨sZ, det_sZ⟩

@[expose] def uSL {c : F} (hc : (2 * c ^ 2) ^ 2 = 1) : SpecialLinearGroup (Fin 4) F :=
  ⟨eK (-1) c c, by rw [det_eK]; linear_combination hc⟩

theorem toGL_kSL : SpecialLinearGroup.toGL (kSL : SpecialLinearGroup (Fin 4) F) =
    kG (neg_one_ne_zero' (F := F)) :=
  Units.ext (by rw [coe_kG]; rfl)

theorem conjAut_kG_eq : conjAut 4 F (kG (neg_one_ne_zero' (F := F))) =
    MulAut.conj (proj 4 F kSL) := by
  rw [← toGL_kSL, conjAut_toGL]

theorem eK_comm_of_comm {X : Matrix (Fin 4) (Fin 4) F} (l a b : F)
    (hX : X * kZero l = kZero l * X) : X * eK l a b = eK l a b * X := by
  rw [← smul_one_add_smul_kZero, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hX]

theorem mem_CK_of_mem_SK {l : F} (hl : l ≠ 0) {s : SpecialLinearGroup (Fin 4) F}
    (hs : s ∈ SK F hl) : s ∈ CK F hl :=
  (Subgroup.commutator_le.2 fun _ ha _ hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) : SK F hl ≤ CK F hl) hs

theorem conj_mem_CA_of_eK {U : SpecialLinearGroup (Fin 4) F} {l a b : F} (hl : l ≠ 0)
    (hU : (U : Matrix (Fin 4) (Fin 4) F) = eK l a b) : MulAut.conj (proj 4 F U) ∈ CA F hl := by
  rintro _ ⟨s, hs, rfl⟩
  have hsC := (mem_CK_iff hl).1 (mem_CK_of_mem_SK hl hs)
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hU]
  exact (eK_comm_of_comm l a b hsC).symm

theorem proj_sSL_sq : proj 4 F sSL ^ 2 = 1 := by
  rw [← map_pow]
  convert map_one (proj 4 F)
  apply Subtype.ext
  rw [sq, Matrix.SpecialLinearGroup.coe_mul]
  exact sZ_mul_sZ

theorem sSL_inv : (sSL : SpecialLinearGroup (Fin 4) F)⁻¹ = sSL := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact sZ_mul_sZ

theorem conj_sSL_apply (Y : SpecialLinearGroup (Fin 4) F) :
    ((sSL * Y * sSL⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      sZ * (Y : Matrix (Fin 4) (Fin 4) F) * sZ := by
  rw [sSL_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rfl

theorem conj_sSL_mem_CK {Y : SpecialLinearGroup (Fin 4) F} (hY : Y ∈ CK F neg_one_ne_zero') :
    sSL * Y * sSL⁻¹ ∈ CK F neg_one_ne_zero' := by
  rw [mem_CK_iff] at hY ⊢
  rw [conj_sSL_apply]
  have h1 : sZ * kZero (-1 : F) = -(kZero (-1) * sZ) := by
    have := sZ_kZero (-1 : F)
    calc sZ * kZero (-1 : F) = sZ * kZero (-1) * sZ * sZ := by
          rw [Matrix.mul_assoc _ sZ, sZ_mul_sZ, Matrix.mul_one]
      _ = -(kZero (-1) * sZ) := by rw [this, Matrix.neg_mul]
  calc sZ * (Y : Matrix (Fin 4) (Fin 4) F) * sZ * kZero (-1) =
      -(sZ * ((Y : Matrix (Fin 4) (Fin 4) F) * kZero (-1)) * sZ) := by
        rw [Matrix.mul_assoc _ sZ, h1, Matrix.mul_neg]; simp only [Matrix.mul_assoc]
    _ = -(sZ * (kZero (-1) * (Y : Matrix (Fin 4) (Fin 4) F)) * sZ) := by rw [hY]
    _ = kZero (-1) * (sZ * (Y : Matrix (Fin 4) (Fin 4) F) * sZ) := by
        rw [← Matrix.mul_assoc sZ, h1]; simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

theorem conj_sSL_mem_JK {x : projectiveSL 4 F} (hx : x ∈ JK F neg_one_ne_zero') :
    MulAut.conj (proj 4 F sSL) x ∈ JK F neg_one_ne_zero' := by
  obtain ⟨Y, hY, rfl⟩ := hx
  refine ⟨sSL * Y * sSL⁻¹, ?_, by rw [MulAut.conj_apply, map_mul, map_mul, map_inv]⟩
  have hle : (SK F neg_one_ne_zero').map (MulAut.conj sSL).toMonoidHom ≤
      SK F neg_one_ne_zero' := by
    rw [SK, Subgroup.map_commutator]
    apply Subgroup.commutator_mono <;>
    · rintro _ ⟨Z, hZ, rfl⟩
      exact conj_sSL_mem_CK hZ
  exact hle ⟨Y, hY, rfl⟩

theorem conj_sSL_comm [Finite F] :
    MulAut.conj (proj 4 F sSL) * conjAut 4 F (kG neg_one_ne_zero') =
      conjAut 4 F (kG neg_one_ne_zero') * MulAut.conj (proj 4 F sSL) := by
  rw [← conjAut_toGL, ← map_mul, ← map_mul]
  have h : SpecialLinearGroup.toGL sSL * kG (neg_one_ne_zero' (F := F)) =
      GeneralLinearGroup.scalar (Fin 4) (-1) * (kG neg_one_ne_zero' * SpecialLinearGroup.toGL sSL)
      := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_kG, GeneralLinearGroup.coe_scalar]
    have := sZ_kZero (-1 : F)
    calc (sZ : Matrix (Fin 4) (Fin 4) F) * kZero (-1) = sZ * kZero (-1) * sZ * sZ := by
          rw [Matrix.mul_assoc _ sZ, sZ_mul_sZ, Matrix.mul_one]
      _ = Matrix.scalar (Fin 4) ((-1 : Fˣ) : F) * (kZero (-1) * sZ) := by
          have hd : (Matrix.diagonal fun _ : Fin 4 => (-1 : F)) = -1 := by
            rw [← Matrix.diagonal_one, ← Matrix.diagonal_neg]
          rw [this, Matrix.scalar_apply, Units.val_neg, Units.val_one, hd, neg_one_mul,
            Matrix.neg_mul]
  rw [h, map_mul, (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).2
    ⟨_, rfl⟩, one_mul]

theorem conj_sSL_inv [Finite F] {B : GL (Fin 4) F} {a b : F}
    (hB : (B : Matrix (Fin 4) (Fin 4) F) = eK (-1) a b) :
    MulAut.conj (proj 4 F sSL) * conjAut 4 F B * (MulAut.conj (proj 4 F sSL))⁻¹ =
      (conjAut 4 F B)⁻¹ := by
  rw [← conjAut_toGL, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  have hn : a ^ 2 - (-1) * b ^ 2 ≠ 0 := by
    intro h0
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
    rw [hB, det_eK, h0] at hd
    simp at hd
  rw [← mul_eq_one_iff_eq_inv, ← map_mul]
  apply (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).2
  refine ⟨Units.mk0 _ hn, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, Units.val_mul, Units.val_mul, Units.val_mul, hB,
    Units.val_mk0]
  rw [sSL_inv]
  change Matrix.scalar (Fin 4) (a ^ 2 - (-1) * b ^ 2) = sZ * eK (-1) a b * sZ * eK (-1) a b
  rw [sZ_eK, eK_mul_eK]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eK, Matrix.scalar_apply] <;> ring

theorem proj_uSL_sq {c : F} (hc : (2 * c ^ 2) ^ 2 = 1) :
    proj 4 F (uSL hc) ^ 2 = proj 4 F kSL := by
  have hε : (2 * c ^ 2 : F) ≠ 0 := by
    intro h0
    rw [h0] at hc
    norm_num at hc
  set ε : Fˣ := Units.mk0 _ hε with hεdef
  have hε4 : ε ^ 4 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hεdef, Units.val_mk0, Units.val_one,
      show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hc, one_pow])
  have h : uSL hc ^ 2 = kSL * scalarElement ε hε4 := by
    apply Subtype.ext
    rw [sq, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    change eK (-1) c c * eK (-1) c c = kZero (-1) * Matrix.scalar (Fin 4) (ε : F)
    rw [eK_mul_eK, hεdef, Units.val_mk0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [eK, kZero, Matrix.scalar_apply, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring
  rw [← map_pow, h, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars ε hε4), mul_one]

theorem conj_uSL_mem_CA {c : F} (hc : (2 * c ^ 2) ^ 2 = 1) :
    MulAut.conj (proj 4 F (uSL hc)) ∈ CA F neg_one_ne_zero' :=
  conj_mem_CA_of_eK neg_one_ne_zero' rfl

theorem exists_c [Fintype F] [DecidableEq F] (hneg : ¬ IsSquare (-1 : F)) (h2 : (2 : F) ≠ 0) :
    ∃ c : F, (2 * c ^ 2) ^ 2 = 1 := by
  have hsq : IsSquare (2 : F) ∨ IsSquare (-2 : F) := by
    by_cases h : IsSquare (2 : F)
    · exact Or.inl h
    · right
      have h1 := quadraticChar_neg_one_iff_not_isSquare.2 h
      have h2' := quadraticChar_neg_one_iff_not_isSquare.2 hneg
      have h3 : quadraticChar F (-2) = 1 := by
        rw [show (-2 : F) = -1 * 2 by ring, map_mul, h1, h2']
        norm_num
      exact (quadraticChar_one_iff_isSquare (neg_ne_zero.2 h2)).1 h3
  rcases hsq with ⟨d, hd⟩ | ⟨d, hd⟩
  · have hd2 : d ^ 2 = 2 := by rw [sq, ← hd]
    refine ⟨d⁻¹, ?_⟩
    rw [inv_pow, hd2, mul_inv_cancel₀ h2, one_pow]
  · have hd2 : d ^ 2 = -2 := by rw [sq, ← hd]
    have h3 : (2 : F) * (-2)⁻¹ = -1 := by
      rw [mul_inv_eq_iff_eq_mul₀ (neg_ne_zero.2 h2)]
      ring
    refine ⟨d⁻¹, ?_⟩
    rw [inv_pow, hd2, h3]
    norm_num

end CSL

end CFSG.ComponentClassification.CatFactsL4U4
