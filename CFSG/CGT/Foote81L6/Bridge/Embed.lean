module

public import CFSG.CGT.Foote81L6.Bridge.Model
public import CFSG.CGT.Foote81L6.Bridge.GL2
public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Matrix CFSG.Open CFSG.ClassicalGroups

variable {K : Type} [Field K]

@[expose] def πsw : Equiv.Perm (Fin 2 × Fin 3) := Equiv.prodCongrRight fun _ => Equiv.swap 0 1

theorem πsw_symm : πsw.symm = πsw := by
  ext ⟨i, k⟩ <;> simp [πsw]

theorem πsw_mul_self : πsw * πsw = 1 := by
  ext ⟨i, k⟩ <;> simp [πsw, Equiv.Perm.mul_apply]

theorem permMatrix_πsw_mul_self : πsw.permMatrix K * πsw.permMatrix K = 1 := by
  rw [← permMatrix_mul, πsw_mul_self, permMatrix_one]

@[expose] def τGL : GL (Fin 2 × Fin 3) K :=
  ⟨πsw.permMatrix K, πsw.permMatrix K, permMatrix_πsw_mul_self, permMatrix_πsw_mul_self⟩

theorem coe_τGL : ((τGL : GL (Fin 2 × Fin 3) K) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) =
    πsw.permMatrix K := rfl

theorem τGL_mul_self : (τGL : GL (Fin 2 × Fin 3) K) * τGL = 1 :=
  Units.ext permMatrix_πsw_mul_self

theorem permMatrix_πsw_mul_blockDiagonal (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    πsw.permMatrix K * blockDiagonal M =
      blockDiagonal (M ∘ Equiv.swap 0 1) * πsw.permMatrix K := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, πsw_symm]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [submatrix_apply, πsw, Equiv.prodCongrRight_apply, id, blockDiagonal_apply,
    Function.comp_apply]
  by_cases h : Equiv.swap (0 : Fin 3) 1 k = l
  · subst h
    simp
  · have h' : k ≠ Equiv.swap (0 : Fin 3) 1 l := fun h' => h (by rw [h', Equiv.swap_apply_self])
    simp [h, h']

theorem τGL_mul_blockDiagGL (x : Fin 3 → GL (Fin 2) K) :
    τGL * SLnThreeLocal.blockDiagGL K x = SLnThreeLocal.blockDiagGL K (x ∘ Equiv.swap 0 1) * τGL :=
  Units.ext (permMatrix_πsw_mul_blockDiagonal _)

theorem blockDiagonal_mul_permMatrix_πsw_apply (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    (blockDiagonal M * πsw.permMatrix K) (0, 0) (0, 0) = 0 := by
  rw [PEquiv.mul_toMatrix_toPEquiv, πsw_symm]
  simp [πsw, blockDiagonal_apply]

theorem det_τGL : ((τGL : GL (Fin 2 × Fin 3) K) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K).det =
    1 := by
  rw [coe_τGL, det_permutation, πsw, Equiv.Perm.sign_prodCongrRight, Fin.prod_univ_two,
    Equiv.Perm.sign_swap (by decide)]
  simp

theorem six_eq : (6 : ℕ) = 6 ∨ (6 : ℕ) = 7 := Or.inl rfl

theorem embMat_six_smul_one (u : K) :
    SLnThreeLocal.embMat six_eq (u • (1 : Matrix SLnThreeLocal.Blk SLnThreeLocal.Blk K)) =
      u • (1 : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  simp only [SLnThreeLocal.embMat, reindex_apply, submatrix_apply, Equiv.symm_symm]
  rcases hi : SLnThreeLocal.blkEquiv six_eq i with p | p
  · rcases hj : SLnThreeLocal.blkEquiv six_eq j with q | q
    · have hpq : p = q ↔ i = j := by
        rw [← (SLnThreeLocal.blkEquiv six_eq).injective.eq_iff, hi, hj, Sum.inl.injEq]
      simp only [fromBlocks_apply₁₁, Matrix.smul_apply, one_apply, hpq]
    · exact Fin.elim0 q
  · exact Fin.elim0 p

namespace GL2Data

variable {n : ℕ} (D : GL2Data K n)

@[expose] def blk3 (x₁ x₂ x₃ : SD n) : GL (Fin 2 × Fin 3) K :=
  SLnThreeLocal.blockDiagGL K ![D.ι x₁, D.ι x₂, D.ι x₃]

@[expose] def blk (a : PHat n) : GL (Fin 2 × Fin 3) K := D.blk3 a.x₁ a.x₂ a.x₃

theorem blk3_mul (x₁ x₂ x₃ y₁ y₂ y₃ : SD n) :
    D.blk3 (x₁ * y₁) (x₂ * y₂) (x₃ * y₃) = D.blk3 x₁ x₂ x₃ * D.blk3 y₁ y₂ y₃ := by
  rw [blk3, blk3, blk3, ← map_mul]
  congr 1
  funext k
  fin_cases k <;> simp

theorem blk3_one : D.blk3 1 1 1 = 1 := by
  rw [blk3, ← map_one (SLnThreeLocal.blockDiagGL K)]
  congr 1
  funext k
  fin_cases k <;> simp

theorem τGL_mul_blk3 (y₁ y₂ y₃ : SD n) : τGL * D.blk3 y₁ y₂ y₃ = D.blk3 y₂ y₁ y₃ * τGL := by
  rw [blk3, blk3, τGL_mul_blockDiagGL]
  congr 2
  funext k
  fin_cases k <;> rfl

@[expose] def embed' : PHat n →* GL (Fin 2 × Fin 3) K where
  toFun a := D.blk a * τGL ^ a.e.val
  map_one' := by
    change D.blk3 1 1 1 * τGL ^ (0 : ZMod 2).val = 1
    rw [blk3_one, ZMod.val_zero, pow_zero, mul_one]
  map_mul' a b := by
    obtain ⟨a₁, a₂, a₃, ae⟩ := a
    obtain ⟨b₁, b₂, b₃, be⟩ := b
    have hτ0 : (τGL : GL (Fin 2 × Fin 3) K) ^ (0 : ZMod 2).val = 1 := by
      rw [ZMod.val_zero, pow_zero]
    have hτ1 : (τGL : GL (Fin 2 × Fin 3) K) ^ (1 : ZMod 2).val = τGL := by
      rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]
    rcases zmod_two_eq_zero_or_one ae with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one be with rfl | rfl
    · change D.blk3 (a₁ * b₁) (a₂ * b₂) (a₃ * b₃) * τGL ^ (0 + 0 : ZMod 2).val =
        D.blk3 a₁ a₂ a₃ * τGL ^ (0 : ZMod 2).val * (D.blk3 b₁ b₂ b₃ * τGL ^ (0 : ZMod 2).val)
      rw [zero_add, hτ0, blk3_mul]
      simp only [mul_one]
    · change D.blk3 (a₁ * b₁) (a₂ * b₂) (a₃ * b₃) * τGL ^ (0 + 1 : ZMod 2).val =
        D.blk3 a₁ a₂ a₃ * τGL ^ (0 : ZMod 2).val * (D.blk3 b₁ b₂ b₃ * τGL ^ (1 : ZMod 2).val)
      rw [zero_add, hτ0, hτ1, blk3_mul]
      simp only [mul_one, mul_assoc]
    · change D.blk3 (a₁ * b₂) (a₂ * b₁) (a₃ * b₃) * τGL ^ (1 + 0 : ZMod 2).val =
        D.blk3 a₁ a₂ a₃ * τGL ^ (1 : ZMod 2).val * (D.blk3 b₁ b₂ b₃ * τGL ^ (0 : ZMod 2).val)
      rw [add_zero, hτ0, hτ1, blk3_mul]
      simp only [mul_one, mul_assoc]
      rw [τGL_mul_blk3]
    · change D.blk3 (a₁ * b₂) (a₂ * b₁) (a₃ * b₃) * τGL ^ (1 + 1 : ZMod 2).val =
        D.blk3 a₁ a₂ a₃ * τGL ^ (1 : ZMod 2).val * (D.blk3 b₁ b₂ b₃ * τGL ^ (1 : ZMod 2).val)
      rw [PHat.one_add_one_zmod_two, hτ0, hτ1, blk3_mul]
      simp only [mul_one, mul_assoc]
      rw [← mul_assoc τGL, τGL_mul_blk3, mul_assoc, τGL_mul_self, mul_one]

theorem embed'_apply (a : PHat n) : D.embed' a = D.blk a * τGL ^ a.e.val := rfl

@[expose] def embed : PHat n →* GL (Fin 6) K := (SLnThreeLocal.embGL six_eq).comp D.embed'

theorem embed'_injective : Function.Injective D.embed' := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨a₁, a₂, a₃, ae⟩ := a
  rcases zmod_two_eq_zero_or_one ae with rfl | rfl
  · rw [embed'_apply, ZMod.val_zero, pow_zero, mul_one, blk, blk3] at ha
    dsimp only at ha
    rw [← map_one (SLnThreeLocal.blockDiagGL K)] at ha
    have h := SLnThreeLocal.blockDiagGL_injective ha
    have h₁ := congrFun h 0
    have h₂ := congrFun h 1
    have h₃ := congrFun h 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Pi.one_apply,
      Matrix.head_cons, Matrix.cons_val, Matrix.tail_cons] at h₁ h₂ h₃
    rw [← map_one D.ι] at h₁ h₂ h₃
    rw [D.ι_injective h₁, D.ι_injective h₂, D.ι_injective h₃]
    rfl
  · exfalso
    rw [embed'_apply, show (1 : ZMod 2).val = 1 from rfl, pow_one] at ha
    have h1 := congrArg (fun g : GL (Fin 2 × Fin 3) K =>
      (g : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) ((0 : Fin 2), (0 : Fin 3))
        ((0 : Fin 2), (0 : Fin 3))) ha
    simp only [Units.val_mul, blk, blk3, SLnThreeLocal.coe_blockDiagGL, coe_τGL,
      blockDiagonal_mul_permMatrix_πsw_apply, Units.val_one, one_apply_eq] at h1
    exact zero_ne_one h1

theorem embed_injective : Function.Injective D.embed :=
  (SLnThreeLocal.embGL_injective six_eq).comp D.embed'_injective

theorem det_embed' (a : PHat n) :
    ((D.embed' a : GL (Fin 2 × Fin 3) K) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K).det =
      (-1) ^ a.det.val := by
  rw [embed'_apply, Units.val_mul, det_mul, Units.val_pow_eq_pow_val, det_pow, det_τGL, one_pow,
    mul_one, blk, blk3, SLnThreeLocal.coe_blockDiagGL, det_blockDiagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.cons_val, Matrix.tail_cons, det_ι]
  rw [PHat.det, neg_one_pow_val_add, neg_one_pow_val_add]

theorem det_embed (a : PHat n) :
    ((D.embed a : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = (-1) ^ a.det.val := by
  change (SLnThreeLocal.embMat six_eq ((D.embed' a : GL (Fin 2 × Fin 3) K) : Matrix _ _ K)).det = _
  rw [SLnThreeLocal.det_embMat, det_embed']

theorem embed_mem_statedSL {a : PHat n} (ha : a ∈ P n) : D.embed a ∈ StatedSL 6 K := by
  rw [StatedAPI.mem_statedSL_iff, det_embed, mem_P.1 ha, ZMod.val_zero, pow_zero]

theorem embed_c (hn : 2 ≤ n) : D.embed PHat.c = -1 := by
  apply Units.ext
  change SLnThreeLocal.embMat six_eq
    ((D.embed' PHat.c : GL (Fin 2 × Fin 3) K) : Matrix _ _ K) = _
  rw [embed'_apply]
  change SLnThreeLocal.embMat six_eq
    ((D.blk3 SD.z SD.z SD.z * τGL ^ (0 : ZMod 2).val : GL (Fin 2 × Fin 3) K) : Matrix _ _ K) = _
  rw [ZMod.val_zero, pow_zero, mul_one, blk3, D.ι_z hn, SLnThreeLocal.coe_blockDiagGL]
  have h : (fun k : Fin 3 => (((![-1, -1, -1] : Fin 3 → GL (Fin 2) K) k : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) = -1 := by
    funext k
    fin_cases k <;> simp
  rw [h, blockDiagonal_neg, blockDiagonal_one, ← neg_one_smul K (1 : Matrix _ _ K),
    embMat_six_smul_one, Units.val_neg, Units.val_one, neg_one_smul]

theorem neg_one_mem_statedScalars : (-1 : GL (Fin 6) K) ∈ StatedScalars (Fin 6) K := by
  refine ⟨-1, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, Units.val_neg,
    Units.val_one, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_smul, one_smul]

theorem embed_mem_statedScalars_iff (hn : 3 ≤ n) {a : PHat n} :
    D.embed a ∈ StatedScalars (Fin 6) K ↔ a = 1 ∨ a = PHat.c := by
  constructor
  · rintro ⟨u, hu⟩
    have hmat : ((D.embed' a : GL (Fin 2 × Fin 3) K) : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) =
        blockDiagonal fun _ => (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h1 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) hu
      change _ = SLnThreeLocal.embMat six_eq
        ((D.embed' a : GL (Fin 2 × Fin 3) K) : Matrix _ _ K) at h1
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, ← embMat_six_smul_one] at h1
      rw [show (fun _ : Fin 3 => (u : K) • (1 : Matrix (Fin 2) (Fin 2) K)) =
        (u : K) • (1 : Fin 3 → Matrix (Fin 2) (Fin 2) K) from rfl, blockDiagonal_smul,
        blockDiagonal_one]
      exact (SLnThreeLocal.embMat_injective six_eq h1).symm
    obtain ⟨a₁, a₂, a₃, ae⟩ := a
    rcases zmod_two_eq_zero_or_one ae with rfl | rfl
    · rw [embed'_apply, ZMod.val_zero, pow_zero, mul_one, blk, blk3,
        SLnThreeLocal.coe_blockDiagGL] at hmat
      have h := blockDiagonal_injective hmat
      have hk : ∀ x : SD n, ((D.ι x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          (u : K) • (1 : Matrix (Fin 2) (Fin 2) K) → x = 1 ∨ x = SD.z := by
        intro x hx
        have hcomm : ∀ y : SD n, x * y = y * x := by
          intro y
          apply D.ι_injective
          apply Units.ext
          rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hx, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.one_mul, Matrix.mul_one]
        exact SD.eq_one_or_eq_z_of_comm hn (hcomm _) (hcomm _)
      have h₁ := congrFun h 0
      have h₂ := congrFun h 1
      have h₃ := congrFun h 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.cons_val, Matrix.tail_cons] at h₁ h₂ h₃
      have e12 : a₁ = a₂ := D.ι_injective (Units.ext (h₁.trans h₂.symm))
      have e13 : a₁ = a₃ := D.ι_injective (Units.ext (h₁.trans h₃.symm))
      subst e12 e13
      rcases hk a₁ h₁ with rfl | rfl
      · left
        rfl
      · right
        rfl
    · exfalso
      rw [embed'_apply, show (1 : ZMod 2).val = 1 from rfl, pow_one] at hmat
      have h1 := congrFun (congrFun hmat (0, 0)) (0, 0)
      simp only [Units.val_mul, blk, blk3, SLnThreeLocal.coe_blockDiagGL, coe_τGL,
        blockDiagonal_mul_permMatrix_πsw_apply, blockDiagonal_apply_eq, Matrix.smul_apply,
        one_apply_eq, smul_eq_mul, mul_one] at h1
      exact u.ne_zero h1.symm
  · rintro (rfl | rfl)
    · rw [map_one]
      exact Subgroup.one_mem _
    · rw [D.embed_c (by omega)]
      exact neg_one_mem_statedScalars

@[expose] def toSL : P n →* StatedSL 6 K :=
  (D.embed.comp (P n).subtype).codRestrict (StatedSL 6 K) fun a => D.embed_mem_statedSL a.2

theorem coe_toSL (a : P n) : ((D.toSL a : StatedSL 6 K) : GL (Fin 6) K) = D.embed a := rfl

theorem toSL_injective : Function.Injective D.toSL := by
  intro a b h
  apply Subtype.ext
  apply D.embed_injective
  rw [← coe_toSL, ← coe_toSL, h]

@[expose] def toProj : P n →* StatedProj (StatedSL 6 K) :=
  (QuotientGroup.mk' _).comp D.toSL

theorem ker_toProj (hn : 3 ≤ n) : D.toProj.ker = Subgroup.zpowers (cP n) := by
  ext a
  rw [toProj, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, coe_toSL,
    D.embed_mem_statedScalars_iff hn, mem_zpowers_cP]
  constructor
  · rintro (h | h)
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h
  · rintro (rfl | rfl)
    · left
      rfl
    · right
      rfl

end GL2Data

end CFSG.CGT.Foote81L6.Bridge
