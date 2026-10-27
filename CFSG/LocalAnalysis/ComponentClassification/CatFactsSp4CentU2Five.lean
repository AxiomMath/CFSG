module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

@[expose] def leviMat (A : GL (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (A : Matrix (Fin 2) (Fin 2) K) 0 0 ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ

theorem formJ_eq_fromBlocks :
    formJ 2 K = fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 := by
  rw [formJ_eq_kron]
  simp [kron, J₁]

theorem leviMat_symplectic (A : GL (Fin 2) K) :
    (leviMat A)ᵀ * formJ 2 K * leviMat A = formJ 2 K := by
  rw [formJ_eq_fromBlocks, leviMat]
  simp only [fromBlocks_transpose, transpose_zero, transpose_transpose, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, ← transpose_mul, Units.inv_mul, transpose_one, neg_zero]

theorem leviMat_mul (A B : GL (Fin 2) K) : leviMat A * leviMat B = leviMat (A * B) := by
  simp only [leviMat, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    _root_.mul_inv_rev, Units.val_mul, transpose_mul]

variable (K) in
@[expose] def levi : GL (Fin 2) K →* StatedSp 2 K where
  toFun A := toSp (leviMat A) (leviMat_symplectic A)
  map_one' := sp_ext (by simp [leviMat, fromBlocks_one])
  map_mul' A B := sp_ext (by simp only [coe_toSp, Subgroup.coe_mul, Units.val_mul, leviMat_mul])

theorem coe_levi (A : GL (Fin 2) K) :
    (((levi K A : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = leviMat A := rfl

theorem levi_injective : Function.Injective (levi K) := by
  intro A B h
  have h' := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_levi, leviMat] at h'
  exact Units.ext (Matrix.fromBlocks_inj.mp h').1

variable {c : K}

@[expose] def scalarGL (hc : c * c = -1) : GL (Fin 2) K where
  val := c • 1
  inv := (-c) • 1
  val_inv := by simp [smul_smul, hc]
  inv_val := by simp [smul_smul, hc]

@[expose] def U0 (hc : c * c = -1) : StatedSp 2 K := levi K (scalarGL hc)

theorem coe_U0 (hc : c * c = -1) :
    (((U0 hc : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (c • 1) 0 0 ((-c) • 1) := by
  simp [U0, coe_levi, leviMat, scalarGL]

theorem U0_mul_U0 (hc : c * c = -1) :
    ((U0 hc : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((U0 hc : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  rw [coe_U0, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp [smul_smul, hc]

theorem levi_mem_centralizer_U0 (hc : c * c = -1) (A : GL (Fin 2) K) :
    levi K A ∈ centralizer ({U0 hc} : Set (StatedSp 2 K)) := by
  rw [mem_centralizer_singleton_iff, U0, ← map_mul, ← map_mul]
  congr 1
  ext1
  simp [scalarGL]

theorem formJ_symplectic : (formJ 2 K)ᵀ * formJ 2 K * formJ 2 K = formJ 2 K := by
  rw [formJ_eq_fromBlocks]
  simp [fromBlocks_transpose, fromBlocks_multiply]

variable (K) in
@[expose] def swapJ : StatedSp 2 K := toSp (formJ 2 K) formJ_symplectic

@[expose] def negOneSp : StatedSp 2 K := toSp (-1) neg_one_symplectic

theorem swapJ_mul_U0 (hc : c * c = -1) : swapJ K * U0 hc = U0 hc * swapJ K * negOneSp := by
  apply sp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, swapJ, negOneSp, coe_toSp, coe_U0,
    formJ_eq_fromBlocks, Matrix.mul_neg, Matrix.mul_one]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
  simp

theorem proj_negOneSp : proj 2 K (negOneSp (K := K)) = 1 := by
  rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
  exact Or.inr rfl

theorem swapJ_not_mem_range : swapJ K ∉ (levi K).range := by
  rintro ⟨A, hA⟩
  have h := congrArg (fun g : StatedSp 2 K =>
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inr 0)) hA
  simp [coe_levi, leviMat, swapJ, formJ_eq_fromBlocks] at h

private theorem card_centralizer_conj' {G : Type*} [Group G] (g x : G) :
    Nat.card (centralizer ({g⁻¹ * x * g} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have h : (centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
      centralizer ({g⁻¹ * x * g} : Set G) := by
    ext z
    rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    simp only [inv_inv, MulAut.conj_symm_apply]
    constructor
    · intro hz
      calc z * (g⁻¹ * x * g) = g⁻¹ * ((g * z * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * z * g⁻¹)) * g := by rw [hz]
        _ = g⁻¹ * x * g * z := by group
    · intro hz
      calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [hz]
        _ = x * (g * z * g⁻¹) := by group
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

theorem card_GL_le_card_centralizer_U0 [Finite K] (h2 : (2 : K) ≠ 0) (hc : c * c = -1) :
    Nat.card (GL (Fin 2) K) ≤
      Nat.card (centralizer ({proj 2 K (U0 hc)} : Set (StatedProj (StatedSp 2 K)))) := by
  set C := centralizer ({proj 2 K (U0 hc)} : Set (StatedProj (StatedSp 2 K))) with hCdef
  set Q := C.comap (proj 2 K) with hQdef
  have hQ : Nat.card Q = Nat.card C * 2 := by
    have hS := (spScalars 2 K).card_eq_card_quotient_mul_card_subgroup
    rw [card_spScalars h2] at hS
    have hQi := Q.card_mul_index
    have hCi := C.card_mul_index
    rw [hQdef, index_comap_of_surjective C proj_surjective, ← hQdef] at hQi
    have hidx : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx)
    rw [hQi, hS, ← hCi]
    ring
  have hle : (levi K).range ≤ Q := by
    rintro _ ⟨A, rfl⟩
    rw [hQdef, mem_comap, hCdef, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (mem_centralizer_singleton_iff.mp (levi_mem_centralizer_U0 hc A))
  have hJQ : swapJ K ∈ Q := by
    rw [hQdef, mem_comap, hCdef, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      swapJ_mul_U0 hc, map_mul, proj_negOneSp, mul_one]
  have hlt : Nat.card (levi K).range * 2 ≤ Nat.card Q := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact swapJ_not_mem_range (Subgroup.eq_of_le_of_card_ge hle hk.le ▸ hJQ)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact hpos.ne' hk
    rw [hk]
    exact Nat.mul_le_mul_left _ (by omega)
  have hrange : Nat.card (levi K).range = Nat.card (GL (Fin 2) K) :=
    (Nat.card_congr (MonoidHom.ofInjective levi_injective).toEquiv).symm
  omega

theorem card_GL_le_card_centralizer_u2 [Finite K] (h2 : (2 : K) ≠ 0) (hc : c * c = -1) :
    Nat.card (GL (Fin 2) K) ≤
      Nat.card (centralizer ({u2 K} : Set (StatedProj (StatedSp 2 K)))) := by
  obtain ⟨g, hg⟩ := exists_conj_T2 h2 (U0 hc) (U0_mul_U0 hc)
  have hu : u2 K = (proj 2 K g)⁻¹ * proj 2 K (U0 hc) * proj 2 K g := by
    rw [u2, ← hg, map_mul, map_mul, map_inv]
  rw [hu, card_centralizer_conj']
  exact card_GL_le_card_centralizer_U0 h2 hc

instance instFactPrimeFiveCentU2 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem le_card_centralizer_u2_zmod_five :
    480 ≤ Nat.card (centralizer ({u2 (ZMod 5)} : Set (StatedProj (StatedSp 2 (ZMod 5))))) := by
  have h := card_GL_le_card_centralizer_u2 (K := ZMod 5) (c := 2) (by decide) (by decide)
  rw [card_GL_field] at h
  simpa [Fin.prod_univ_two, ZMod.card] using h

end CFSG.ComponentClassification.CatFactsSp4
