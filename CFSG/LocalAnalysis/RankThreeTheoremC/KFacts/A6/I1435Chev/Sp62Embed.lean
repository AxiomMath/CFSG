module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Sp62
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossPSU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Sp62

open Subgroup Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LieType.SteinbergBR.EvenSp (planeMat planeHom planeHom_val planeMat_mul
  planeMat_transpose planeMat_gram planeMat_one projEquiv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed spEmbed_injective)

section Field

variable (K : Type) [Field K] [CharP K 2]

@[expose] def f2 : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

@[expose] noncomputable def spField : StatedSp 3 (ZMod 2) →* StatedSp 3 K :=
  ((Matrix.GeneralLinearGroup.map (f2 K)).comp (StatedSp 3 (ZMod 2)).subtype).codRestrict _
    fun g => CFSG.Open.StatedAPI.map_mem_statedSp (f2 K) g.2

variable {K}

theorem f2_injective : Function.Injective (f2 K) := (f2 K).injective

theorem spField_injective : Function.Injective (spField K) := by
  intro g g' h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrArg (fun x : StatedSp 3 K =>
    ((x : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) i j) h
  exact f2_injective this

theorem f2_eq_zero_or_one (x : ZMod 2) : f2 K x = 0 ∨ f2 K x = 1 := by
  fin_cases x
  · left
    exact map_zero _
  · right
    exact map_one _

theorem det_eq_one_zmod_two {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι (ZMod 2)) :
    (g : Matrix ι ι (ZMod 2)).det = 1 := by
  have h : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
  have := congrArg Units.val (h (Matrix.GeneralLinearGroup.det g))
  simpa using this

end Field

theorem witness_projSp {K : Type} [Field K] [CharP K 2] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    Witness (StatedProj (StatedSp n K)) := by
  have hφ : Function.Injective ((projEquiv (K := K) (n := n) (by omega)).symm.toMonoidHom.comp
      ((spEmbed (Fin.castLE hn) (Fin.castLE_injective hn)).comp (spField K))) :=
    (projEquiv (by omega)).symm.injective.comp
      ((spEmbed_injective (Fin.castLE_injective hn)).comp spField_injective)
  exact witness_sp6two.map hφ

section Ext

variable {K : Type} [Field K]

@[expose] def extEquiv (m : ℕ) : (Fin 3 ⊕ Fin 3) ⊕ Fin m ≃ Fin (6 + m) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

@[expose] def extMat (m : ℕ) (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin (6 + m)) (Fin (6 + m)) K :=
  reindex (extEquiv m) (extEquiv m) (fromBlocks A 0 0 1)

theorem extMat_mul (m : ℕ) (A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    extMat m (A * B) = extMat m A * extMat m B := by
  rw [extMat, extMat, extMat, ← reindexAlgEquiv_apply K K, ← reindexAlgEquiv_apply K K,
    ← reindexAlgEquiv_apply K K, ← map_mul, fromBlocks_multiply]
  simp

theorem extMat_one (m : ℕ) : extMat (K := K) m 1 = 1 := by
  rw [extMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

theorem det_extMat (m : ℕ) (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    (extMat m A).det = A.det := by
  rw [extMat, det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem extMat_map (m : ℕ) (φ : K →+* K) (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    (extMat m A).map φ = extMat m (A.map φ) := by
  rw [extMat, extMat, reindex_apply, reindex_apply, ← submatrix_map, fromBlocks_map]
  simp

theorem extMat_transpose (m : ℕ) (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    (extMat m A)ᵀ = extMat m Aᵀ := by
  rw [extMat, extMat, transpose_reindex, fromBlocks_transpose]
  simp

theorem extMat_apply_inl (m : ℕ) (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (x y : Fin 3 ⊕ Fin 3) :
    extMat m A (extEquiv m (.inl x)) (extEquiv m (.inl y)) = A x y := by
  simp [extMat, reindex_apply]

@[expose] def extMatHom (m : ℕ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K →* Matrix (Fin (6 + m)) (Fin (6 + m)) K where
  toFun := extMat m
  map_one' := extMat_one m
  map_mul' := extMat_mul m

@[expose] def extGL (m : ℕ) : GL (Fin 3 ⊕ Fin 3) K →* GL (Fin (6 + m)) K :=
  Units.map (extMatHom m)

theorem coe_extGL (m : ℕ) (A : GL (Fin 3 ⊕ Fin 3) K) :
    ((extGL m A : GL (Fin (6 + m)) K) : Matrix (Fin (6 + m)) (Fin (6 + m)) K) =
      extMat m (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := rfl

theorem extGL_injective (m : ℕ) : Function.Injective (extGL (K := K) m) := by
  intro A B h
  apply Units.ext
  ext x y
  have := congrArg (fun g : GL (Fin (6 + m)) K =>
    (g : Matrix (Fin (6 + m)) (Fin (6 + m)) K) (extEquiv m (.inl x)) (extEquiv m (.inl y))) h
  simpa only [coe_extGL, extMat_apply_inl] using this

theorem eq_scalar_of_extGL {m : ℕ} {A : GL (Fin 3 ⊕ Fin 3) K} {c : Kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin (6 + m)) c = extGL m A) (x : Fin 3 ⊕ Fin 3) :
    ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) x x) = c := by
  have := congrArg (fun g : GL (Fin (6 + m)) K =>
    (g : Matrix (Fin (6 + m)) (Fin (6 + m)) K) (extEquiv m (.inl x)) (extEquiv m (.inl x))) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq,
    coe_extGL, extMat_apply_inl] at this
  exact this.symm

theorem eq_zero_of_extGL {m : ℕ} {A : GL (Fin 3 ⊕ Fin 3) K} {c : Kˣ}
    (h : Matrix.GeneralLinearGroup.scalar (Fin (6 + m)) c = extGL m A) {x y : Fin 3 ⊕ Fin 3}
    (hxy : x ≠ y) : ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) x y) = 0 := by
  have := congrArg (fun g : GL (Fin (6 + m)) K =>
    (g : Matrix (Fin (6 + m)) (Fin (6 + m)) K) (extEquiv m (.inl x)) (extEquiv m (.inl y))) h
  have hne : extEquiv m (.inl x) ≠ extEquiv m (.inl y) := fun h' =>
    hxy (Sum.inl_injective ((extEquiv m).injective h'))
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_ne _ hne,
    coe_extGL, extMat_apply_inl] at this
  exact this.symm

end Ext

section Linear

variable {F : Type} [Field F] [CharP F 2] [Finite F]

@[expose] noncomputable def spSL (m : ℕ) : StatedSp 3 (ZMod 2) →* StatedSL (6 + m) F :=
  ((extGL m).comp ((StatedSp 3 F).subtype.comp (spField F))).codRestrict _ fun g => by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, MonoidHom.comp_apply, MonoidHom.comp_apply,
      coe_extGL, det_extMat]
    show (RingHom.mapMatrix (f2 F) ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))).det = 1
    rw [← RingHom.map_det, det_eq_one_zmod_two, map_one]

theorem spSL_injective (m : ℕ) : Function.Injective (spSL (F := F) m) := by
  intro g g' h
  apply spField_injective (K := F)
  apply Subtype.ext
  have h1 : extGL m ((spField F g : StatedSp 3 F) : GL (Fin 3 ⊕ Fin 3) F) =
      extGL m ((spField F g' : StatedSp 3 F) : GL (Fin 3 ⊕ Fin 3) F) := congrArg Subtype.val h
  exact extGL_injective m h1

theorem witness_projSL (m : ℕ) : Witness (StatedProj (StatedSL (6 + m) F)) := by
  refine witness_sp6two.map (φ := (QuotientGroup.mk' _).comp (spSL m)) ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hg)
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin (6 + m)) c =
      extGL m ((spField F g : StatedSp 3 F) : GL (Fin 3 ⊕ Fin 3) F) := hc
  have hd := eq_scalar_of_extGL hc' (Sum.inl 0)
  have hc1 : (c : F) = 1 := by
    rcases f2_eq_zero_or_one (K := F) (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) (Sum.inl 0) (Sum.inl 0)) with h | h
    · exfalso
      apply c.ne_zero
      rw [← hd]
      exact h
    · rw [← hd]
      exact h
  apply spSL_injective (F := F) m
  rw [map_one]
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hc, show c = 1 from Units.ext hc1, map_one]

end Linear

section Unitary

variable {L : Type} [Field L] [CharP L 2]

@[expose] def q0 (b ν : L) : Matrix (Fin 2) (Fin 2) L := !![1, b; 1, b * ν]

theorem det_q0 (b ν : L) : (q0 b ν).det = b * (ν - 1) := by
  rw [q0, det_fin_two_of]
  ring

theorem q0_gram (φ : L →+* L) {q : ℕ} (hφ : ∀ x, φ x = x ^ q) {b ν : L} (hb : b * (1 + ν) = 1)
    (hν : ν ^ q * ν = 1) : ((q0 b ν).map φ)ᵀ * q0 b ν = !![0, 1; -1, 0] := by
  have hbν : φ b + φ (b * ν) = 1 := by
    rw [← map_add, show b + b * ν = b * (1 + ν) by ring, hb, map_one]
  have hbb : φ b * b + φ (b * ν) * (b * ν) = 0 := by
    rw [hφ, hφ, mul_pow]
    calc b ^ q * b + b ^ q * ν ^ q * (b * ν) = b ^ q * b * (1 + ν ^ q * ν) := by ring
      _ = 0 := by rw [hν, CharTwo.add_self_eq_zero, mul_zero]
  have hb' : b + b * ν = 1 := by rw [← hb]; ring
  have hbν' : φ b + φ b * φ ν = 1 := by rw [← map_mul]; exact hbν
  have hbb' : φ b * b + φ b * φ ν * (b * ν) = 0 := by rw [← map_mul]; exact hbb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q0, Matrix.mul_apply, Fin.sum_univ_two, map_one, CharTwo.add_self_eq_zero]
  · exact hb'
  · rw [CharTwo.neg_eq]
    exact hbν'
  · exact hbb'

theorem planeMat_map (φ : L →+* L) (h : Fin 3 → Matrix (Fin 2) (Fin 2) L) :
    (planeMat h).map φ = planeMat fun j => (h j).map φ := by
  simp only [planeMat, fromBlocks_map, diagonal_map (map_zero φ), Matrix.map_apply]

@[expose] noncomputable def qGL (b ν : L) (hb : b ≠ 0) (hν : ν ≠ 1) : GL (Fin 3 ⊕ Fin 3) L :=
  planeHom fun _ => Matrix.GeneralLinearGroup.mkOfDetNeZero (q0 b ν) (by
    rw [det_q0]
    exact mul_ne_zero hb (sub_ne_zero.2 hν))

theorem coe_qGL (b ν : L) (hb : b ≠ 0) (hν : ν ≠ 1) :
    ((qGL b ν hb hν : GL (Fin 3 ⊕ Fin 3) L) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L) =
      planeMat fun _ => q0 b ν := rfl

theorem qGL_gram (φ : L →+* L) {q : ℕ} (hφ : ∀ x, φ x = x ^ q) {b ν : L} (hb0 : b ≠ 0)
    (hν1 : ν ≠ 1) (hb : b * (1 + ν) = 1) (hν : ν ^ q * ν = 1) :
    (((qGL b ν hb0 hν1 : GL (Fin 3 ⊕ Fin 3) L) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L).map
      φ)ᵀ * ((qGL b ν hb0 hν1 : GL (Fin 3 ⊕ Fin 3) L) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L) =
      fromBlocks 0 1 (-1) 0 := by
  rw [coe_qGL, planeMat_map, planeMat_transpose, planeMat_mul, ← planeMat_gram]
  congr 1
  funext j
  exact q0_gram φ hφ hb hν

theorem spField_map (φ : L →+* L) (g : StatedSp 3 (ZMod 2)) :
    (((spField L g : StatedSp 3 L) : GL (Fin 3 ⊕ Fin 3) L) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L).map φ =
      (((spField L g : StatedSp 3 L) : GL (Fin 3 ⊕ Fin 3) L) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L) := by
  ext x y
  show φ (f2 L (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) x y)) =
      f2 L (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) x y)
  rcases f2_eq_zero_or_one (K := L) (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) x y) with h | h <;>
    rw [h]
  · exact map_zero φ
  · exact map_one φ

@[expose] noncomputable def rhoGL (b ν : L) (hb0 : b ≠ 0) (hν1 : ν ≠ 1)
    (g : StatedSp 3 (ZMod 2)) : GL (Fin 3 ⊕ Fin 3) L :=
  qGL b ν hb0 hν1 * ((spField L g : StatedSp 3 L) : GL (Fin 3 ⊕ Fin 3) L) * (qGL b ν hb0 hν1)⁻¹

theorem unitary_conj (φ : L →+* L) {q : ℕ} (hφ : ∀ x, φ x = x ^ q) {b ν : L} (hb0 : b ≠ 0)
    (hν1 : ν ≠ 1) (hb : b * (1 + ν) = 1) (hν : ν ^ q * ν = 1) (g : StatedSp 3 (ZMod 2)) :
    (((rhoGL b ν hb0 hν1 g : GL (Fin 3 ⊕ Fin 3) L) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L).map φ)ᵀ *
      ((rhoGL b ν hb0 hν1 g : GL (Fin 3 ⊕ Fin 3) L) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L) =
      1 := by
  set M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L :=
    ((qGL b ν hb0 hν1 : GL (Fin 3 ⊕ Fin 3) L) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L)
  set M' : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L :=
    (((qGL b ν hb0 hν1)⁻¹ : GL (Fin 3 ⊕ Fin 3) L) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L)
  set A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L :=
    (((spField L g : StatedSp 3 L) : GL (Fin 3 ⊕ Fin 3) L) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L)
  set J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L := fromBlocks 0 1 (-1) 0
  have hMM' : M * M' = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMM'φ : M.map φ * M'.map φ = 1 := by
    rw [← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hJ : (M.map φ)ᵀ * M = J := qGL_gram φ hφ hb0 hν1 hb hν
  have hA : Aᵀ * J * A = J :=
    CFSG.Open.StatedAPI.mem_statedSp_iff.1 (spField L g).2
  have hAφ : A.map φ = A := spField_map φ g
  show ((M * A * M').map φ)ᵀ * (M * A * M') = 1

  calc ((M * A * M').map φ)ᵀ * (M * A * M') =
      (M'.map φ)ᵀ * Aᵀ * ((M.map φ)ᵀ * M) * A * M' := by
        rw [Matrix.map_mul, Matrix.map_mul, hAφ]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (M'.map φ)ᵀ * (Aᵀ * J * A) * M' := by
        rw [hJ]
        simp only [Matrix.mul_assoc]
    _ = (M'.map φ)ᵀ * ((M.map φ)ᵀ * M) * M' := by rw [hA, hJ]
    _ = (M.map φ * M'.map φ)ᵀ * (M * M') := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hMM'φ, hMM', Matrix.transpose_one, Matrix.one_mul]

variable [Finite L]

theorem witness_projSU {f : ℕ} (hf : 1 ≤ f) (hL : Nat.card L = (2 ^ f) ^ 2) (m : ℕ) :
    Witness (StatedProj (StatedSU (6 + m) (2 ^ f) L)) := by
  have hq2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  obtain ⟨ν', hν'⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.exists_orderOf_eq_of_dvd_card_sub_one
      (F := L) (d := 2 ^ f + 1) (by
        rw [hL, show (2 ^ f) ^ 2 - 1 = (2 ^ f) ^ 2 - 1 ^ 2 by norm_num, Nat.pow_two_sub_pow_two]
        exact dvd_mul_right _ _)
  set ν : L := (ν' : L)
  have hν : ν ^ (2 ^ f) * ν = 1 := by
    rw [← pow_succ]
    have := pow_orderOf_eq_one ν'
    rw [hν'] at this
    exact congrArg Units.val this
  have hν1 : ν ≠ 1 := by
    intro h
    have h1 : ν' = 1 := Units.ext h
    rw [h1, orderOf_one] at hν'
    omega
  have hν0 : (1 : L) + ν ≠ 0 := by
    intro h
    apply hν1
    have : ν = -1 := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
    rw [this, CharTwo.neg_eq]
  set b : L := (1 + ν)⁻¹
  have hb : b * (1 + ν) = 1 := inv_mul_cancel₀ hν0
  have hb0 : b ≠ 0 := inv_ne_zero hν0
  let φ : L →+* L := iterateFrobenius L 2 f
  have hφ : ∀ x, φ x = x ^ 2 ^ f := fun x => iterateFrobenius_def 2 f x
  set Q := qGL b ν hb0 hν1
  let ρ : StatedSp 3 (ZMod 2) →* GL (Fin (6 + m)) L :=
    (extGL m).comp ((MulAut.conj Q).toMonoidHom.comp ((StatedSp 3 L).subtype.comp (spField L)))
  have hρ : ∀ g, ρ g ∈ StatedSU (6 + m) (2 ^ f) L := by
    intro g
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree.PSUThree.mem_statedSU_iff
      Nat.prime_two hL (by omega)]
    have hcoe : ((ρ g : GL (Fin (6 + m)) L) : Matrix (Fin (6 + m)) (Fin (6 + m)) L) =
        extMat m ((rhoGL b ν hb0 hν1 g : GL (Fin 3 ⊕ Fin 3) L) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L) := rfl
    refine ⟨?_, ?_⟩
    · rw [hcoe, det_extMat, rhoGL, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
        mul_right_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.det_one, one_mul]
      show (RingHom.mapMatrix (f2 L) ((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))).det = 1
      rw [← RingHom.map_det, det_eq_one_zmod_two, map_one]
    · have hmap : ∀ M : Matrix (Fin (6 + m)) (Fin (6 + m)) L, M.map (· ^ 2 ^ f) = M.map φ :=
        fun M => by ext; simp [hφ]
      rw [hmap, hcoe, extMat_map, extMat_transpose, ← extMat_mul,
        unitary_conj φ hφ hb0 hν1 hb hν g, extMat_one]
  let ψ : StatedSp 3 (ZMod 2) →* StatedSU (6 + m) (2 ^ f) L := ρ.codRestrict _ hρ
  have hψ : Function.Injective ψ := by
    intro g g' h
    have h1 : ρ g = ρ g' := congrArg Subtype.val h
    have h2 := extGL_injective m h1
    have h3 := (MulAut.conj Q).injective h2
    exact spField_injective (Subtype.ext h3)
  refine witness_sp6two.map (φ := (QuotientGroup.mk' _).comp ψ) ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hg)
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin (6 + m)) c = extGL m (rhoGL b ν hb0 hν1 g) :=
    hc
  have hconj : rhoGL b ν hb0 hν1 g = Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c := by
    apply Units.ext
    ext x y
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
      exact eq_scalar_of_extGL hc' x
    · rw [diagonal_apply_ne _ hxy]
      exact eq_zero_of_extGL hc' hxy
  have hA : ((spField L g : StatedSp 3 L) : GL (Fin 3 ⊕ Fin 3) L) =
      Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c := by
    have h1 : ((spField L g : StatedSp 3 L) : GL (Fin 3 ⊕ Fin 3) L) =
        Q⁻¹ * rhoGL b ν hb0 hν1 g * Q := by
      show _ = Q⁻¹ * (Q * ((spField L g : StatedSp 3 L) : GL (Fin 3 ⊕ Fin 3) L) * Q⁻¹) * Q
      group
    have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c * Q =
        Q * Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq
    rw [h1, hconj, mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hd : f2 L (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) (Sum.inl 0) (Sum.inl 0)) = c := by
    have := congrArg (fun x : GL (Fin 3 ⊕ Fin 3) L =>
      (x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L) (Sum.inl 0) (Sum.inl 0)) hA
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      diagonal_apply_eq] at this
    exact this
  have hc1 : (c : L) = 1 := by
    rcases f2_eq_zero_or_one (K := L) (((g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) (Sum.inl 0) (Sum.inl 0)) with h | h
    · exfalso
      apply c.ne_zero
      rw [← hd]
      exact h
    · rw [← hd]
      exact h
  apply spField_injective (K := L)
  rw [map_one]
  apply Subtype.ext
  rw [hA, show c = 1 from Units.ext hc1, map_one]
  rfl

end Unitary

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev.Sp62
