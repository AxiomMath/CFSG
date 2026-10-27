module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.GH74.Uniqueness.SU.SU5F4

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.LieType.Universal.Unitary
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

@[expose] def f4Frob : F4c ≃+* F4c where
  toFun := F4c.sg
  invFun := F4c.sg
  left_inv := F4c.sg_sg
  right_inv := F4c.sg_sg
  map_mul' := F4c.sg_mul
  map_add' := F4c.sg_add

theorem f4Frob_apply (x : F4c) : f4Frob x = x * x := rfl

theorem charP_f4c : CharP F4c 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero (by decide) (by decide)

theorem f4c_eq_one_of_mul_self : ∀ x : F4c, x * x = 1 → x = 1 := by decide

theorem f4c_eq_of_add_eq_zero : ∀ x y : F4c, x + y = 0 → x = y := by decide

section Form

variable {F : Type*} [Field F]

theorem conjTr_mul_antidiag_mul_apply (σ : F ≃+* F) {n : ℕ} (g : Matrix (Fin n) (Fin n) F)
    (i j : Fin n) :
    (conjTr σ g * (antidiag n : Matrix (Fin n) (Fin n) F) * g) i j =
      ∑ k, σ (g k i) * g (Fin.rev k) j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [conjTr, antidiag, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, ite_mul]

@[expose] noncomputable def suMk (σ : F ≃+* F) {n : ℕ} (g : Matrix (Fin n) (Fin n) F)
    (hd : g.det = 1) (hu : conjTr σ g * antidiag n * g = antidiag n) : SU σ n :=
  ⟨⟨g, g⁻¹, Matrix.mul_nonsing_inv g (by rw [hd]; exact isUnit_one),
    Matrix.nonsing_inv_mul g (by rw [hd]; exact isUnit_one)⟩, hd, hu⟩

@[simp] theorem coe_suMk (σ : F ≃+* F) {n : ℕ} (g : Matrix (Fin n) (Fin n) F) (hd : g.det = 1)
    (hu : conjTr σ g * antidiag n * g = antidiag n) :
    (((suMk σ g hd hu : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = g := rfl

end Form

section Det

variable {R : Type*} [CommRing R]

theorem det_of_corners {m : ℕ} (g : Matrix (Fin (m + 2)) (Fin (m + 2)) R)
    (h0 : ∀ i : Fin (m + 1), g i.succ 0 = 0)
    (hl : ∀ j : Fin (m + 1), g (Fin.last (m + 1)) j.castSucc = 0) :
    g.det = g 0 0 * g (Fin.last (m + 1)) (Fin.last (m + 1)) *
      (Matrix.of fun a b : Fin m => g a.castSucc.succ b.castSucc.succ).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  rw [det_succ_row _ (Fin.last m), Fin.sum_univ_castSucc]
  have hz : ∀ j : Fin m, (g.submatrix Fin.succ Fin.succ) (Fin.last m) j.castSucc = 0 := by
    intro j
    simp only [submatrix_apply, Fin.succ_last]
    rw [← Fin.castSucc_succ]
    exact hl j.succ
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last]
  have hpow : ((-1 : R) ^ ((Fin.last m : ℕ) + (Fin.last m : ℕ))) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  rw [hpow, one_mul, mul_assoc]
  congr 2

theorem det_of_blockTri {a b : ℕ} (g : Matrix (Fin (a + b)) (Fin (a + b)) R)
    (h : ∀ i j, g (Fin.natAdd a i) (Fin.castAdd b j) = 0) :
    g.det = (g.submatrix (Fin.castAdd b) (Fin.castAdd b)).det *
      (g.submatrix (Fin.natAdd a) (Fin.natAdd a)).det := by
  rw [← det_submatrix_equiv_self finSumFinEquiv g]
  have e : g.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (g.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (g.submatrix (Fin.castAdd b) (Fin.natAdd a)) 0
        (g.submatrix (Fin.natAdd a) (Fin.natAdd a)) := by
    ext (i | i) (j | j) <;> simp [h]
  rw [e, det_fromBlocks_zero₂₁]

end Det

section Transfer

variable {F F' : Type*} [Field F] [Field F'] {σ : F ≃+* F} {σ' : F' ≃+* F'}

theorem conjTr_mapMatrix (φ : F ≃+* F') (hφ : ∀ c, φ (σ c) = σ' (φ c)) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    conjTr σ' (φ.mapMatrix A) = φ.mapMatrix (conjTr σ A) := by
  ext i j
  simp [conjTr, hφ]

theorem mapMatrix_antidiag (φ : F ≃+* F') {n : ℕ} :
    φ.mapMatrix (antidiag n : Matrix (Fin n) (Fin n) F) = antidiag n := by
  ext i j
  simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply, antidiag, Matrix.of_apply]
  split_ifs <;> simp

theorem mapMatrix_mem_SU (φ : F ≃+* F') (hφ : ∀ c, φ (σ c) = σ' (φ c)) {n : ℕ}
    (A : SU σ n) :
    (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ).det = 1 ∧
      conjTr σ' (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ) * antidiag n *
        (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ) = antidiag n := by
  obtain ⟨hd, hu⟩ := A.2
  refine ⟨?_, ?_⟩
  · have := RingEquiv.map_det φ ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    rw [hd, map_one] at this
    exact this.symm
  · have e := congrArg φ.mapMatrix hu
    rw [map_mul, map_mul, ← conjTr_mapMatrix φ hφ, mapMatrix_antidiag] at e
    exact e

@[expose] noncomputable def suCongr (φ : F ≃+* F') (hφ : ∀ c, φ (σ c) = σ' (φ c)) (n : ℕ) :
    SU σ n ≃* SU σ' n where
  toFun A := ⟨⟨((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ,
      (((A⁻¹ : SU σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ, by
        change φ.mapMatrix _ * φ.mapMatrix _ = 1
        rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one, map_one], by
        change φ.mapMatrix _ * φ.mapMatrix _ = 1
        rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one, map_one]⟩, mapMatrix_mem_SU φ hφ A⟩
  invFun B := ⟨⟨((B : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map φ.symm,
      (((B⁻¹ : SU σ' n) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map φ.symm, by
        change φ.symm.mapMatrix _ * φ.symm.mapMatrix _ = 1
        rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one, map_one], by
        change φ.symm.mapMatrix _ * φ.symm.mapMatrix _ = 1
        rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one, map_one]⟩,
    mapMatrix_mem_SU φ.symm (fun c => by
      apply φ.injective
      rw [RingEquiv.apply_symm_apply, hφ, RingEquiv.apply_symm_apply]) B⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp
  right_inv B := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp
  map_mul' A B := by
    apply Subtype.ext
    apply Units.ext
    change φ.mapMatrix (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = φ.mapMatrix _ * φ.mapMatrix _
    rw [map_mul]

theorem coe_suCongr (φ : F ≃+* F') (hφ : ∀ c, φ (σ c) = σ' (φ c)) {n : ℕ} (A : SU σ n) :
    (((suCongr φ hφ n A : SU σ' n) : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ := rfl

end Transfer

section Count

variable {G H : Type*} [Group G] [Group H]

theorem card_centralizer_mulEquiv (ψ : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({ψ x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have e : (Subgroup.centralizer ({x} : Set G)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ x} : Set H) := by
    ext y
    obtain ⟨y, rfl⟩ := ψ.surjective y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [← hyy']
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      change ψ y' * ψ x = ψ x * ψ y'
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hy']
    · intro hy
      refine ⟨y, Subgroup.mem_centralizer_singleton_iff.2 (ψ.injective ?_), rfl⟩
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hy
  rw [← e, Subgroup.card_map_of_injective ψ.injective]

theorem card_eq_card_ker_mul_card_range (ρ : G →* H) :
    Nat.card G = Nat.card ρ.ker * Nat.card ρ.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm]

theorem natCard_eq_of_bijective_finset {α P : Type*} [Fintype P] [DecidableEq P]
    (S : Finset P) (f : S → α) (hf : Function.Bijective f) : Nat.card α = S.card := by
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]

end Count

end CFSG.SeitzReduction.F4Pilot
