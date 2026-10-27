module

public import CFSG.Blueprint.Catalog

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Open CFSG.Blueprint Matrix

@[expose] def FGSpU : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  Matrix.fromBlocks !![1, 1; 0, 1] !![0, 1; 0, 1] 0 !![1, 0; -1, 1]

@[expose] def FGSpUInv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  Matrix.fromBlocks !![1, -1; 0, 1] !![0, 0; -1, -1] 0 !![1, 0; 1, 1]

theorem fg_spU_mul_inv : FGSpU * FGSpUInv = 1 := by decide +kernel

theorem fg_spU_inv_mul : FGSpUInv * FGSpU = 1 := by decide +kernel

theorem fg_spU_symp :
    FGSpUᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) *
        FGSpU = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem fg_spU_pow_nine : FGSpU ^ 9 = 1 := by decide +kernel

theorem fg_spU_pow_three_entry : (FGSpU ^ 3) (Sum.inl 0) (Sum.inr 0) ≠ 0 := by decide +kernel

@[expose] noncomputable def FGSpUnit (K : Type) [Field K] [CharP K 3] : GL (Fin 2 ⊕ Fin 2) K :=
  Matrix.GeneralLinearGroup.map (ZMod.castHom (dvd_refl 3) K)
    (⟨FGSpU, FGSpUInv, fg_spU_mul_inv, fg_spU_inv_mul⟩ : GL (Fin 2 ⊕ Fin 2) (ZMod 3))

section Transport

variable (K : Type) [Field K] [CharP K 3]

theorem fg_spUnit_coe :
    ((FGSpUnit K : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      FGSpU.map (ZMod.castHom (dvd_refl 3) K) := rfl

theorem fg_spUnit_pow_coe (n : ℕ) :
    ((FGSpUnit K ^ n : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (FGSpU ^ n).map (ZMod.castHom (dvd_refl 3) K) := by
  rw [Units.val_pow_eq_pow_val, fg_spUnit_coe]
  exact (map_pow (RingHom.mapMatrix (ZMod.castHom (dvd_refl 3) K)) FGSpU n).symm

theorem fg_spUnit_mem : FGSpUnit K ∈ StatedSp 2 K := by
  apply Subgroup.subset_closure
  show _ = _
  have h := congrArg (RingHom.mapMatrix (ZMod.castHom (dvd_refl 3) K)) fg_spU_symp
  simp only [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map] at h
  rw [fg_spUnit_coe]
  have hneg : ((-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)).map (ZMod.castHom (dvd_refl 3) K)) = -1 := by
    rw [Matrix.map_neg _ (map_neg (ZMod.castHom (dvd_refl 3) K)),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.fromBlocks_map] at h
  simpa [hneg] using h

theorem fg_spUnit_pow_nine : FGSpUnit K ^ 9 = 1 := by
  apply Units.ext
  rw [fg_spUnit_pow_coe, fg_spU_pow_nine, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem fg_spUnit_pow_three_not_scalar :
    FGSpUnit K ^ 3 ∉ StatedScalars (Fin 2 ⊕ Fin 2) K := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun A : GL (Fin 2 ⊕ Fin 2) K =>
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inr 0)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, fg_spUnit_pow_coe, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ (Sum.inl_ne_inr), Matrix.map_apply] at h
  apply fg_spU_pow_three_entry
  apply ZMod.castHom_injective K
  rw [map_zero]
  exact h.symm

theorem fg_exists_orderNine_statedProj :
    ∃ y : StatedProj (StatedSp 2 K), orderOf y = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let u : StatedSp 2 K := ⟨FGSpUnit K, fg_spUnit_mem K⟩
  refine ⟨(QuotientGroup.mk u : StatedProj (StatedSp 2 K)), ?_⟩
  have h : orderOf (QuotientGroup.mk u : StatedProj (StatedSp 2 K)) = 3 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 3) (n := 1) ?_ ?_
  · simpa using h
  · intro h1
    have h2 : (QuotientGroup.mk (u ^ 3) : StatedProj (StatedSp 2 K)) = 1 := by
      rw [QuotientGroup.mk_pow]
      simpa using h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact fg_spUnit_pow_three_not_scalar K h2
  · have h9 : u ^ 3 ^ (1 + 1) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact fg_spUnit_pow_nine K
    have h10 : (QuotientGroup.mk (u ^ 3 ^ (1 + 1)) : StatedProj (StatedSp 2 K)) = 1 := by
      rw [h9]
      exact QuotientGroup.mk_one _
    rw [QuotientGroup.mk_pow] at h10
    exact h10

end Transport

theorem fg_exists_orderNine_of_lieModel_psp {X : Type} [Group X] (h : LieModel X .PSp 2 3 1) :
    ∃ k : X, orderOf k = 9 := by
  obtain ⟨-, K, _, hfin, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 3 := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hK]; norm_num)
  obtain ⟨y, hy⟩ := fg_exists_orderNine_statedProj K
  exact ⟨e.symm y, by rw [MulEquiv.orderOf_eq]; exact hy⟩

end CFSG.OddStandard.SmallF3.Omega
