module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.StandardType.Line63.H5 CFSG.SectionRank.OddCover

variable {K : Type} [Field K] {n d : ℕ}

theorem blockRes_smul_one {S : Finset (Fin d)} (c : K) :
    blockRes S (c • (1 : Matrix (Fin d) (Fin d) K)) = c • (1 : Matrix (Fin S.card) (Fin S.card) K) := by
  ext a b
  simp only [blockRes, Matrix.smul_apply, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · have hne : (S.equivFin.symm a : Fin d) ≠ S.equivFin.symm b := fun h =>
      hab (S.equivFin.symm.injective (Subtype.ext h))
    simp [hne, hab]

theorem blockRes_transpose_mul {S : Finset (Fin d)} {A B : Matrix (Fin d) (Fin d) K}
    (hA : IsBlockDiag S A) :
    blockRes S (Aᵀ * B) = (blockRes S A)ᵀ * blockRes S B := by
  ext a b
  simp only [blockRes, Matrix.mul_apply, Matrix.transpose_apply]
  set e := S.equivFin.symm with he
  have hz : ∀ k ∉ S, A k (e a) * B k (e b) = 0 := by
    intro k hk
    rw [hA k (e a) (Or.inr ⟨hk, (e a).2⟩), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) fun k _ hk => hz k hk,
    ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e fun k : ↥S => A k (e a) * B k (e b)).symm

theorem blockRes_similitude {S : Finset (Fin d)} (h : UnitaryFieldData 2 n K)
    {M : GL (Fin d) K} {ν : K}
    (hM : IsBlockDiag S (M : Matrix (Fin d) (Fin d) K))
    (hgu : ((M : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (M : Matrix (Fin d) (Fin d) K) =
      ν • (1 : Matrix (Fin d) (Fin d) K)) :
    ((blockRes S (M : Matrix (Fin d) (Fin d) K)).map h.bar)ᵀ *
        blockRes S (M : Matrix (Fin d) (Fin d) K) =
      ν • (1 : Matrix (Fin S.card) (Fin S.card) K) := by
  have hdiag : IsBlockDiag S ((M : Matrix (Fin d) (Fin d) K).map h.bar) := by
    intro i j hij
    rw [Matrix.map_apply, hM i j hij, map_zero]
  have h1 : blockRes S (((M : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (M : Matrix (Fin d) (Fin d) K)) = ν • (1 : Matrix (Fin S.card) (Fin S.card) K) := by
    rw [hgu, blockRes_smul_one]
  rw [← h1, blockRes_transpose_mul hdiag]
  rfl

@[expose] noncomputable def blockResGL {S : Finset (Fin d)} {M : GL (Fin d) K}
    (hM : IsBlockDiag S (M : Matrix (Fin d) (Fin d) K)) : GL (Fin S.card) K where
  val := blockRes S (M : Matrix (Fin d) (Fin d) K)
  inv := blockRes S ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  val_inv := by
    rw [← blockRes_mul_of_left hM, ← Units.val_mul, mul_inv_cancel, Units.val_one, blockRes_one]
  inv_val := by
    rw [← blockRes_mul_of_right hM, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      blockRes_one]

theorem coe_blockResGL {S : Finset (Fin d)} {M : GL (Fin d) K}
    (hM : IsBlockDiag S (M : Matrix (Fin d) (Fin d) K)) :
    ((blockResGL hM : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
      blockRes S (M : Matrix (Fin d) (Fin d) K) :=
  rfl

theorem inv_coe_blockResGL {S : Finset (Fin d)} {M : GL (Fin d) K}
    (hM : IsBlockDiag S (M : Matrix (Fin d) (Fin d) K)) :
    (((blockResGL hM)⁻¹ : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) =
      blockRes S ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  rfl

theorem blockRes_conj_eq {S : Finset (Fin d)} {M : GL (Fin d) K}
    (hM : IsBlockDiag S (M : Matrix (Fin d) (Fin d) K)) {u : Matrix (Fin d) (Fin d) K}
    (hu : IsBlockOn S u) :
    blockRes S ((M : Matrix (Fin d) (Fin d) K) * u *
        ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
      ((blockResGL hM : GL (Fin S.card) K) : Matrix (Fin S.card) (Fin S.card) K) *
        blockRes S u * (((blockResGL hM)⁻¹ : GL (Fin S.card) K) :
          Matrix (Fin S.card) (Fin S.card) K) := by
  rw [mul_assoc, blockRes_mul_of_left hM, blockRes_mul_of_right (isBlockDiag_inv hM),
    ← mul_assoc, coe_blockResGL, inv_coe_blockResGL]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
