module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG.LocalAnalysis.GLTheoremA.YS09Field CFSG.Assembly CFSG.Open
open scoped Matrix

section Sp

variable {K : Type} [Field K] [Finite K] {m : ℕ}

theorem mem_StatedSp_iff (A : GL (Fin m ⊕ Fin m) K) :
    A ∈ StatedSp m K ↔
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.fromBlocks 0 1 (-1) 0 := by
  have h : StatedSp m K = Subgroup.closure {A : GL (Fin m ⊕ Fin m) K |
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
        (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.fromBlocks 0 1 (-1) 0} := rfl
  rw [h, mem_closure_iff_of_mul_closed]
  · rfl
  · simp
  · intro a ha b hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul] at ha hb ⊢
    calc _ = (b : Matrix _ _ K)ᵀ * ((a : Matrix _ _ K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
          (a : Matrix _ _ K)) * (b : Matrix _ _ K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]

theorem sp_map_subtype_iff (σ : K ≃+* K) (A : GL (Fin m ⊕ Fin m) (fixF σ)) :
    Matrix.GeneralLinearGroup.map (fixF σ).subtype A ∈ StatedSp m K ↔ A ∈ StatedSp m (fixF σ) := by
  rw [mem_StatedSp_iff, mem_StatedSp_iff]
  set f : fixF σ →+* K := (fixF σ).subtype with hf
  have hJ : (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (fixF σ)).map f := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  have hA : ((Matrix.GeneralLinearGroup.map f A : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (fixF σ)).map f := rfl
  rw [hA, hJ, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective f.injective).eq_iff

theorem twoPart_card_Sp {e : ℕ} (he : 1 ≤ e) {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = 2 ^ e) :
    twoPart (Nat.card (LargeEvenSpGroup L m)) = 2 ^ (e * (m * m)) := by
  rw [twoPart_card_matrix_group he hL, twoPart_card_statedProj_statedSp he hL]

theorem stOrderBody_symplectic (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ}
    (hp : p.Prime) (I : Set (MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) :
    StOrderBody p (LargeEvenProj (LargeEvenSpGroup K m)) I
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) := by
  refine stOrderBody_of_matrix hn hK (LargeEvenSpGroup K m)
    (fun σ h hh => sp_map_mem σ h hh) (fun _ => True) (fun _ _ _ => trivial)
    (u := m * m) (v := 1) (Nat.mul_pos hm hm) one_pos ?_ ?_ hp
    (fun σ => ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.1 h), trivial⟩) I
  · rw [pow_one]
    exact twoPart_card_Sp hn hK
  · intro σ _ e he
    have hk : Nat.card (fixF σ) = 2 ^ e := card_fixF.trans he
    rw [pow_one, card_fixed_eq_of_iff σ _ (LargeEvenSpGroup (fixF σ) m) (sp_map_subtype_iff σ)]
    exact twoPart_card_Sp (one_le_of_card_fixed he) hk

end Sp

end FQ

end CFSG.LocalAnalysis.GLTheoremA
