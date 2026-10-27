module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9SL
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TNine

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.SectionRank.OddCover Matrix

theorem det_eq_one_of_mem_statedSL {F : Type} [Field F] {x : GL (Fin 3) F}
    (hx : x ∈ StatedSL 3 F) : (x : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hx

theorem mem_statedSL_of_det {F : Type} [Field F] {x : GL (Fin 3) F}
    (hx : (x : Matrix (Fin 3) (Fin 3) F).det = 1) : x ∈ StatedSL 3 F :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det hx

theorem fieldNine_SL {F : Type} [Field F] [Finite F] (hF : Nat.card F % 9 = 1)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (e : K ≃* ↥(StatedSL 3 F))
    (H : Subgroup (MulAut K)) (hH : IsElemAbelian 3 H) (h27 : Nat.card H = 27) :
    ∃ ψ ∈ H, ¬ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsInnerAut ψ ∧
      ∃ T P Q : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ P ≤ Subgroup.normalizer (T : Set K) ∧
        Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
        Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) ∧ P ≤ Q ∧
        T.map ψ.toMonoidHom = T ∧ ∃ k : ℕ, ∀ x ∈ Q, ψ x = x ^ k := by
  obtain ⟨ψ, hψH, hni, M, σ, hM⟩ := exists_fieldType_SL hF hq e H hH h27
  refine ⟨ψ, hψH, hni, ?_⟩
  obtain ⟨ω, hω⟩ := exists_orderOf_nine (K := F) (by omega)
  have hstd : NineFix (StatedSL 3 F) (GeneralLinearGroup.map (σ : F →+* F)) := by
    refine nineFix_of_mem hω ?_ ?_ σ
    · intro a b _ _
      refine mem_statedSL_of_det ?_
      have ha := a.ne_zero
      have hb := b.ne_zero
      simp [coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_three]
      field_simp
    · exact mem_statedSL_of_det (by simp [coe_tMat, Matrix.det_fin_three])
  have hconj := nineFix_conj hstd M (fun x hx => by
    refine mem_statedSL_of_det ?_
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_eq_one_of_mem_statedSL hx]
    have : (M : Matrix (Fin 3) (Fin 3) F).det * ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [mul_one, this])
  exact nine_of_nineFix e ψ hM hconj

end CFSG.HardMathSupport.Solomon.Coordinator
