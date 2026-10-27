module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5Block

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

theorem exists_fixed_sl3_block_of_sq_gen {m : ℕ} (hm : 1 ≤ m) (hK : ringChar K ≠ 2) (B : GL (Fin (3 + m)) K) (hB : B * B = 1)
    (h3 : 3 ≤ finrank K (LinearMap.ker (toLin' B.val - 1))) :
    ∃ ρ : SpecialLinearGroup (Fin 3) K →* projectiveSL (3 + m) K, Function.Injective ρ ∧
      ∀ g, conjAut (3 + m) K B (ρ g) = ρ g := by
  have hBm : (B : Matrix (Fin (3 + m)) (Fin (3 + m)) K) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  set k := finrank K (LinearMap.ker (toLin' B.val - 1)) with hk
  set d : Fin (3 + m) → K := fun i => if (i : ℕ) < k then 1 else -1 with hd
  have hDd : (D : Matrix (Fin (3 + m)) (Fin (3 + m)) K) = diagonal d := by
    rw [hD]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp [hd]
    · simp [hac, Ne.symm hac]
  have hconj : conjAut (3 + m) K B =
      conjAut (3 + m) K P * conjAut (3 + m) K D * (conjAut (3 + m) K P)⁻¹ := by
    rw [← hPD, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  set θ : SpecialLinearGroup (Fin 3) K →* projectiveSL (3 + m) K :=
    (proj (3 + m) K).comp (slBlock K 3 m) with hθ
  have hfixD : ∀ g, conjAut (3 + m) K D (θ g) = θ g := by
    intro g
    refine (conjAut_proj D _).trans ?_
    show proj (3 + m) K _ = proj (3 + m) K _
    congr 1
    apply Subtype.ext
    refine (coe_slConjugation D _).trans ?_
    change (D : Matrix (Fin (3 + m)) (Fin (3 + m)) K) *
        (blockGL K 3 m (SpecialLinearGroup.toGL g) : Matrix (Fin (3 + m)) (Fin (3 + m)) K) *
        ((D⁻¹ : GL (Fin (3 + m)) K) : Matrix (Fin (3 + m)) (Fin (3 + m)) K) = _
    rw [hDd, ← blockGL_mul_diagonal_comm, Matrix.mul_assoc, ← hDd, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.mul_one]
    · rfl
    · intro i j
      have hi : ((finSumFinEquiv (Sum.inl i : Fin 3 ⊕ Fin m) : Fin (3 + m)) : ℕ) < k := by
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
        omega
      have hj : ((finSumFinEquiv (Sum.inl j : Fin 3 ⊕ Fin m) : Fin (3 + m)) : ℕ) < k := by
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
        omega
      simp only [hd, hi, hj, ↓reduceIte]
  refine ⟨(conjAut (3 + m) K P : MulAut (projectiveSL (3 + m) K)).toMonoidHom.comp θ, ?_, ?_⟩
  · exact (conjAut (3 + m) K P).injective.comp (injective_proj_slBlock hm)
  · intro g
    rw [hconj]
    change conjAut (3 + m) K P (conjAut (3 + m) K D ((conjAut (3 + m) K P)⁻¹
      (conjAut (3 + m) K P (θ g)))) = conjAut (3 + m) K P (θ g)
    rw [MulAut.inv_apply_self, hfixD]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
