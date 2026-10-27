module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT119FSL
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9SU
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9UH

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.SectionRank.OddCover Matrix

theorem fieldNine_SU {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 9 = 8) {K : Type} [Group K] [Finite K] (hqs : CFSG.Open.IsQuasisimple K)
    (e : K ≃* ↥(StatedSU 3 q F)) (H : Subgroup (MulAut K)) (hH : IsElemAbelian 3 H)
    (h27 : Nat.card H = 27) :
    ∃ ψ ∈ H, ¬ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsInnerAut ψ ∧
      ∃ T P Q : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ P ≤ Subgroup.normalizer (T : Set K) ∧
        Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
        Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) ∧ P ≤ Q ∧
        T.map ψ.toMonoidHom = T ∧ ∃ k : ℕ, ∀ x ∈ Q, ψ x = x ^ k := by
  obtain ⟨ψ, hψH, hni, M, σ, hMS, hM⟩ :=
    exists_fieldType_SU hF hq (unitaryH90 F q) hqs e H hH h27
  refine ⟨ψ, hψH, hni, ?_⟩
  have hq0 : 0 < q := by omega
  have h9 : 9 ∣ Nat.card F - 1 := by
    have : q ^ 2 % 9 = 1 := by
      rw [pow_two, Nat.mul_mod, hq]
    have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq0
    rw [hF]; omega
  obtain ⟨ω, hω⟩ := exists_orderOf_nine h9
  have hdiv : ∀ x : Fˣ, x ^ 9 = 1 → x ^ (q + 1) = 1 := by
    intro x hx
    obtain ⟨m, hm⟩ : 9 ∣ q + 1 := by omega
    rw [hm, pow_mul, hx, one_pow]
  have hdiag : ∀ (x y z : F), x ^ (q + 1) = 1 → y ^ (q + 1) = 1 → z ^ (q + 1) = 1 →
      ((Matrix.diagonal ![x, y, z]).map (· ^ q))ᵀ * Matrix.diagonal ![x, y, z] = 1 := by
    intro x y z hx hy hz
    rw [Matrix.diagonal_map (by simp [hq0.ne'])]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three, ← pow_succ, hx, hy, hz]
  have hstd : NineFix (StatedSU 3 q F) (GeneralLinearGroup.map (σ : F →+* F)) := by
    refine nineFix_of_mem hω ?_ ?_ σ
    · intro a b ha hb
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · have ha' := a.ne_zero
        have hb' := b.ne_zero
        simp [coe_diagHom, Matrix.det_diagonal, Fin.prod_univ_three]
        field_simp
      · rw [coe_diagHom]
        have hae := hdiv a (pow_nine_eq_one hω ha)
        have hbe := hdiv b (pow_nine_eq_one hω hb)
        have hce : ((a * b)⁻¹) ^ (q + 1) = 1 := by rw [inv_pow, mul_pow, hae, hbe]; simp
        have := hdiag (a : F) (b : F) (((a * b)⁻¹ : Fˣ) : F)
          (by simpa using congrArg (fun u : Fˣ => (u : F)) hae)
          (by simpa using congrArg (fun u : Fˣ => (u : F)) hbe)
          (by simpa using congrArg (fun u : Fˣ => (u : F)) hce)
        have hfun : (fun i => ((![a, b, (a * b)⁻¹] i : Fˣ) : F)) =
            ![(a : F), (b : F), (((a * b)⁻¹ : Fˣ) : F)] := by
          funext i
          fin_cases i <;> rfl
        rw [hfun]
        exact this
    · refine Subgroup.subset_closure ⟨?_, ?_⟩
      · simp [coe_tMat, Matrix.det_fin_three]
      · rw [coe_tMat]
        have hn := neg_one_pow_eq hF
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, hn, hq0.ne']
  have hconj := nineFix_conj hstd M hMS
  exact nine_of_nineFix e ψ hM hconj

theorem tables112Types_T11_9F_holds : ∀ (K : Type) [Group K] [Finite K],
    CFSG.Open.IsQuasisimple K → CFSG.Open.IsKGroup K → IsThreeNine K →
    ∀ H : Subgroup (MulAut K), CFSG.Open.IsElemAbelian 3 H → Nat.card H = 27 →
      ∃ ψ ∈ H, ¬ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsInnerAut ψ ∧
        ∃ T P Q : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧
          P ≤ Subgroup.normalizer (T : Set K) ∧ Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
          Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) ∧ P ≤ Q ∧
          T.map ψ.toMonoidHom = T ∧ ∃ k : ℕ, ∀ x ∈ Q, ψ x = x ^ k := by
  intro K _ _ hq _ h H hH h27
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨F, _, _, q, hF2, hF, ⟨e⟩⟩
  · exact fieldNine_SL hF hq e H hH h27
  · exact fieldNine_SU hF2 hF hq e H hH h27

end CFSG.HardMathSupport.Solomon.Coordinator
