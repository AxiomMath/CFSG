module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3EvenGL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.KFactF2Proof

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsLThreeTwo)

theorem vGL_mul_self (a b : ZMod 2) : vGL a b * vGL a b = 1 :=
  mul_eq_one_iff_inv_eq.2 (vGL_inv a b)

theorem aGL_mul_vGL_one_zero : aGL * vGL 1 0 = vGL 1 1 * aGL := by
  rw [aGL_vGL, add_zero]

theorem aGL_mul_vGL_one_one : aGL * vGL 1 1 = vGL 1 0 * vGL 1 1 * aGL := by
  rw [aGL_vGL, vGL_mul, zero_add]

theorem vGL_comm_one : vGL 1 0 * vGL 1 1 = vGL 1 1 * vGL 1 0 := by
  rw [vGL_mul, vGL_mul, zero_add, add_zero]

theorem exists_a4_pair {X : Type} [Group X] [Finite X] (hX : IsLThreeTwo X) {c : X}
    (hc : orderOf c = 3) :
    ∃ x y d : X, x ≠ 1 ∧ x * x = 1 ∧ y * y = 1 ∧ x * y = y * x ∧ d ^ 3 = 1 ∧
      (d = c ∨ d = c⁻¹) ∧ d * x = y * d ∧ d * y = x * y * d := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_isLThreeTwo hX
  set a₀ : X := e.symm aGL with ha₀
  have ha3 : a₀ ^ 3 = 1 := by rw [ha₀, ← map_pow, aGL_pow, map_one]
  have ha1 : a₀ ≠ 1 := fun h => aGL_ne (e.symm.injective (by rw [← ha₀, h, map_one]))
  have haord : orderOf a₀ = 3 := orderOf_eq_prime ha3 ha1
  have hcard := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_card_eq hX
  obtain ⟨g, hg⟩ := exists_conj_of_card_three hcard (Subgroup.zpowers a₀) (Subgroup.zpowers c)
    (by rw [Nat.card_zpowers, haord]) (by rw [Nat.card_zpowers, hc])
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg a₀ (Subgroup.mem_zpowers a₀))
  have hc3 : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc] at this
  have hmod : c ^ (k % 3) = c ^ k := by
    have := zpow_mod_orderOf c k
    rwa [hc, Nat.cast_ofNat] at this
  have hcase : g * a₀ * g⁻¹ = c ∨ g * a₀ * g⁻¹ = c⁻¹ := by
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have hk' : c ^ (k % 3) = g * a₀ * g⁻¹ := by rw [hmod, hk]
    interval_cases hm : k % 3
    · exfalso
      apply ha1
      have : g * a₀ * g⁻¹ = 1 := by rw [← hk']; simp
      have := mul_inv_eq_one.1 this
      simpa using this
    · left
      have : c = g * a₀ * g⁻¹ := by rw [← hk']; simp
      exact this.symm
    · right
      have h2 : c ^ 2 * c = 1 := by rw [← pow_succ]; exact hc3
      have h2' : c ^ 2 = c⁻¹ := eq_inv_of_mul_eq_one_left h2
      have hinv : c⁻¹ = g * a₀ * g⁻¹ := by
        rw [← h2', ← hk']
        simp [zpow_two, pow_two]
      exact hinv.symm
  let φ : GL (Fin 3) (ZMod 2) ≃* X := e.symm.trans (MulAut.conj g)
  have hφ : φ aGL = g * a₀ * g⁻¹ := rfl
  refine ⟨φ (vGL 1 0), φ (vGL 1 1), φ aGL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact vGL_ne_one (φ.injective (by rw [h, map_one]))
  · rw [← map_mul, vGL_mul_self, map_one]
  · rw [← map_mul, vGL_mul_self, map_one]
  · simpa only [map_mul] using congrArg φ vGL_comm_one
  · rw [← map_pow, aGL_pow, map_one]
  · rw [hφ]
    exact hcase
  · simpa only [map_mul] using congrArg φ aGL_mul_vGL_one_zero
  · simpa only [map_mul] using congrArg φ aGL_mul_vGL_one_one

end CFSG.LocalAnalysis.RankThreeUC.S15.KFactF2Proof
