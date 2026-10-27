module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.GL32

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

@[expose] def matB : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def matA : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

theorem matB_mul : matB * matB ^ 6 = 1 := by unfold matB; decide +kernel
theorem matB_mul' : matB ^ 6 * matB = 1 := by unfold matB; decide +kernel
theorem matA_mul : matA * matA ^ 2 = 1 := by unfold matA; decide +kernel
theorem matA_mul' : matA ^ 2 * matA = 1 := by unfold matA; decide +kernel
theorem matB_pow : matB ^ 7 = 1 := by unfold matB; decide +kernel
theorem matB_ne : matB ≠ 1 := by unfold matB; decide +kernel
theorem matA_pow : matA ^ 3 = 1 := by unfold matA; decide +kernel
theorem matA_ne : matA ≠ 1 := by unfold matA; decide +kernel
theorem matA_matB : matA * matB = matB ^ 2 * matA := by unfold matA matB; decide +kernel

@[expose] def bGL : GL (Fin 3) (ZMod 2) := ⟨matB, matB ^ 6, matB_mul, matB_mul'⟩

@[expose] def aGL : GL (Fin 3) (ZMod 2) := ⟨matA, matA ^ 2, matA_mul, matA_mul'⟩

theorem bGL_pow : bGL ^ 7 = 1 := Units.ext (by
  rw [Units.val_pow_eq_pow_val]; exact matB_pow)

theorem bGL_ne : bGL ≠ 1 := fun h => matB_ne (congrArg Units.val h)

theorem aGL_pow : aGL ^ 3 = 1 := Units.ext (by
  rw [Units.val_pow_eq_pow_val]; exact matA_pow)

theorem aGL_matB : aGL * bGL = bGL ^ 2 * aGL := Units.ext (by
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]; exact matA_matB)

theorem aGL_ne : aGL ≠ 1 := fun h => matA_ne (congrArg Units.val h)

section Pair

variable {X : Type} [Group X]

theorem nonempty_mulEquiv_GL_of_isLThreeTwo (hX : IsLThreeTwo X) :
    Nonempty (X ≃* GL (Fin 3) (ZMod 2)) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have key : ∀ {Z : Type} [Group Z], IsLThreeTwo Z → Nonempty (Z ≃* CFSG.AGLEmbedding.PSL2GF 7 1) := by
    intro Z _ hZ
    obtain ⟨d, hd, ⟨e⟩⟩ := hZ
    obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
      (CFSG.AGLEmbeddingD2.McLaughlin.isLinTwoIndex_seven_one hd)
    exact ⟨e.trans e2⟩
  obtain ⟨e1⟩ := key hX
  obtain ⟨e2⟩ := key CFSG.AGLEmbeddingD2.McLaughlin.Lie.isLThreeTwo_GL_three_two
  exact ⟨e1.trans e2.symm⟩

theorem exists_conj_of_card_three [Finite X] (hX : Nat.card X = 168) (C₀ C : Subgroup X)
    (h0 : Nat.card C₀ = 3) (h1 : Nat.card C = 3) : ∃ g : X, ∀ x ∈ C₀, g * x * g⁻¹ ∈ C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : (Nat.card X).factorization 3 = 1 := by
    rw [hX, Nat.factorization_def _ Nat.prime_three]
    decide +kernel
  let P₀ : Sylow 3 X := Sylow.ofCard C₀ (by rw [h0, hf]; norm_num)
  let P₁ : Sylow 3 X := Sylow.ofCard C (by rw [h1, hf]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₀ P₁
  refine ⟨g, fun x hx => ?_⟩
  have hx' : MulAut.conj g • x ∈ MulAut.conj g • (P₀ : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hx
  rw [← Sylow.coe_subgroup_smul, hg] at hx'
  simp only [MulAut.smul_def, MulAut.conj_apply] at hx'
  exact hx'

theorem exists_frobenius_pair [Finite X] (hX : IsLThreeTwo X) {c : X} (hc : orderOf c = 3) :
    ∃ b : X, b ^ 7 = 1 ∧ b ≠ 1 ∧ (c * b = b ^ 2 * c ∨ c⁻¹ * b = b ^ 2 * c⁻¹) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_GL_of_isLThreeTwo hX
  set a₀ : X := e.symm aGL with ha₀
  set b₀ : X := e.symm bGL with hb₀
  have hab : a₀ * b₀ = b₀ ^ 2 * a₀ := by
    rw [ha₀, hb₀, ← map_mul, aGL_matB, map_mul, map_pow]
  have hb7 : b₀ ^ 7 = 1 := by rw [hb₀, ← map_pow, bGL_pow, map_one]
  have hb1 : b₀ ≠ 1 := fun h => bGL_ne (e.symm.injective (by rw [← hb₀, h, map_one]))
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
  have hrel : ∀ y : X, y = g * a₀ * g⁻¹ → y * (g * b₀ * g⁻¹) = (g * b₀ * g⁻¹) ^ 2 * y := by
    intro y hy
    rw [hy]
    calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
      _ = g * (b₀ ^ 2 * a₀) * g⁻¹ := by rw [hab]
      _ = (g * b₀ * g⁻¹) ^ 2 * (g * a₀ * g⁻¹) := by rw [conj_pow]; group
  refine ⟨g * b₀ * g⁻¹, by rw [conj_pow, hb7]; group, ?_, ?_⟩
  · intro h
    apply hb1
    have : g * b₀ * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    simpa using this
  · have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have hk' : c ^ (k % 3) = g * a₀ * g⁻¹ := by rw [hmod, hk]
    interval_cases hm : k % 3
    · exfalso
      apply ha1
      have : g * a₀ * g⁻¹ = 1 := by rw [← hk']; simp
      have := mul_inv_eq_one.1 this
      simpa using this
    · left
      apply hrel
      rw [← hk']; simp
    · right
      have h2 : c ^ 2 * c = 1 := by rw [← pow_succ]; exact hc3
      have h2' : c ^ 2 = c⁻¹ := eq_inv_of_mul_eq_one_left h2
      have hinv : c⁻¹ = g * a₀ * g⁻¹ := by
        rw [← h2', ← hk']
        simp [zpow_two, pow_two]
      exact hrel _ hinv

end Pair

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
