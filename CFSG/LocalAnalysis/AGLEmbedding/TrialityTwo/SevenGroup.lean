module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL27Proof
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.GL32
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenDim

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

section LThreeTwo

variable {X : Type} [Group X]

theorem exists_mul_ne_mul_of_isLThreeTwo (hX : IsLThreeTwo X) : ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple hX
  by_contra h
  push Not at h
  let _ : CommGroup X := { mul_comm := h }
  have hp := IsSimpleGroup.prime_card (α := X)
  rw [CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_card_eq hX] at hp
  norm_num at hp

theorem center_eq_bot_of_isLThreeTwo (hX : IsLThreeTwo X) : Subgroup.center X = ⊥ := by
  have hs : IsSimpleGroup X := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isLThreeTwo hX
    have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem isPerfect_of_isLThreeTwo (hX : IsLThreeTwo X) : Group.IsPerfect X := by
  have hs : IsSimpleGroup X := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple hX
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_of_isLThreeTwo hX
    have hc : ⁅a, b⁆ ∈ commutator X := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hab hc
  · exact h

end LThreeTwo

theorem pow_seven_or_pow_three_of_cubic {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {y : R}
    (h21 : y ^ 21 = 1) {c₀ c₁ c₂ : R} (h₀ : c₀ = 0 ∨ c₀ = 1) (h₁ : c₁ = 0 ∨ c₁ = 1)
    (h₂ : c₂ = 0 ∨ c₂ = 1) (h : y ^ 3 + (c₂ * y ^ 2 + c₁ * y + c₀) = 0) :
    y ^ 7 = 1 ∨ y ^ 3 = 1 := by
  rcases h₀ with rfl | rfl <;> rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    simp only [zero_mul, one_mul, add_zero, zero_add] at h <;> grind

theorem pow_seven_or_pow_three_of_GL {K : Type} [Field K] (hK : Nat.card K = 2)
    (A : GL (Fin 3) K) (h21 : A ^ 21 = 1) : A ^ 7 = 1 ∨ A ^ 3 = 1 := by
  set M := (A : Matrix (Fin 3) (Fin 3) K)
  set y : Algebra.adjoin K {M} := ⟨M, Algebra.self_mem_adjoin_singleton K M⟩
  have hy : Polynomial.aeval y M.charpoly = 0 :=
    Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact Matrix.aeval_self_charpoly M)
  rw [(Matrix.charpoly_monic M).as_sum, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hy
  simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, mul_one] at hy
  have hc : ∀ c : K, algebraMap K (Algebra.adjoin K {M}) c = 0 ∨
      algebraMap K (Algebra.adjoin K {M}) c = 1 := fun c => by
    rcases eq_zero_or_eq_one_of_card hK c with rfl | rfl
    · exact .inl (map_zero _)
    · exact .inr (map_one _)
  have h2 : (2 : Algebra.adjoin K {M}) = 0 := by
    rw [← map_ofNat (algebraMap K (Algebra.adjoin K {M})) 2, two_eq_zero_of_card hK, map_zero]
  have hy21 : y ^ 21 = 1 := Subtype.ext (by
    change M ^ 21 = 1
    rw [← Units.val_pow_eq_pow_val, h21, Units.val_one])
  have hpow : ∀ n : ℕ, y ^ n = 1 → A ^ n = 1 := fun n h => Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact congrArg Subtype.val h)
  rcases pow_seven_or_pow_three_of_cubic h2 hy21 (hc (M.charpoly.coeff 0))
    (hc (M.charpoly.coeff 1)) (hc (M.charpoly.coeff 2)) (by linear_combination hy) with h | h
  · exact .inl (hpow 7 h)
  · exact .inr (hpow 3 h)

theorem isLThreeTwo_GL_of_card {K : Type} [Field K] (hK : Nat.card K = 2) :
    IsLThreeTwo (GL (Fin 3) K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
  let φK : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  obtain ⟨d, hd, ⟨f⟩⟩ := CFSG.AGLEmbeddingD2.McLaughlin.Lie.isLThreeTwo_GL_three_two
  exact ⟨d, hd, ⟨(Units.mapEquiv (RingEquiv.mapMatrix φK).toMulEquiv).trans f⟩⟩

section Rigid

variable {X : Type} [Group X]

theorem mulAut_pow_apply (β : MulAut X) (n : ℕ) (x : X) : (β ^ n) x = β^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

theorem eq_one_of_mulAut (hX : IsLThreeTwo X) (h21 : ∀ z : X, z ^ 21 = 1 → z ^ 7 = 1 ∨ z ^ 3 = 1)
    {g : X} (hg7 : g ^ 7 = 1) (hg : g ≠ 1) (β : MulAut X) (hβ : β g = g) (h3 : β ^ 3 = 1) :
    β = 1 := by
  have hin := CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.outL27_proved X hX β 1
    (fun x => by rw [pow_one, ← mulAut_pow_apply, h3, MulAut.one_apply])
  obtain ⟨a, ha⟩ := hin
  have hcomm : Commute a g := by
    have h := ha g
    rw [hβ, eq_mul_inv_iff_mul_eq] at h
    exact h.symm
  have ha3 : a ^ 3 = 1 := by
    have hz : a ^ 3 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun γ : MulAut X => γ x) h3
      simp only [mulAut_pow_apply, MulAut.one_apply] at h
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, ha] at h
      rw [eq_comm] at h
      have key : a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ = a ^ 3 * x * (a ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      rw [key] at h
      calc x * a ^ 3 = a ^ 3 * x * (a ^ 3)⁻¹ * a ^ 3 := by rw [← h]
        _ = a ^ 3 * x := by group
    rw [center_eq_bot_of_isLThreeTwo hX, Subgroup.mem_bot] at hz
    exact hz
  have hz21 : (a * g) ^ 21 = 1 := by
    rw [hcomm.mul_pow, show 21 = 3 * 7 by rfl, pow_mul, ha3, one_pow, one_mul,
      show 3 * 7 = 7 * 3 by rfl, pow_mul, hg7, one_pow]
  have ha1 : a = 1 := by
    rcases h21 _ hz21 with h | h
    · rw [hcomm.mul_pow, hg7, mul_one, show 7 = 3 * 2 + 1 by rfl, pow_succ, pow_mul, ha3,
        one_pow, one_mul] at h
      exact h
    · rw [hcomm.mul_pow, ha3, one_mul] at h
      exfalso
      apply hg
      calc g = g ^ 7 * (g ^ 3)⁻¹ * (g ^ 3)⁻¹ := by group
        _ = 1 := by rw [hg7, h]; group
  apply MulEquiv.ext
  intro x
  rw [ha, ha1, one_mul, inv_one, mul_one, MulAut.one_apply]

end Rigid

end CFSG.AGLEmbedding.TrialityTwo.Seven
