module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GUNormal
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU

open scoped MatrixGroups
open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

section Field

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def invol (h : UnitaryFieldData p f K) : K ≃+* K :=
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have := h.finite
  CFSG.LieType.BorelTits.unitaryInvolution K p f

theorem invol_apply (h : UnitaryFieldData p f K) (c : K) : invol h c = h.bar c := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have := h.finite
  exact CFSG.LieType.BorelTits.unitaryInvolution_apply K p f c

theorem isUnitaryInvolution_invol (h : UnitaryFieldData p f K) :
    IsUnitaryInvolution (invol h) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have := h.finite
  exact CFSG.LieType.SeitzGeneration.Nonsplit.isUnitaryInvolution h

theorem mem_unitaryIsom3_iff (h : UnitaryFieldData p f K) {A : GL (Fin 3) K} :
    A ∈ unitaryIsom3 h ↔ conjTr (invol h) (A : Matrix (Fin 3) (Fin 3) K) *
      (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [mem_unitaryIsom3, conjTr]
  have : (A : Matrix (Fin 3) (Fin 3) K).map (invol h) = (A : Matrix (Fin 3) (Fin 3) K).map h.bar :=
    Matrix.ext fun i j => by simp [Matrix.map_apply, invol_apply h]
  rw [this]

theorem hF3_of_dvd (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1) :
    ∀ ν : K, invol h ν = ν → ν ^ 3 = 1 → ν = 1 := by
  intro ν hν hν3
  rw [invol_apply, UnitaryFieldData.bar_apply] at hν
  obtain ⟨m, hm⟩ := h3
  have hq : p ^ f = 3 * (m - 1) + 2 := by
    have : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · omega
      · exact hpos
    omega
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν3
  rw [hq, pow_add, pow_mul, hν3, one_pow, one_mul] at hν
  have : ν * (ν - 1) = 0 := by linear_combination hν
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hν0
  · exact sub_eq_zero.mp h0

theorem three_dvd_card_sub_one (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1) :
    3 ∣ Nat.card K - 1 := by
  rw [h.card, pow_mul']
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, p ^ f = m + 1 := ⟨p ^ f - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [this]
  exact Dvd.dvd.mul_right h3 _

end Field

theorem eigSep_of_pow_three {n : ℕ} {K : Type} [Field K] {σ : K ≃+* K} (hσ : IsUnitaryInvolution σ)
    (hF3 : ∀ ν : K, σ ν = ν → ν ^ 3 = 1 → ν = 1) {T : Matrix (Fin n) (Fin n) K} {s : K}
    (hT : T ^ 3 = Matrix.scalar (Fin n) s) : EigSep σ T := by
  intro u u' l l' hu hu' hl hl' hll
  have key : ∀ (x : Fin n → K) (l : K), x ≠ 0 → T *ᵥ x = l • x → l ^ 3 = s := by
    intro x l hx hl
    have e : T *ᵥ (T *ᵥ (T *ᵥ x)) = l ^ 3 • x := by
      simp only [hl, mulVec_smul, smul_smul]
      congr 1
      ring
    have e2 : T *ᵥ (T *ᵥ (T *ᵥ x)) = s • x := by
      rw [mulVec_mulVec, mulVec_mulVec, show T * T * T = T ^ 3 by rw [pow_succ, pow_two], hT,
        scalar_mulVec']
    have : (l ^ 3 - s) • x = 0 := by rw [sub_smul, ← e, ← e2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx
  have h1 := key u l hu hl
  have h2 := key u' l' hu' hl'
  have hl0 : σ l ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hll
    exact zero_ne_one hll
  have hν : σ l * l = 1 := by
    have h3 : (σ l * l) ^ 3 = 1 := by
      have : (σ l) ^ 3 * l' ^ 3 = 1 := by rw [← mul_pow, hll, one_pow]
      rw [mul_pow, h1, ← h2]
      exact this
    exact hF3 _ (by rw [map_mul, hσ.invol, mul_comm]) h3
  exact (mul_left_cancel₀ hl0 (hν.trans hll.symm))

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU
