module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I714FourAut
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor lieSylowExponent LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.Coordinator (OuterFixedOrderBoundCyc)

theorem not_five_dvd_lieOrderDivisor (t : StatedLieTag) (n : ℕ) {f : ℕ} (hf : 1 ≤ f) :
    ¬ 5 ∣ lieOrderDivisor t n (5 ^ f) := by
  have h5 : 5 ∣ 5 ^ f := dvd_pow_self 5 (by omega)
  have hpos : 1 ≤ 5 ^ f := Nat.one_le_pow _ _ (by norm_num)
  intro h
  cases t
  · simp only [lieOrderDivisor] at h
    have h1 : 5 ∣ 5 ^ f - 1 := h.trans (Nat.gcd_dvd_right _ _)
    have h2 : 5 ∣ 5 ^ f - (5 ^ f - 1) := Nat.dvd_sub h5 h1
    rw [Nat.sub_sub_self hpos] at h2
    omega
  · simp only [lieOrderDivisor] at h
    have h1 : 5 ∣ 5 ^ f + 1 := h.trans (Nat.gcd_dvd_right _ _)
    have h2 : 5 ∣ 1 := (Nat.dvd_add_right h5).mp h1
    omega
  all_goals
    simp only [lieOrderDivisor] at h
    first
      | omega
      | exact absurd (h.trans (Nat.gcd_dvd_left _ _)) (by omega)

theorem false_of_lieModel_char_five (hbound : OuterFixedOrderBoundCyc)
    (hord : LieOrderFormulasInput) {X : Type} [Group X] [Finite X] {K : Subgroup X}
    [K.Normal] (hC : Subgroup.centralizer (K : Set X) = ⊥) {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 5 f) (hmodel : CFSG.Blueprint.LieModel ↥K t n 5 f)
    (h5 : (Nat.card ↥K).factorization 5 = 2) {a : X} (haK : a ∉ K) (ha5 : a ^ 5 = 1) :
    False := by
  have hf : 1 ≤ f := hadm.2.1
  have ht : t ≠ .Tits := by
    rintro rfl
    obtain ⟨-, -, -, h2, -⟩ := hadm
    omega
  have hαp : (MulAut.conjNormal (H := K) a) ^ 5 = 1 := by rw [← map_pow, ha5, map_one]
  have hαin : MulAut.conjNormal (H := K) a ∉ inner ↥K := fun h =>
    haK (mem_of_conjNormal_mem_inner hC h)
  obtain ⟨f₀, hff₀, -⟩ := hbound ↥K t n 5 f hadm hmodel ht 5 Nat.prime_five (by norm_num)
    (not_five_dvd_lieOrderDivisor t n hf) (by simp) (by simp) _ hαp hαin
  obtain ⟨-, -, hfac⟩ := hord ↥K t n 5 f hadm hmodel
  have hN : 1 ≤ lieSylowExponent t n := CFSG.AGLEmbedding.OuterSylow.one_le_lieSylowExponent hadm
  have hf5 : 5 ≤ f := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hff₀
      omega
    · omega
  have : 1 * 5 ≤ lieSylowExponent t n * f := Nat.mul_le_mul hN hf5
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
