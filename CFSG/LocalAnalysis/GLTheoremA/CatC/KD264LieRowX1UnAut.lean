module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnGoodBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowX1Un

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

theorem mem_range_xunConj_of_pow_three4 {N : ℕ} (hN : 4 ≤ N) (α : MulAut (xunM N))
    (h3 : α ^ 3 = 1) : ∃ g : uU xunH N, xunConj N (by omega) g = α := by
  have hN3 : 3 ≤ N := by omega
  have hq : ¬(N = 3 ∧ 2 ^ 1 = 2) := fun h => by omega
  obtain ⟨A, φ, hα⟩ := exists_uConjAut_mul_uFieldAut xunH hN3 hq α
  have hφ3 : φ ^ 3 = 1 := by
    have := congrArg (uFactor xunH hN3 hq) h3
    rw [map_pow, hα, uFactor_apply, map_one] at this
    exact this
  rcases CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.ringEquiv_eq_refl_or_bar xunH φ with
    h1 | h1
  · refine ⟨A, ?_⟩
    have hφ1 : φ = 1 := h1
    subst hφ1
    rw [hα, map_one]
    exact (mul_one _).symm
  · exfalso
    obtain ⟨ω, hω0, hω1⟩ :=
      CFSG.LocalAnalysis.GorensteinLyons.FourUnitary.exists_ne_zero_ne_one xunH
    have hb : ∀ a : xunK, φ a = a ^ 2 := fun a => by
      rw [h1 a, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
      norm_num
    haveI : Fintype xunK := Fintype.ofFinite xunK
    have hcard : Fintype.card xunK = 4 := by
      rw [← Nat.card_eq_fintype_card, xunK_card]
      norm_num
    have hpow : ω ^ 4 = ω := by
      have := FiniteField.pow_card ω
      rw [hcard] at this
      exact this
    have h3ω : φ (φ (φ ω)) = ω := by
      have e3 : (φ ^ 3) ω = φ (φ (φ ω)) := by
        rw [pow_succ, pow_two]
        rfl
      rw [← e3, hφ3]
      rfl
    rw [hb, hb, hb] at h3ω
    have h8 : ω ^ 8 = ω ^ 2 := by
      calc ω ^ 8 = (ω ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ω ^ 2 := by rw [hpow]
        _ = ω ^ 2 := rfl
    rw [show ((ω ^ 2) ^ 2) ^ 2 = ω ^ 8 by ring, h8] at h3ω
    have : ω * (ω - 1) = 0 := by linear_combination h3ω
    rcases mul_eq_zero.1 this with h | h
    · exact hω0 h
    · exact hω1 (sub_eq_zero.1 h)

theorem le_range_xunConj_of_isElemAbelian4 {N : ℕ} (hN : 4 ≤ N)
    (A : Subgroup (MulAut (xunM N))) (hA : IsElemAbelian 3 A) :
    ∀ a ∈ A, ∃ g : uU xunH N, xunConj N (by omega) g = a :=
  fun a ha => mem_range_xunConj_of_pow_three4 hN a (hA.2 a ha)

theorem statedScalars_subgroupOf_eq_bot {N : ℕ} (h3 : ¬ 3 ∣ N) :
    (CFSG.Open.StatedScalars (Fin N) xunK).subgroupOf
      (CFSG.Open.StatedSU N (2 ^ 1) xunK) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hx
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU x.2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at hdet
  have hdet' : (c : xunK) ^ N = 1 := by
    rw [Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  have hc3 : (c : xunK) ^ 3 = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good.pow_three_eq_one_of_ne_zero
      (Units.ne_zero c)
  have hg : Nat.gcd N 3 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  have hc1 : (c : xunK) = 1 := by
    have := (pow_gcd_eq_one).2 ⟨hdet', hc3⟩
    rwa [hg, pow_one] at this
  have hc' : c = 1 := Units.ext hc1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc', map_one]
  rfl

theorem pRank_xunM_ge {N : ℕ} (hN : 2 ≤ N) (h3 : ¬ 3 ∣ N) :
    N - 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (xunM N)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card xunK = (2 ^ 1) ^ 2 := by
    rw [xunK_card]
    norm_num
  have key := CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := xunK)
    (p := 2) (f := 1) (n := N) (r := 3) Nat.prime_two hN (by norm_num)
    (H := CFSG.Open.StatedSU N (2 ^ 1) xunK) (Or.inr ⟨hK, rfl, by norm_num⟩)
    ((CFSG.Open.StatedScalars (Fin N) xunK).subgroupOf (CFSG.Open.StatedSU N (2 ^ 1) xunK))
    le_rfl
  apply key.2
  rw [statedScalars_subgroupOf_eq_bot h3, Subgroup.card_bot]
  norm_num

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowX1Un

end
