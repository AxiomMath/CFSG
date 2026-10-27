module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Even
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Bad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddGood
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreAction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrob

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem odd_index_of_odd (hF : Nat.card F = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1) {ω : Fˣ} (hω : orderOf ω = 3)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hNW : normA0 hF ω ≤ W)
    (hW : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W) : ¬ 2 ∣ W.index := by
  have hodd : p ^ f % 2 = 1 := by
    have : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
    exact Nat.odd_iff.1 this.pow
  by_cases h4 : p ^ f % 4 = 1
  ·
    have hω' : ω ^ (p ^ f) = ω := pow_eq_self_of_orderOf_three hω hq3
    have hTW : (tSU hF).range ≤ W := (range_tSU_le_normA0 hF hω hq3).trans hNW
    have hsW : (sSU : SU (unitaryInvolution F p f) 3) ∈ W := by
      refine hNW (mem_normalizer_zpowers_of_inv sSU_mul_self ?_)
      rw [sSU_conj_tSU, hω', map_inv]
    have hn : ∀ x ∈ (tSU hF).range, (sSU : SU (unitaryInvolution F p f) 3) * x * sSU⁻¹ ∈
        (tSU hF).range := by
      rintro _ ⟨μ, rfl⟩
      rw [sSU_conj_tSU]
      exact ⟨_, rfl⟩
    have hdvd := two_mul_card_dvd_of_involution sSU_mul_self (sSU_not_mem_range hF) hn hTW hsW
    refine not_two_dvd_index_of_dvd_card hdvd ?_
    rw [card_range_tSU hF, card_SU3 hF]
    exact not_four_mul_dvd_card _ h4 (two_le_q hF)
  · have hq4 : p ^ f % 4 = 3 := by omega
    by_cases hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω
    ·
      obtain ⟨ν, -, hν2, hνq⟩ := exists_unit_orderOf_card_add_one hF hp2
      have hB := badCase_model hF hp2 hω hq3 hq4 hν2 hνq hNW hbad
      exact absurd (S3AmalgamBound.OvergroupA5.isPSolvable_of_isSolvable Nat.prime_three
        (BadCase.isSolvable hB)) hW
    ·
      push Not at hbad
      have hK : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield hF
      refine u3OddGood_of_dickson hF hp2 hq3 hq4 ?_ ω hω W hNW hbad
      intro A H hA _ hAH
      exact psl2_normalizer_three_dichotomy hK (by rw [hK]; exact hq3) (by rw [hK]; exact hq4)
        hA hAH

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem exists_orderOf_three (hF : Nat.card F = (p ^ f) ^ 2) (hq3 : p ^ f % 3 = 1) :
    ∃ ω : Fˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h2 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    have h3 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by have := two_le_q hF; omega)
    omega
  exact exists_prime_orderOf_dvd_card' 3 hF3

theorem overgroupOddIndex_SU3 (hF : Nat.card F = (p ^ f) ^ 2)
    (hq3 : p ^ f % 3 = 1) : OvergroupOddIndex (SU (unitaryInvolution F p f) 3) := by
  intro _ hcyc A W hA hNW hW h16
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_orderOf_three hF hq3
  have hA0 : Nat.card (Subgroup.zpowers (tSU hF ω)) = 3 := by
    rw [Nat.card_zpowers, orderOf_injective _ (tSU_injective hF) ω, hω]
  obtain ⟨g, hg⟩ := OrdinaryProofs.L3Leaves.exists_conj_eq_of_card_eq_three hcyc hA hA0
  set W' := W.map (MulAut.conj g).toMonoidHom
  have hNW' : normA0 hF ω ≤ W' := by
    show Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) : Subgroup _) : Set _) ≤ W'
    rw [hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNW
  have hW' : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W' := fun hs =>
    hW (OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (W.equivMapOfInjective _ (MulAut.conj g).injective).symm hs)
  have hidx : W'.index = W.index := Subgroup.index_map_equiv W (MulAut.conj g)
  rw [← hidx] at h16 ⊢
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  by_cases hp2 : p = 2
  · subst hp2
    rcases odd_or_sixteen_dvd_index hF hq3 hω hNW' with h | h
    · exact h
    · exact absurd h h16
  · exact odd_index_of_odd hF hp2 hq3 hω hNW' hW'

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
