module

public import CFSG.GH74.Generic.BProg.B2.GenLocL2SL3

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open scoped MatrixGroups

theorem genLoc_psl2
    {J : Type} [Group J] [Finite J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hJ : LieModel J .PSL 2 p f) : GenLoc J :=
  genLoc_psl2_of_small_loc hp hp2 h5 hJ
    (fun hq _ _ _ α hA hg => loc_psl2_small hp hp2 hq hJ α hA hg)

section SL2Small

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_sl2_rank3_lt25
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h11 : 11 ≤ p ^ f) (hlt : p ^ f < 25)
    (α : A →* MulAut (SL(2, K))) (hA : IsRank23 A) (hk : pRank 2 A = 3) : gammaAct α = ⊤ := by
  have _ := hk
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h11
      omega
    · exact h0
  have hfodd : Odd f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hf2 : f ≤ 2 := by
      by_contra hf
      have h1 : 3 ^ 3 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 3 ^ f ≤ p ^ f := Nat.pow_le_pow_left hp3 f
      omega
    have hf2' : f ≠ 2 := by
      intro h
      subst h
      have hp4 : 4 ≤ p := by nlinarith
      have hp4' : p ≤ 4 := by nlinarith
      have : p = 4 := le_antisymm hp4' hp4
      subst this
      exact absurd hp (by norm_num)
    interval_cases f
    · exact odd_one
    · exact absurd rfl hf2'
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h3 : 3 < Nat.card K := by
    rw [hK]
    omega
  have hOPP : IsOddPrimePower (Nat.card K) := isOddPrimePower_of hp hp2 hf1 hK
  by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hle⟩ := hker
    exact gammaAct_eq_top_of_le_ker α hE hle
  push Not at hker
  obtain ⟨hD, hγ, -⟩ := range_reduction α hA (fun E hE hle => hker E hE hle)
  rw [hγ]
  have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card α.range = 4 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
      norm_num
    rcases GenLocL2SL.gammaAct_sl2_core hp hp2 hK (by omega) hD.1 h4 α.range.subtype with h | ⟨hq, -⟩
    · exact h
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      omega
  · exfalso
    have h8 : Nat.card α.range = 8 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
      norm_num
    set ι : ↥α.range →* PGammaL2 K :=
      (GLS.IVK.Lifted.gammaOf hodd h3).comp α.range.subtype with hι
    have hιinj : Function.Injective ι :=
      (GLS.IVK.Lifted.gammaOf_injective hodd h3).comp Subtype.val_injective
    set E' : Subgroup (PGammaL2 K) := ι.range with hE'
    have hDsq : ∀ x : α.range, x * x = 1 := fun x =>
      WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD.1 x
    have hE2 : ∀ x ∈ E', x * x = 1 := by
      rintro _ ⟨x, rfl⟩
      rw [← map_mul, hDsq x, map_one]
    have hle := GenLocL2.pGammaL2_card_le_four_of_sq_of_odd hp hp2 hfodd hK E' hE2
    have hE8 : Nat.card E' = 8 := by
      rw [hE', ← h8]
      exact (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
    omega

end SL2Small

section SL2Fam

theorem genLoc_sl2_of_rank3
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (hr3 : ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut (SL(2, K))), IsRank23 A →
      pRank 2 A = 3 → 25 ≤ p ^ f → gammaAct α = ⊤)
    {J : Type} [Group J] (e : J ≃* SL(2, K)) : GenLoc J := by
  refine GenLoc.of_mulEquiv e.symm ?_
  intro A _ _ α hA
  by_cases hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)
  · by_cases hg : gammaAct α = ⊤
    · exact Or.inl hg
    · exact Or.inr (loc_sl2_small hp hp2 hK hq α hA hg)
  · left
    have hq' : ¬ (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hq
    have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2).pow
    have h11 : 11 ≤ p ^ f := by omega
    rcases hA.2 with hk | hk
    · exact gammaAct_sl2_rank2 hp hp2 hK h5 α hA hk (fun h => hq h.1)
    · by_cases h25 : 25 ≤ p ^ f
      · exact hr3 A α hA hk h25
      · exact gammaAct_sl2_rank3_lt25 hp hp2 hK h11 (by omega) α hA hk

theorem genLoc_sl2
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {J : Type} [Group J]
    (e : J ≃* SL(2, K)) : GenLoc J :=
  genLoc_sl2_of_rank3 hp hp2 hK h5
    (fun _ _ _ α hA hk h25 => gammaAct_sl2_rank3 hp hp2 hK h25 α hA hk) e

end SL2Fam

end CFSG.GH74.Generic.BProg.B2
