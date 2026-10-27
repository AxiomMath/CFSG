module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem i2018_lie (hOdd : I2018OddB3) (hChar : I2018U38Char2) (hBT : I2018BorelTits) (hCore : I2018ChevCore)
    {X K J S₀ : Subgroup G} {x : G}
    (hK : GLAPComponent 3 X K) (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1)
    (hJ : GLAPComponent 3 (K ⊓ cx x) J) (hU : catalogIs (PSimple 3 J) CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight)
    (hS₀K : S₀ ≤ K) (hS₀2 : IsPGroup 2 S₀) (hJS : ⁅S₀, J⁆ = S₀) (hS₀n : ¬ S₀ ≤ GLAPPrimeCoreOf 3 K)
    (r : ℕ) (hr : r.Prime) (hχ : IsChevSimple r (PSimple 3 K)) :
    IsChevSimple 2 (PSimple 3 K) ∧ ¬ IsTD4 3 K ∧
      GLAMarking (PQuot 3 K) (fun lab _ _ _ _ _ => (lab.n = 1 ∧ 2 ^ 6 < card2 3 K) ∨ (lab.n = 3 ∧ 2 ^ 18 < card2 3 K)) := by
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
  haveI := hsimple
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hx3
  have hα3 : (chevAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := chevAut_pow_eq_one 3 K hxN hx3
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hxN hxp hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxN hxp hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) CFSG.LocalAnalysis.GLTheoremA.S9.isU3eight :=
    catalogIs_congr' eJ hU
  have hr2 : r = 2 := by
    by_contra hne
    have hD := hOdd r hr hne
    have hJχ : IsChevSimple r (PSimple 3 (chevTransfer 3 K J)) :=
      hD (PSimple 3 K) hsimple hna hχ _ hα3 _ hJ'
    exact hne (hChar _ hU' r hJχ)
  subst hr2
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have hT_ne : chevTransfer 3 K S₀ ≠ ⊥ := chevTransfer_ne_bot hJK hS₀K hJS hS₀n
  have hT_p : IsPGroup 2 (chevTransfer 3 K S₀) := isPGroup_chevTransfer hS₀2 hS₀K
  have hT_comm := chevTransfer_commutator hJK hS₀K hJS
  have hJN := le_normalizer_of_commutator_eq hT_comm
  obtain ⟨P, hP, hTP, hNP⟩ := hBT (PSimple 3 K) hsimple hχ _ hT_p hT_ne
  have hJP : chevTransfer 3 K J ≤ P := hJN.trans hNP
  obtain ⟨hnotTD4, lab, hlab, hbd, hraw⟩ :=
    hCore (PSimple 3 K) hsimple hna hχ _ hα3 P hP _ hTP hT_ne _ hJ' hJP hU'
  have hle := twoPart_pSimple_le_card2 K
  have hbd' : (lab.n = 1 ∧ 2 ^ 6 < card2 3 K) ∨ (lab.n = 3 ∧ 2 ^ 18 < card2 3 K) := by
    rcases hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, lt_of_lt_of_le h2 hle⟩
    · exact Or.inr ⟨h1, lt_of_lt_of_le h2 hle⟩
  exact ⟨hχ, hnotTD4, gla_marking_of_raw hq lab hlab hbd' hraw⟩

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
