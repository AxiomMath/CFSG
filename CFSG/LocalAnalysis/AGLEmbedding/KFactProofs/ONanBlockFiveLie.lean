module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeLie
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabAutIrr
  CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem lieFive_of_model_psl {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSL n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hJtop : J ≠ ⊤) :
    HasE9 Y ∨ (∃ f' : ℕ, Odd f' ∧ StatedClassicalModel Y .PSL 3 2 f') ∨
      Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  have h' := h
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ePSL := (projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | hm
  · exfalso
    obtain ⟨i, j, hij⟩ := (borelQuotient_sl ePSL).exists_two_nodes T J hNJ hJ hJtop
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    exact hij (Fin.ext (by omega))
  · by_cases hfe : Even f
    · exact Or.inl (hasE9_psl_three_of_even h' hfe)
    · exact Or.inr (Or.inl ⟨f, Nat.not_even_iff_odd.1 hfe, h'⟩)
  · exact Or.inl (hasE9_psl_of_three_le hm ePSL)

theorem hasE9_or_five_of_small {Y : Type} [Group Y] [Finite Y] (hS : IsSmallTwo Y) :
    HasE9 Y ∨ (∃ f : ℕ, Odd f ∧ StatedClassicalModel Y .PSL 3 2 f) ∨
      Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨e⟩)
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
  · rcases hd with ⟨q, hq7, hd1⟩ | ⟨q, hq3, hd1⟩
    ·
      obtain rfl : idx = .A 1 q := hd1
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hpe : q.p = 7 ∧ q.exponent = 1 := by
        have h7 : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq7
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h7
      rw [hpe.1, hpe.2] at h
      exact Or.inr (Or.inl ⟨1, odd_one,
        CFSG.QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven
          h⟩)
    ·
      obtain rfl : idx = .twistedA 2 q := hd1
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hpe : q.p = 3 ∧ q.exponent = 1 := by
        have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq3
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h3
      rw [hpe.1, hpe.2] at h
      exact Or.inl (hasE9_of_model_psu_three_three h)

theorem lieFiveParabolic_of (hG2 : LieCyclicG2) :
    ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y,
      IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
        J ≠ Subgroup.normalizer (T : Set Y) → J ≠ ⊤ →
          HasE9 Y ∨ (∃ f : ℕ, Odd f ∧ StatedClassicalModel Y .PSL 3 2 f) ∨
            Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  intro Y _ _ hY T J hT hNJ hJ hJtop
  obtain ⟨T', rfl⟩ := exists_sylow_of_isSylowTwoOf_top hT
  rcases isClassicalTwoOrG2_cases hY with ⟨t, n, f, ht, h⟩ | hG | hS
  · rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact lieFive_of_model_psl h T' J hNJ hJ hJtop
    · exact Or.inl (hasE9_of_model_psu_of_parabolic h T' J hNJ hJ hJtop)
    · exact Or.inl (hasE9_of_model_psp h)
    · exact Or.inl (hasE9_of_model_pomegaPlus h)
    · exact Or.inl (hasE9_of_model_pomegaMinus h)
  · exact Or.inl (hG2 Y hG)
  · exact hasE9_or_five_of_small hS

theorem lieFiveOrthogonal :
    ∀ (Y : Type) [Group Y] [Finite Y], IsOrthogonalTwo Y →
      HasE9 Y ∨ Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  intro Y _ _ hY
  rcases hY with ⟨⟨d, hv⟩, ⟨m, q, hq, hdm⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hp2 := p_eq_two_of_card_eq_two hq
    rcases hdm with rfl | rfl | ⟨rfl, rfl⟩
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hp2 e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_pomegaPlus h)
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hp2 e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_pomegaMinus h)
    · have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hp2] at h
      exact Or.inl (hasE9_of_model_psu h (by norm_num))
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr ⟨e⟩
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))

end CFSG.AGLEmbedding.BlockCyc
