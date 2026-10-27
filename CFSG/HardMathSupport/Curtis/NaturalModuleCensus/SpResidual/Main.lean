module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Main
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.Reduction
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.FixedEscape
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.OddFixed
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.TrivialTwo
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.CycFour
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.SiegelThree

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

theorem false_of_fixBarFull_sp_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {J : Subgroup (StatedSp 2 K)} {v : StatedSp 2 K}
    (h : FixBarFull J 3 v) : False := by
  obtain ⟨I, v', hI, hI0, h'⟩ := SpResidual.exists_flagStabilizer_fixBarFull h
  have hp0 : ((3 : ℕ) : K) ≠ 0 := fun h0 => by
    have := (CharP.cast_eq_zero_iff K 2 3).1 h0
    omega
  by_cases hA : ∃ i ∈ I, i = 1 ∨ i - 1 ∈ I
  · obtain ⟨i, hi, hi1⟩ := hA
    refine false_of_fixBarData_flagStabilizer_caseA hK hp0 hI hi hi1 h'.base.join h'.base.pow
      (fun V hV _ g hg => h'.fix_all g ?_)
    exact ((Subgroup.mem_centralizer_iff.1 (hV hg)) v' (Set.mem_singleton _)).symm
  · push Not at hA
    obtain ⟨i, hi⟩ := hI0
    have hI2 : I = {2} := by
      ext j
      constructor
      · intro hj
        have := hI j hj
        have := (hA j hj).1
        simp only [Set.mem_singleton_iff]
        omega
      · intro hj
        rw [Set.mem_singleton_iff] at hj
        have := hI i hi
        have := hA i hi
        subst hj
        have : i = 2 := by omega
        rw [← this]; exact hi
    subst hI2
    exact SpResidual.SiegelThree.false_of_siegel_three h'.base.join h'.base.pow h'.fix_all

namespace SpResidual

variable {r : ℕ}

theorem false_of_odd_or_two {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r)
    {v : StatedSp r (ZMod 2)}
    (h : FixBarFull (flagStabilizer r (ZMod 2) I) 3 v)
    (hcase : (∃ i ∈ I, Odd i) ∨ 2 ∈ I) : False := by
  have hp0 : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide
  have hvJ : v ∈ flagStabilizer r (ZMod 2) I := perfectJoin_le _ h.base.join
  rcases hcase with ⟨i, hi, hio⟩ | h2
  · obtain ⟨a, haF, ha0, hva⟩ := OddFixed.exists_fixed_vector_of_odd hI hi hio h.base.pow hvJ
    exact FixedEscape.false_of_fixed_vector_flag hp0 hI h.base.pow h.fix_all hi haF ha0 hva
  · have hr : 2 ≤ r := (hI 2 h2).2
    have hfix2 := TrivialTwo.fixes_flag_two_of_mem_perfectJoin hI h2 h.base.join
    have hF : (Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin r ⊕ Fin r → ZMod 2) ∈
        SymplecticFlag.flag r (ZMod 2) 2 := single_mem_flag hr 0 (by omega) (by omega)
    refine FixedEscape.false_of_fixed_vector_flag hp0 hI h.base.pow h.fix_all h2 hF ?_
      (hfix2 _ hF)
    intro h0
    have := congrFun h0 (Sum.inl ⟨0, by omega⟩)
    simp at this

end SpResidual

theorem false_of_fixBarFull_sp_six {J : Subgroup (StatedSp 3 (ZMod 2))}
    {v : StatedSp 3 (ZMod 2)} (h : FixBarFull J 3 v) : False := by
  obtain ⟨I, v', hI, hI0, h'⟩ := SpResidual.exists_flagStabilizer_fixBarFull h
  obtain ⟨i, hi⟩ := hI0
  have hi' := hI i hi
  by_cases hio : Odd i
  · exact SpResidual.false_of_odd_or_two hI h' (Or.inl ⟨i, hi, hio⟩)
  · have hi2 : i = 2 := by
      rw [Nat.not_odd_iff_even] at hio
      obtain ⟨k, hk⟩ := hio
      omega
    subst hi2
    exact SpResidual.false_of_odd_or_two hI h' (Or.inr hi)

theorem false_of_fixBarFull_sp_eight {J : Subgroup (StatedSp 4 (ZMod 2))}
    {v : StatedSp 4 (ZMod 2)} (h : FixBarFull J 3 v) : False := by
  obtain ⟨I, v', hI, hI0, h'⟩ := SpResidual.exists_flagStabilizer_fixBarFull h
  by_cases hodd : ∃ i ∈ I, Odd i
  · exact SpResidual.false_of_odd_or_two hI h' (Or.inl hodd)
  · by_cases h2 : 2 ∈ I
    · exact SpResidual.false_of_odd_or_two hI h' (Or.inr h2)
    · push Not at hodd
      obtain ⟨i, hi⟩ := hI0
      have hI4 : I = {4} := by
        have key : ∀ j ∈ I, j = 4 := by
          intro j hj
          have h1 := hI j hj
          have h3 := hodd j hj
          have h4 : j ≠ 2 := fun h => h2 (h ▸ hj)
          rw [Nat.not_odd_iff_even] at h3
          obtain ⟨k, hk⟩ := h3
          omega
        ext j
        simp only [Set.mem_singleton_iff]
        constructor
        · exact key j
        · intro hj
          subst hj
          have := key i hi
          rw [← this]; exact hi
      subst hI4
      exact SpResidual.CycFour.false_of_cyc_lagrangian_four h'.base.cyc

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
