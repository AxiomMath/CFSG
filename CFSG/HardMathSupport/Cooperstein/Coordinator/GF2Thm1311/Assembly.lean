module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKleinFam
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.AltSix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFam
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFamD4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFamMinus4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.OrthFamPlus4
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.Assembly.LowTwoRank TauCeti CFSG.AGLEmbedding CFSG.Open

theorem noKlein_of_small {Y : Type} [Group Y] (d : ValidLieTypeIndex)
    (hd : (∃ q : PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q))
    (e : Y ≃* (CFSGIndex.lie d).Group) : NoKlein Y := by
  obtain ⟨d1, hv⟩ := d
  rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
  · simp only at hd1
    subst hd1
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    have hq' : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def]; exact hq
    obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
    rw [hp7, he1] at h
    exact noKlein_PSL_two_seven h
  · simp only at hd1
    subst hd1
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hq' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact hq
    obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
    rw [hp3, he1] at h
    exact noKlein_PSU_three_three h

theorem kleinBigInv_of_isClassicalTwoOrG2_of_G2 {Y : Type} [Group Y]
    (hG2 : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      (Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) → NoKlein Y)
    (h : IsClassicalTwoOrG2 Y) : KleinBigInv Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · rcases CFSG.AGLEmbedding.ParabAutIrr.classical_model_or_g2 d hd e with
      ⟨t, n, f, ht, hm⟩ | ⟨q, hq, hq2, hdq⟩
    · have hadm := hm.1
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · obtain ⟨-, -, hn2, -⟩ := hadm
        rcases Nat.lt_or_ge n 3 with h3 | h3
        · have : n = 2 := by omega
          subst this
          exact KleinBigInv.of_noKlein (noKlein_PSL_two hm)
        · exact kleinBigInv_PSL_ge_three_all h3 hm
      · exact KleinBigInv.of_noKlein (noKlein_PSU hm)
      · obtain ⟨-, -, hn2, -⟩ := hadm
        rcases Nat.lt_or_ge n 3 with h3 | h3
        · have : n = 2 := by omega
          subst this
          exact KleinBigInv.of_noKlein (noKlein_PSp_two hm)
        · exact KleinBigInv.of_noKlein (noKlein_PSp_ge_three h3 hm)
      · obtain ⟨-, -, hn4⟩ := hadm
        rcases Nat.lt_or_ge n 5 with h5 | h5
        · have : n = 4 := by omega
          subst this
          by_cases hf : f = 2
          · subst hf
            exact kleinBigInv_POmegaPlus_four_q4 hm
          · exact kleinBigInv_POmegaPlus_four hf hm
        · by_cases hf : f = 2
          · subst hf
            exact kleinBigInv_POmegaPlus_ge_five_q4 h5 hm
          · exact kleinBigInv_POmegaPlus_ge_five h5 (Or.inl hf) hm
      · obtain ⟨-, -, hn4⟩ := hadm
        by_cases hf : f = 2
        · subst hf
          exact kleinBigInv_POmegaMinus_four hm
        · exact kleinBigInv_POmegaMinus (Or.inl hf) hm
    · subst hdq
      exact KleinBigInv.of_noKlein (hG2 q hq hq2 e)
  · have h5 : n = 5 ∨ n = 6 ∨ n = 8 := hn
    rcases h5 with rfl | rfl | rfl
    · exact KleinBigInv.of_noKlein (NoKlein.of_mulEquiv e.symm (noKlein_alternatingGroup (Or.inl rfl)))
    · exact KleinBigInv.of_noKlein (NoKlein.of_mulEquiv e.symm noKlein_alternatingGroup_six)
    · exact KleinBigInv.of_noKlein (NoKlein.of_mulEquiv e.symm (noKlein_alternatingGroup (Or.inr (by norm_num))))
  · exact KleinBigInv.of_noKlein (noKlein_of_small d hd e)

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
