module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Timmesfeld.Tables.Census


private theorem threeTwoWitness_lie (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group] (h2 : d.1.characteristic ≠ 2)
    (h3 : d.1.characteristic ≠ 3) : ThreeTwoWitness (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | A n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_A] at h2
    have hr : 1 ≤ n ∧ (n = 1 → 4 ≤ q.card) :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨-, hc | ⟨h0, -⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA n q hv
    swap
    · omega
    rcases Nat.lt_or_ge n 2 with hn | hn
    · obtain rfl : n = 1 := by omega
      obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hc
      have h1 : (-1 : K) ≠ 1 := neg_one_ne_one_of_card hp h2 hK
      refine (threeTwoWitness_psl_two_odd (Ring.two_ne_zero fun h => h1 ?_) ?_).of_mulEquiv
        e.symm
      · exact neg_one_eq_one_iff.2 h
      · rw [hK]
        exact Nat.odd_iff.1 ((hp.odd_of_ne_two h2).pow)
    · refine threeTwoWitness_of_psl hc ?_
      rcases Nat.lt_or_ge n 3 with h | h
      · exact Or.inr ⟨by omega, h2⟩
      · exact Or.inl (by omega)
  | twistedA n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedA] at h2
    have hr : 2 ≤ n ∧ (n = 2 → 3 ≤ q.card) :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    refine threeTwoWitness_of_psu
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv (MulEquiv.refl _)) ?_
    rcases Nat.lt_or_ge n 3 with h | h
    · exact Or.inr ⟨by omega, h2⟩
    · exact Or.inl (by omega)
  | B n q =>
    simp only [TauCeti.LieTypeIndex.characteristic_B] at h2
    have hr : 2 ≤ n ∧ ¬(n = 2 ∧ q.card = 2) :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      obtain ⟨-, K, _, _, -, ⟨e⟩⟩ :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _)
      exact (threeTwoWitness_psp le_rfl).of_mulEquiv e.symm
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd n q hv h2 h (MulEquiv.refl _)
      exact (threeTwoWitness_omega_odd h).of_mulEquiv e.symm
  | C n q =>
    have hr : 3 ≤ n ∧ q.p ≠ 2 :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC n q hv (MulEquiv.refl _)
    exact (threeTwoWitness_psp (by omega)).of_mulEquiv e.symm
  | D n q =>
    have hr : 4 ≤ n :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD n q hv (MulEquiv.refl _)
    exact (threeTwoWitness_omega_plus (by omega)).of_mulEquiv e.symm
  | twistedD n q =>
    have hr : 4 ≤ n :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    obtain ⟨-, K, _, _, -, b, c, -, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD n q hv (MulEquiv.refl _)
    exact (threeTwoWitness_omega_minus hr b c).of_mulEquiv e.symm
  | E6 q =>
    exact threeTwoWitness_of_untwistedBridge (c := TauCeti.LieTypeIndex.E6)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 (by decide) (MulEquiv.refl _)
  | E7 q =>
    exact threeTwoWitness_of_untwistedBridge (c := TauCeti.LieTypeIndex.E7)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 (by decide) (MulEquiv.refl _)
  | E8 q =>
    exact threeTwoWitness_of_untwistedBridge (c := TauCeti.LieTypeIndex.E8)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 (by decide) (MulEquiv.refl _)
  | F4 q =>
    exact threeTwoWitness_of_untwistedBridge (c := TauCeti.LieTypeIndex.F4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 (by decide) (MulEquiv.refl _)
  | G2 q =>
    exact threeTwoWitness_of_untwistedBridge (c := TauCeti.LieTypeIndex.G2)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 (by decide) (MulEquiv.refl _)
  | twistedE6 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_twistedE6] at h2
    exact threeTwoWitness_twistedE6_odd (MulEquiv.refl _) h2
  | trialityD4 q =>
    simp only [TauCeti.LieTypeIndex.characteristic_trialityD4] at h2
    exact threeTwoWitness_trialityD4 (MulEquiv.refl _) (Or.inl h2)
  | suzuki m => exact absurd (TauCeti.LieTypeIndex.characteristic_suzuki m) h2
  | reeG2 m => exact absurd (TauCeti.LieTypeIndex.characteristic_reeG2 m) h3
  | reeF4 m => exact absurd (TauCeti.LieTypeIndex.characteristic_reeF4 m) h2
  | tits => exact absurd TauCeti.LieTypeIndex.characteristic_tits h2

theorem genChevThreeLocal_holds : GenChevThreeLocal := by
  intro r _ hr2 hr3 L _ _ _ hL
  refine one_le_glaTwoLocalRank_of_witness ?_
  rcases hL with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      have hd : d.1.characteristic = r := hi
      have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv L e.toEquiv
      exact (threeTwoWitness_lie d (hd ▸ hr2) (hd ▸ hr3)).of_mulEquiv e.symm
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | alternating n hn =>
      simp only [ambiguousChev] at hi
      obtain rfl : n = 5 := by omega
      exact threeTwoWitness_alt_five.of_mulEquiv e.symm
    | lie d =>
      exfalso
      simp only [ambiguousChev] at hi
      split at hi <;> omega
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

end
