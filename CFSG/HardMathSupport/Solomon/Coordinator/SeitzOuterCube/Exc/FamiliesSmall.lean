module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FamiliesUntw
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneRee
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneSmall
public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEight
public import CFSG.LieType.SeitzGeneration.ExcWideThree.G2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

theorem eq_two_three_of_card_eight {q : PrimePower} (h : q.card = 8) :
    q.p = 2 ∧ q.exponent = 3 := by
  have h8 : q.p ^ q.exponent = 2 ^ 3 := by rw [← PrimePower.card_def, h]; norm_num
  have hdvd : q.p ∣ 2 ^ 3 := h8 ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hp2 : q.p = 2 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  rw [hp2] at h8
  exact ⟨hp2, Nat.pow_right_injective (le_refl 2) h8⟩

theorem p1ThreeLieList_G2_eight {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid)
    (h : q.card = 8) : P1ThreeLieList 3 ⟨.G2 q, hv⟩ := by
  obtain ⟨h2, h3⟩ := eq_two_three_of_card_eight h
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, h2, h3, Or.inr (Or.inl rfl)⟩)))))

section G2Pair


theorem excOuterPair_G2 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.G2 q).Valid) (p : ℕ) [Fact p.Prime] : ExcOuterPair ⟨.G2 q, hv⟩ p := by
  intro hp2 hpd hl hno
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (PrimePower.card_def q)
  have hq3 : 3 ≤ q.card := (LieTypeIndex.inStandardRange_iff _).1
    ((LieTypeIndex.valid_iff _).1 hv).1
  have hfin : Finite (Cat ⟨.G2 q, hv⟩) :=
    have : Finite ↥(adjointGroup Tag.G2 K) := generated_group_finite .G2 K
    Finite.of_equiv _ e.symm.toEquiv
  have hrk : RankLE2 p (Cat ⟨.G2 q, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_G2 q).symm)
  have h8 : ¬ (p = 3 ∧ q.card = 8) := fun ⟨hp3, hc⟩ => by
    subst hp3
    exact hl (p1ThreeLieList_G2_eight hv hc)
  have hfa : FieldAutData (adjointGroup Tag.G2 K) p := by
    by_cases h2 : q.p = 2
    · have hf : 2 ≤ q.exponent := by
        by_contra hlt
        have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
        rw [PrimePower.card_def, h1, h2] at hq3
        omega
      have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK', h2]
      by_cases hp3 : p = 3
      · subst hp3
        exact CFSG.RankThree.PartTwo.Sec19.fieldAutData_G2_three
          CFSG.RankThree.PartTwo.Sec19.subfieldPairG2EvenThree_holds hf
          hK2
      · exact SEITZ2.fieldAutData_G2 (SEITZ2.subfieldPairG2_of_f2 SEITZ2.subfieldPairG2F2) hp
          (five_le_of_prime_ne_two_three hp hp2 hp3) hf hK2
    · by_cases h3 : q.p = 3
      · exact CFSG.HardMathSupport.Seitz.G2Noninner.fieldAutData_G2_three
          CFSG.HardMathSupport.Seitz.G2Noninner.subfieldPairG2Odd q.exponent_pos
          (by rw [hK', h3]) hp (five_le_of_prime_ne_two_three hp hp2 (by rw [h3] at hpq; exact hpq))
      · exact ExcWideThree.fieldAutData_G2_odd_ne_three_ge3 q.prime_p h2 h3 q.exponent_pos hK' hp
          (ExcWideThree.subfieldPairG2AtGe3 (by rw [ringChar.eq K q.p]; exact h2))
          (by have := hp.two_le; omega)
  exact ⟨hfa.of_mulEquiv e hp,
    (fixPlaneGen_G2 hLow hq3 hK hp hp2 hpq h8 (RankLE2.of_mulEquiv e hrk)).of_mulEquiv e hp⟩

end G2Pair

section ReePair


theorem excOuterPair_reeF4 (hLow : ExcInnerLowPlanes) {m : ℕ}
    (hv : (LieTypeIndex.reeF4 m).Valid) (p : ℕ) [Fact p.Prime] : ExcOuterPair ⟨.reeF4 m, hv⟩ p := by
  intro hp2 hpd hl hno
  have hp : p.Prime := Fact.out
  obtain ⟨X, _, _, _, hm1, hX, hsimple, ⟨e⟩⟩ := exists_reeGamma_equiv_cat hv
  have hfin : Finite (Cat ⟨.reeF4 m, hv⟩) := (finite_isSimpleGroup_cat_reeF4 hv).1
  have hrk : RankLE2 p (Cat ⟨.reeF4 m, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  by_cases hp3 : p = 3
  · subst hp3
    refine ⟨(CFSG.RankThree.PartTwo.Sec4.E27.fieldAutData_reeF4_three hm1 hX).of_mulEquiv e hp, ?_⟩
    by_cases hm : m = 1
    · subst hm
      exact (CFSG.RankThree.PartTwo.Sec4.E27.reeF4EightFixPlaneGen_of_certs X hX).of_mulEquiv e hp
    · exact (CFSG.RankThree.PartTwo.Sec4.E27.fixPlaneGen_reeF4_three (by omega) hX).of_mulEquiv
        e hp
  · have hp5 := five_le_of_prime_ne_two_three hp hp2 hp3
    have hexc : ¬ (p = 5 ∧ m = 2) := fun ⟨h5, h2⟩ => by
      subst h5
      subst h2
      exact hl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))
    exact ⟨(SEITZ2.fieldAutData_reeF4 CFSG.RankThree.PartOne.SEITZRF.subfieldPairReeF4_holds hp hp5
        hm1 hX).of_mulEquiv e hp,
      (fixPlaneGen_reeF4_odd hLow hm1 hX hp hp5 hexc (RankLE2.of_mulEquiv e hrk)).of_mulEquiv
        e hp⟩

end ReePair

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
