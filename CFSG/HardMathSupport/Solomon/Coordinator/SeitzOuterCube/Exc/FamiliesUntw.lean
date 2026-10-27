module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneUntw
public import CFSG.LieType.SeitzGeneration.ExcSeitzWide

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.TauCetiBridge TauCeti

@[expose] def ExcOuterPair (d : ValidLieTypeIndex) (p : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → p ≠ d.1.characteristic → ¬ P1ThreeLieList p d →
    (¬ ∃ E : Subgroup (CFSG.LieType.SeitzGeneration.Cat d), IsElemAbelian p E ∧
      Nat.card E = p ^ 3) →
    FieldAutData (CFSG.LieType.SeitzGeneration.Cat d) p ∧
      FixPlaneGen (CFSG.LieType.SeitzGeneration.Cat d) p

section Untwisted


theorem excOuterPair_F4 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.F4 q).Valid) (p : ℕ) [Fact p.Prime] : ExcOuterPair ⟨.F4 q, hv⟩ p := by
  intro hp2 hpd _ hno
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hfin : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.F4 q, hv⟩) :=
    have : Finite ↥(adjointGroup Tag.F4 K) := generated_group_finite .F4 K
    Finite.of_equiv _ e.symm.toEquiv
  have hrk : RankLE2 p (CFSG.LieType.SeitzGeneration.Cat ⟨.F4 q, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_F4 q).symm)
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  by_cases hp3 : p = 3
  · subst hp3
    exact (not_rankLE2_cat_F4_three q hv hpq hrk).elim
  · exact ⟨(ExcOuterLeOne.fieldAutData_F4_of_odd hp hp2 hpK).of_mulEquiv e hp,
      (fixPlaneGen_F4 hLow hK hp hp2 hpq (RankLE2.of_mulEquiv e hrk)).of_mulEquiv e hp⟩

theorem excOuterPair_E6 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.E6 q).Valid) (p : ℕ) [Fact p.Prime] : ExcOuterPair ⟨.E6 q, hv⟩ p := by
  intro hp2 hpd _ hno
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hfin : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.E6 q, hv⟩) :=
    have : Finite ↥(adjointGroup Tag.E6 K) := generated_group_finite .E6 K
    Finite.of_equiv _ e.symm.toEquiv
  have hrk : RankLE2 p (CFSG.LieType.SeitzGeneration.Cat ⟨.E6 q, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E6 q).symm)
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  by_cases hp3 : p = 3
  · subst hp3
    exact (not_rankLE2_cat_E6_three q hv hpq hrk).elim
  · have hp5 := five_le_of_prime_ne_two_three hp hp2 hp3
    exact ⟨(fieldAutData_E6_of_subfieldMaximalAll ExcOuterLeOne.subfieldMaximalAll_E6 hp hp5
        hpK).of_mulEquiv e hp,
      (fixPlaneGen_E6 hLow hK hp (by omega) hpq (RankLE2.of_mulEquiv e hrk)).of_mulEquiv e hp⟩

theorem excOuterPair_E7 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.E7 q).Valid) (p : ℕ) [Fact p.Prime] : ExcOuterPair ⟨.E7 q, hv⟩ p := by
  intro hp2 hpd _ hno
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hfin : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.E7 q, hv⟩) :=
    have : Finite ↥(adjointGroup Tag.E7 K) := generated_group_finite .E7 K
    Finite.of_equiv _ e.symm.toEquiv
  have hrk : RankLE2 p (CFSG.LieType.SeitzGeneration.Cat ⟨.E7 q, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E7 q).symm)
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  by_cases hp3 : p = 3
  · subst hp3
    exact (not_rankLE2_cat_E7_three q hv hpq hrk).elim
  · have hp5 := five_le_of_prime_ne_two_three hp hp2 hp3
    exact ⟨(ExcOuterLeOne.fieldAutData_E7_of_odd hp hp2 hpK).of_mulEquiv e hp,
      (fixPlaneGen_E7 hLow hK hp (by omega) hpq (RankLE2.of_mulEquiv e hrk)).of_mulEquiv e hp⟩

theorem excOuterPair_E8 (hLow : ExcInnerLowPlanes) {q : PrimePower}
    (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ) [Fact p.Prime] : ExcOuterPair ⟨.E8 q, hv⟩ p := by
  intro hp2 hpd _ hno
  have hp : p.Prime := Fact.out
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hfin : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.E8 q, hv⟩) :=
    have : Finite ↥(adjointGroup Tag.E8 K) := generated_group_finite .E8 K
    Finite.of_equiv _ e.symm.toEquiv
  have hrk : RankLE2 p (CFSG.LieType.SeitzGeneration.Cat ⟨.E8 q, hv⟩) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.rankLE2_of_not_exists_cube hp hno
  have hpq : p ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E8 q).symm)
  have hpK : p ≠ ringChar K := by rw [ringChar.eq K q.p]; exact hpq
  by_cases hp3 : p = 3
  · subst hp3
    exact (not_rankLE2_cat_E8_three q hv hpq hrk).elim
  · have hp5 := five_le_of_prime_ne_two_three hp hp2 hp3
    exact ⟨(ExcOuterLeOne.fieldAutData_E8_of_odd hp hp2 hpK).of_mulEquiv e hp,
      (fixPlaneGen_E8 hLow hK hp (by omega) hpq (RankLE2.of_mulEquiv e hrk)).of_mulEquiv e hp⟩

end Untwisted

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
