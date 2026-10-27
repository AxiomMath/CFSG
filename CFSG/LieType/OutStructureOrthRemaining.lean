module

public import CFSG.LieType.OutStructureOrthNorm
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SOrthMinus
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Orth
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutTowerThreeRankTwo

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.AGLEmbedding
open CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
open CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

theorem center_eq_bot_of_simple_nonneab {K : Type} [Group K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

theorem exists_fieldPart_of_outPChain_outLift_tower {K : Type} [Group K] [Finite K]
    [IsSimpleGroup K] (hnab : ∃ a b : K, a * b ≠ b * a) {p : ℕ} (hp : p.Prime)
    (hChain : OutPChain p K) (hLift : OutLift p K) (hTower : OutTowerAt K p) :
    ∃ F : Subgroup (MulAut K),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner K = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).index ∧
      ∀ x : MulAut K, (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact exists_fieldPart_of_outPChain_outLift hp hChain hLift
    (sylow_normal_outer_of_outTowerAt (center_eq_bot_of_simple_nonneab hnab) hTower)

theorem two_le_pRank_three_classical_POmegaMinus_charTwo {S : Type} [Group S] [Finite S]
    {n f : ℕ} (h : StatedClassicalModel S .POmegaMinus n 2 f) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, -, ⟨e⟩⟩ := h
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card, hK])
  have h3 := CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (K := K) hn b c
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  omega

theorem i713ClauseFor_lie_B_odd (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p ≠ 2) (hr3 : 3 ≤ r) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : IsSimpleGroup K := hK
  have hSC : StatedClassicalModel K .POmegaOdd r q.p q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr3 eK
  have hChain : OutPChain p K := (outPNice_POmegaOdd_all hp hp2 hSC).toChain
  have hLift : OutLift p K :=
    (liftClause_classical_POmegaOdd (n := r) (p := q.p) (f := q.exponent)) K hnab hSC p hp hp2 hpRank
  have hTower : OutTowerAt K p := outTowerAt_of_statedOdd_all hSC
  exact Or.inr (Or.inl (exists_fieldPart_of_outPChain_outLift_tower hnab hp hChain hLift hTower))

theorem i713ClauseFor_lie_D (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : IsSimpleGroup K := hK
  have hr4 : 4 ≤ r :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hSC : StatedClassicalModel K .POmegaPlus r q.p q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv eK
  by_cases hp3 : p = 3
  · subst hp3
    have h3 := GL83.I713.two_le_pRank_three_classical_POmegaPlus hSC
    omega
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    have h4 : p = 4 := by omega
    subst h4
    exact absurd hp (by norm_num)
  have hChain : OutPChain p K := by
    rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
    · exact outPChain_POmegaPlus_four_gen hp hp5 hSC
    · exact (outPNice_POmegaPlus_all_ge_five hp hp2 hr5 hSC).toChain
  have hLift : OutLift p K :=
    (liftClause_classical_POmegaPlus (n := r) (p := q.p) (f := q.exponent)) K hnab hSC p hp hp2 hpRank
  have hTower : OutTowerAt K p := outTowerAt_of_statedPlus hSC hp hp5
  exact Or.inr (Or.inl (exists_fieldPart_of_outPChain_outLift_tower hnab hp hChain hLift hTower))

theorem i713ClauseFor_lie_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩) := by
  intro K _ _ hK hnab ⟨eK⟩ p hp hp2 hpRank
  haveI : IsSimpleGroup K := hK
  have hSC : StatedClassicalModel K .POmegaMinus r q.p q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv eK
  have hChain : OutPChain p K := (outPNice_POmegaMinus_all hp hp2 hSC).toChain
  have hLift : OutLift p K :=
    (liftClause_classical_POmegaMinus (n := r) (p := q.p) (f := q.exponent)) K hnab hSC p hp hp2 hpRank
  have hTower : OutTowerAt K p := by
    by_cases hp3 : p = 3
    · subst hp3
      by_cases hq2 : q.p = 2
      · have hSC2 : StatedClassicalModel K .POmegaMinus r 2 q.exponent := by
          simpa [hq2] using hSC
        have h3 := two_le_pRank_three_classical_POmegaMinus_charTwo hSC2
        omega
      · have hqodd : q.p ≠ 2 := hq2
        exact outTowerAt_of_statedMinus_odd_three hqodd hSC
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        by_contra h
        have h4 : p = 4 := by omega
        subst h4
        exact absurd hp (by norm_num)
      exact outTowerAt_of_statedMinus hSC hp hp5
  exact Or.inr (Or.inl (exists_fieldPart_of_outPChain_outLift_tower hnab hp hChain hLift hTower))

end CFSG.LieType.OutStructure
