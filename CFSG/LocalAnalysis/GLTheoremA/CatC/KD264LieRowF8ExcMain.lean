module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ExcConj
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ClsOm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer


theorem exc_contra (τ : Tag) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ 3) {S : Type} [Group S] [Finite S] (e : S ≃* adjointGroup τ K)
    (A : Subgroup (MulAut S)) (hA : KD264F8Hyp S A) : False := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : Finite ↥(adjointGroup τ K) := Finite.of_equiv S e.toEquiv
  obtain ⟨hAab', hout', hnot'⟩ := F8Trans.hyp_transport e A hA
  have h4 : CFSG.Open.pRank 3 A ≤ 4 := hA.2.2.1
  have h3 := pRank_map_mulEquiv (p := 3) (MulAut.congr e) A
  obtain ⟨b, hbA, hbout⟩ := SetLike.not_le_iff_exists.1 hnot'
  have hb3 : b ^ 3 = 1 := hAab'.2 b hbA
  obtain ⟨E, hEfix, hEab, hEcard⟩ := F8Exc.exists_fixed_rank_four_of_outer τ hτ hK hb3 hbout
  have hbnin : b ∉ (MulAut.conj : ↥(adjointGroup τ K) →*
      MulAut ↥(adjointGroup τ K)).range := fun h => hbout (inner_le_innAutDerived _ h)
  have h1 := hout' b hbA hbnin E hEfix hEab
  have h2 := F8Om.four_le_pRank_of_card hEab hEcard
  omega

theorem KD264F8ClsExc_holds : KD264F8ClsExc := by
  intro d _hfin _hns _hk2 _hk3 hov hP _ _ _ A hA
  exfalso
  obtain ⟨d1, hd1⟩ := d
  rcases hP with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : q.card = 8 := hov
    obtain ⟨K, _, _, hKcard, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hd1
    exact exc_contra Tag.E6 (Or.inr (Or.inl rfl)) (by rw [hKcard, hq]; norm_num) eK A hA
  · have hq : q.card = 8 := hov
    obtain ⟨K, _, _, hKcard, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hd1
    exact exc_contra Tag.E7 (Or.inr (Or.inr (Or.inl rfl))) (by rw [hKcard, hq]; norm_num) eK A hA
  · have hq : q.card = 8 := hov
    obtain ⟨K, _, _, hKcard, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hd1
    exact exc_contra Tag.E8 (Or.inr (Or.inr (Or.inr rfl))) (by rw [hKcard, hq]; norm_num) eK A hA
  · have hq : q.card = 8 := hov
    obtain ⟨K, _, _, hKcard, -, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hd1
    exact exc_contra Tag.F4 (Or.inl rfl) (by rw [hKcard, hq]; norm_num) eK A hA

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
