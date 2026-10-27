module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BDefs
public import CFSG.LieType.Chevalley.OddTrialityAllInvolutionComponents
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.Blueprint CFSG.ComponentClassification CFSG.LieType.Chevalley

section


theorem bTwo_d4 {X : Type} [Group X] [Finite X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .trialityD4 n p f)
    (hm : CFSG.Blueprint.LieModel X .trialityD4 n p f) (hZ : Subgroup.center X = ⊥) {z : X}
    (hz : orderOf z = 2) : BTwo X z := by
  obtain ⟨-, hf, rfl⟩ := hadm
  have hmod : TwistedChevalleyModel X .D4 (p ^ f) := by
    rcases hm with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact h.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hmod
  have hsq : (MulAut.conj z : MulAut X) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (MulAut.conj z : MulAut X)
    rwa [orderOf_conj_eq_two hZ hz] at h1
  intro S hS
  refine OddToralFixed.pComponent_quasisimple_of_mulEquiv
    (CatalogueRelativeB.fixedSubgroupEquivalence e (MulAut.conj z)) ?_ S hS
  intro L hL
  exact odd_triality_all_involution_fixed_p_components hp hp2 hf K hK σ hσ
    (MulAut.congr e (MulAut.conj z)) (by rw [← map_pow, hsq, map_one]) 2 Nat.prime_two L hL

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
