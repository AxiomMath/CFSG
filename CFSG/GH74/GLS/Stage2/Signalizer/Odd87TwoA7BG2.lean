module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BDefs
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8AllInvolutionComponents
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.Blueprint CFSG.ComponentClassification CFSG.LieType.Chevalley

section


theorem bTwo_g2 {X : Type} [Group X] [Finite X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .G2 n p f)
    (hm : CFSG.Blueprint.LieModel X .G2 n p f) (hZ : Subgroup.center X = ⊥) {z : X}
    (hz : orderOf z = 2) : BTwo X z := by
  obtain ⟨-, -, rfl, -⟩ := hadm
  have hmod : UntwistedChevalleyModel X .G2 (p ^ f) := by
    rcases hm with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact h.2
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmod
  have hKodd : Odd (Nat.card K) := hK ▸ (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hsq : (MulAut.conj z : MulAut X) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (MulAut.conj z : MulAut X)
    rwa [orderOf_conj_eq_two hZ hz] at h1
  intro S hS
  refine OddToralFixed.pComponent_quasisimple_of_mulEquiv
    (CatalogueRelativeB.fixedSubgroupEquivalence e (MulAut.conj z)) ?_ S hS
  intro L hL
  exact CFSG.LieType.AlgebraicGroups.odd_G2_F4_E8_all_involution_fixed_p_components .G2
    (Or.inl rfl) K hKodd (MulAut.congr e (MulAut.conj z)) (by rw [← map_pow, hsq, map_one]) 2
    Nat.prime_two L hL

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
