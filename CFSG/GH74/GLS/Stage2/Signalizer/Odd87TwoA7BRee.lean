module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87ReeCent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.Blueprint CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

section


theorem bTwo_ree {X : Type} [Group X] [Finite X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .twistedG2 n p f)
    (hm : CFSG.Blueprint.LieModel X .twistedG2 n p f) (hZ : Subgroup.center X = ⊥) {z : X}
    (hz : orderOf z = 2) : BTwo X z := by
  obtain ⟨-, -, -, hp3, -, -⟩ := hadm
  subst hp3
  have hR : ReeTitsModel X .twistedG2 3 f := by
    rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ := ree_model_data_pos hR
  have hα : orderOf (MulAut.congr e (MulAut.conj z)) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
      (MulAut.conj z)).trans (orderOf_conj_eq_two hZ hz)
  intro S hS
  let Ψ := CatalogueRelativeB.fixedSubgroupEquivalence e (MulAut.conj z)
  exact (isQuasisimple_congr (S.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)).2
    (CatalogueBSmallRee.small_Ree_involution_fixed_p_components a ha K hK _ hα 2 Nat.prime_two _
      (isPComponent_map_of_isPComponent 2 Ψ hS))

end

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
