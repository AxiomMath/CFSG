module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBInvolution
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBAlmostSimple

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.ComponentClassification CFSG.Assembly.LowTwoRank

theorem bTwo_psp {X : Type} [Group X] [Finite X] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp n p f)
    (hm : CFSG.Blueprint.LieModel X .PSp n p f) (hZ : Subgroup.center X = ⊥) {z : X}
    (hz : orderOf z = 2) : BTwo X z := by
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* StatedProj (StatedSp n K)) := by
    rcases hm with ⟨-, h⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩ | ⟨hn0, -⟩
    · obtain ⟨-, K, _, _, hK, e⟩ := h
      exact ⟨K, inferInstance, inferInstance, hK, e⟩
    all_goals omega
  have hα : orderOf (MulAut.congr e (MulAut.conj z)) = 2 :=
    (MulEquiv.orderOf_eq (MulAut.congr e) _).trans (orderOf_conj_eq_two hZ hz)
  have hα2 : MulAut.congr e (MulAut.conj z) * MulAut.congr e (MulAut.conj z) = 1 := by
    rw [← pow_two, ← hα]
    exact pow_orderOf_eq_one _
  have hα1 : MulAut.congr e (MulAut.conj z) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα
    omega
  intro S hS
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv 2
    (CatalogueRelativeB.fixedSubgroupEquivalence e (MulAut.conj z))
    (fun L hL => CatalogueBSymplecticB.odd_symplectic_involution_fixed_p_components p f hp hp2
      hadm.2.1 K hK n hn _ hα2 hα1 2 Nat.prime_two L hL) S hS

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
