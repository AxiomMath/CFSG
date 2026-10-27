module

public import CFSG.LieType.SeitzGeneration.SpHyperGen
public import CFSG.LieType.SeitzGeneration.HyperLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

@[expose] def SpReducible (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E₀ : Subgroup (Cat d)) :
    Prop :=
  ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
    (e : Cat d ≃* StatedProj (StatedSp r K)), (p : K) ≠ 0 ∧ 1 ≤ r ∧
    ∃ W : Submodule K (Fin r ⊕ Fin r → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) ∧
      ∀ g : StatedSp r K, proj r K g ∈ E₀.map e.toMonoidHom → ∀ w ∈ W, spEnd g w ∈ W

theorem seitzHyperLie_symplecticReducible : SeitzHyperLie fun d p E₀ => SpReducible d p E₀ := by
  intro d p hp hp2 hpd hlist E₀ hE hcard hred
  obtain ⟨r, K, _, _, e, hpK, hr, W, hW0, hWiso, hWstab⟩ := hred
  have hE' : IsElemAbelian p (E₀.map e.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hcard' : Nat.card (E₀.map e.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  exact hyperGen_top_of_mulEquiv e
    (hyperGen_top_of_isotropic hp hp2 hpK hr hE' hcard' hW0 hWiso hWstab)

end CFSG.LieType.SeitzGeneration
