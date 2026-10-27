module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerOrthAbs
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup

section Helpers

variable {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

private theorem mem_commutator_of_mem_orthDerived (R : QuadraticForm K W)
    {g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)}
    (hg : (g : W ≃ₗ[K] W) ∈ CFSG.RankThree.Classical2.orthDerived R) :
    g ∈ _root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  rw [CFSG.RankThree.Classical2.orthDerived, ← Subgroup.map_subtype_commutator] at hg
  obtain ⟨g', hg', hgg'⟩ := hg
  rwa [← Subtype.ext hgg']

private theorem oddPCoreInClosure_orthogonalGroup_of_derived (R : QuadraticForm K W) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : CFSG.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived R))
    (hcen : Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived R) = ⊥)
    (hsq : ∀ g : ↥(TauCeti.QuadraticMap.orthogonalGroup R),
      g ^ 2 ∈ _root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :
    OddPCoreInClosure p ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hodd : Odd (Nat.card (Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived R))) := by
    rw [hcen, Subgroup.card_bot]
    exact odd_one
  refine oddPCoreInClosure_of_sq_mem hp hp2
    (_root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) hsq ?_
  exact OddPCoreInClosure.of_mulEquiv (CFSG.RankThree.PartOne.orthDerivedEquivCommutator R).symm
    (oddPCoreInClosure_of_isQuasisimple hp hq hodd)

end Helpers

theorem oddPCoreInClosure_orthogonalGroup_of_threeSingular {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hT : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, R u = 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  have : Nontrivial W := by
    obtain ⟨U, hU, -⟩ := hT
    refine Module.nontrivial_of_finrank_pos (R := K) ?_
    have := Submodule.finrank_le U
    omega
  obtain ⟨-, -, -, -, -, hsq, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR hT
  refine oddPCoreInClosure_orthogonalGroup_of_derived R hp hp2
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (CFSG.RankThree.PartOne.center_orthDerived_eq_bot hR hT) fun g => ?_
  exact mem_commutator_of_mem_orthDerived R (by simpa using hsq _ g.2)

theorem oddPCoreInClosure_orthogonalGroup_nonsplit {K : Type} [Field K] [Finite K]
    [CharP K 2] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (hd : Module.finrank K W = 4 ∨ Module.finrank K W = 6)
    (hts : ∀ U : Submodule K W, Module.finrank K U = Module.finrank K W / 2 → ∃ u ∈ U, R u ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OddPCoreInClosure p ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  obtain ⟨hs, -, hna, hidx, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR hd hts
  have hq := (CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived R hR hd hts).1
  have hcen : Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived R) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
    · exact h
    · exfalso
      refine hna fun x y => ?_
      have hx : x ∈ Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived R) := by
        rw [h]
        exact Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm
  have hJ : (CFSG.RankThree.Classical2.orthDerived R).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup R) =
        _root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    ext g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · exact fun hg => mem_commutator_of_mem_orthDerived R hg
    · intro hg
      rw [CFSG.RankThree.Classical2.orthDerived, ← Subgroup.map_subtype_commutator]
      exact ⟨g, hg, rfl⟩
  have hidx' : (_root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)).index = 2 := by
    rw [← hJ]
    exact hidx
  refine oddPCoreInClosure_orthogonalGroup_of_derived R hp hp2 hq hcen fun g => ?_
  have := Subgroup.pow_index_mem (_root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) g
  rwa [hidx'] at this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
