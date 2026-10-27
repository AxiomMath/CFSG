module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import all CFSG.LocalAnalysis.GLTheoremA.CatA.S2019OrthOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem s2019FixCentralizes_omega_plus_of_mem_E {G : Type} [Group G] {n q f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n q f) (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = q ^ f)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) (β : MulAut G) (hβ : β ^ p = 1)
    (hnot : ∀ a : G, β ≠ MulAut.conj a)
    (hβE : MulAut.congr (coordinatePlusWitnessEquiv K e) β ∈
      matrixProjectiveImage (coordinateQuadPlus n K)) :
    S2019FixCentralizes p β := by
  obtain ⟨hq, -, hn4⟩ := hG.1
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n q f hG K hK e
  have h2 := two_ne_zero_of_card_eq_pow hq hq2 hK
  set e' := coordinatePlusWitnessEquiv K e
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) := Finite.of_equiv _ e'.toEquiv
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hD := not_mem_D_of_not_inner hgates hp hp2 e' β hβ hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  refine s2019FixCentralizes_of_congr hp e' β ?_
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n q f p hG hp hp2 K hK e _ hβE hD hord
  obtain ⟨g, hgE⟩ := hβE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord1, -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord1
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  exact s2019FixCentralizes_of_fieldDescent
    (subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord' (by omega : 3 ≤ n))
    h2 (by omega) U Θ g' hg'l hg'r hΘ

end CFSG.LocalAnalysis.GLTheoremA.S2019
