module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactG2
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactStmt

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

theorem exists_component_of_not_aEmpty (hD4 : D4NormalizerMax p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {K : Subgroup X} (hK : K ∈ Φ)
    (hnA : ¬ AEmpty Φ K) :
    ∃ (i : Fin D.card) (R S : Subgroup (D.model i).K) (J : Subgroup X) (zK zJ a : X),
      D.tag i = .G2 ∧ R ∈ D.cls i ∧ S ∈ D.cls i ∧ K = R.map (D.hom i) ∧ J = S.map (D.hom i) ∧
        AViol Φ K J zK zJ ∧ QuotViol Φ K J zK zJ a := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hnA
  obtain ⟨a, hQ⟩ := quotViol_of_aViol_self hp hq hΦ hK hv
  obtain ⟨i, R, S, hR, hS, hKR, hJS⟩ := hQ.exists_components D
  refine ⟨i, R, S, J, zK, zJ, a, ?_, hR, hS, hKR, hJS, hv, hQ⟩
  by_contra hi
  rw [hKR, hJS] at hQ
  by_cases hD : D.tag i = .trialityD4
  · exact hQ.false_of_trialityD4 hD4 hp hq hΦ D hD hR hS
  · exact hQ.false_of_classical hp hq hΦ D hi hD hR hS

theorem thm3Comm_of_violation (hgen : G2CentralizersGenerate p) (hD4 : D4NormalizerMax p)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ)
    {K : Subgroup X} (hK : K ∈ Φ) (hnA : ¬ AEmpty Φ K) :
    aStar Φ K = vStar Φ K ∧
      ∀ L ∈ Φ, L ∉ vStar Φ K → ∀ M ∈ vStar Φ K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M := by
  obtain ⟨i, R, S, J, zK, zJ, a, hG2, hR, hS, rfl, rfl, hv, hQ⟩ :=
    exists_component_of_not_aEmpty hD4 hp hq hΦ D hK hnA
  have hJ : S.map (D.hom i) ∈ aStar Φ (R.map (D.hom i)) :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  have hKc : R.map (D.hom i) ∈ compMembers D i := ⟨R, hR, rfl⟩
  have hA := aStar_eq_compMembers hgen hp hq hΦ D hG2 hR hQ hJ
  have hV := vStar_eq_compMembers hp D hq hΦ (Or.inl hG2) hKc
  refine ⟨hA.trans hV.symm, ?_⟩
  intro L hL hLv M hMv
  rw [hV] at hLv hMv
  have hc := commutes_of_not_mem_compMembers D hL hLv hMv
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc x hx y hy)]
  exact one_mem _

theorem thm3CommBelowExact_of_citBelowU (hgen : G2CentralizersGenerate p)
    (hD4 : D4NormalizerMax p) {n : ℕ} (hn : CITBelowU p f n) : Thm3CommBelowExact p f n := by
  intro hp hq G _ _ hlt hO Ω hΩ K hK hnA
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΩ.conjInvariant hΩ.classical ⟨K, hK⟩ hO hlt
  exact thm3Comm_of_violation hgen hD4 hp hq hΩ D hK hnA

end CFSG.ClassicalInvolution.Asc77.T3Typed
