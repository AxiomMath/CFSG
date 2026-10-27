module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2GenToral
public import CFSG.ClassicalInvolution.RouteD.G2D4T3D4

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Comm

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

theorem exists_component_of_not_aEmpty_free (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
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
  · exact quotViol_false_of_trialityD4 hp hq hΦ D hD hR hS hQ
  · exact hQ.false_of_classical hp hq hΦ D hi hD hR hS

theorem thm3Comm_of_violation_free (hgen : G2CentralizersGenerate p)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ)
    {K : Subgroup X} (hK : K ∈ Φ) (hnA : ¬ AEmpty Φ K) :
    aStar Φ K = vStar Φ K ∧
      ∀ L ∈ Φ, L ∉ vStar Φ K → ∀ M ∈ vStar Φ K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M := by
  obtain ⟨i, R, S, J, zK, zJ, a, hG2, hR, hS, rfl, rfl, hv, hQ⟩ :=
    exists_component_of_not_aEmpty_free hp hq hΦ D hK hnA
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

theorem thm3CommBelowExact_of_citBelowU_free (hgen : G2CentralizersGenerate p) {n : ℕ}
    (hn : CITBelowU p f n) : Thm3CommBelowExact p f n := by
  intro hp hq G _ _ hlt hO Ω hΩ K hK hnA
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΩ.conjInvariant hΩ.classical ⟨K, hK⟩ hO hlt
  exact thm3Comm_of_violation_free hgen hp hq hΩ D hK hnA

end Comm

section Lie

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

theorem thm3Lie_of_violation_free (hgen : G2CentralizersGenerate p)
    (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ)
    {K : Subgroup X} (hK : K ∈ Φ) (hnA : ¬ AEmpty Φ K) :
    SectionLieType p f Φ (omegaGen (aStar Φ K)) .G2 0 := by
  obtain ⟨i, R, S, J, zK, zJ, a, hG2, hR, hS, rfl, rfl, hv, hQ⟩ :=
    exists_component_of_not_aEmpty_free hp hq hΦ D hK hnA
  have hJ : S.map (D.hom i) ∈ aStar Φ (R.map (D.hom i)) :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  exact sectionLieType_of_violation hp hq hΦ D hgen hG2 hR hQ hJ

theorem thm3LieBelowExact_of_citBelowU_free (hgen : G2CentralizersGenerate p) {n : ℕ}
    (hn : CITBelowU p f n) : Thm3LieBelowExact p f n := by
  intro hp hq G _ _ hlt hO Ω hΩ K hK hnA
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΩ.conjInvariant hΩ.classical ⟨K, hK⟩ hO hlt
  exact thm3Lie_of_violation_free hgen hp hq hΩ D hK hnA

end Lie

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem thm3TypedBelowExact_of_citBelowU_free (hgen : G2CentralizersGenerate p) {n : ℕ}
    (hn : CITBelowU p f n) : Thm3TypedBelowExact p f n :=
  ⟨thm3CommBelowExact_of_citBelowU_free hgen hn, thm3LieBelowExact_of_citBelowU_free hgen hn⟩

theorem ih8Thm3Exact_free (hgen : G2CentralizersGenerate p) :
    ∀ n, CITBelowU p f n → Thm3TypedBelowExact p f n :=
  fun _ hn => thm3TypedBelowExact_of_citBelowU_free hgen hn

theorem dstarConnected_of_split_free {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    {z j a : X} (hgen : G2CentralizersGenerate p) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ) {K J : Subgroup X}
    (h : QuotViol Φ K J z j a) : DStarConnected Φ := by
  obtain ⟨i, R, S, hR, hS, rfl, rfl⟩ := h.exists_components D
  have hG2 : D.tag i = .G2 := by
    by_contra hne
    by_cases hD : D.tag i = .trialityD4
    · exact quotViol_false_of_trialityD4 hp hq hΦ D hD hR hS h
    · exact h.false_of_classical hp hq hΦ D hne hD hR hS
  refine dstarConnected_of_pivot h.mem_left fun M hMΦ => ?_
  obtain ⟨i', R', hR'f, hMR'⟩ := D.fundamental M hMΦ
  by_cases hii : i' = i
  · subst hii
    have hR'cls : R' ∈ D.cls i' := ⟨hR'f, hMR' ▸ hMΦ⟩
    rw [hMR']
    exact h.mem_dstarComp_of_g2 hgen hp hq hΦ D hG2 hR hR'cls
  · refine mem_dstarComp_of_commutes hp hΦ hMΦ ?_
    rw [hMR']
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact D.commute i' i hii x y

theorem thm3SectBelow_of_split_free (hgen : G2CentralizersGenerate p) {n : ℕ}
    (hn : CITBelowU p f n) : Thm3SectBelow p f n := by
  intro hp hq Y _ _ hY Λ hΛ hdis L hL
  by_contra hnA
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hnA
  obtain ⟨a, hQ⟩ := quotViol_of_aViol hp hq hΛ hL hv
  have hΛb : HypOmegaMod p f (oddQuotientFamily Λ) :=
    oddQuotHyp p f hp hq Y Λ hΛ (classicalInvolutionOddCore Y)
      (CFSG.ComponentClassification.OddCore.odd_card Y)
  have hO : classicalInvolutionOddCore (Y ⧸ classicalInvolutionOddCore Y) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hlt : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hY
  obtain ⟨D⟩ := ih8_exists_omegaLie hn hΛb.conjInvariant hΛb.classical
    ⟨_, mem_oddQuotientFamily hL⟩ hO hlt
  exact hdis (dstarConnected_of_split_free hgen hp hq hΛb D hQ)

theorem h3s_free (hgen : G2CentralizersGenerate p) :
    ∀ n, CITBelowU p f n → Thm3SectBelow p f n :=
  fun _ hn => thm3SectBelow_of_split_free hgen hn

theorem ih8Thm3Exact_of_nonToral_free (hNT : G2NonToralGenerate p) :
    ∀ n, CITBelowU p f n → Thm3TypedBelowExact p f n :=
  ih8Thm3Exact_free (G2CentralizersGenerate.of_nonToral hNT)

theorem h3s_of_nonToral_free (hNT : G2NonToralGenerate p) :
    ∀ n, CITBelowU p f n → Thm3SectBelow p f n :=
  h3s_free (G2CentralizersGenerate.of_nonToral hNT)

end Main

end CFSG.ClassicalInvolution.G2D4Models
