module

public import CFSG.ClassicalInvolution.Asc77.AscR10Mod
public import CFSG.ClassicalInvolution.RouteD.G2D4T3D4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.R10

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.G2D4Models
  CFSG.Assembly.LowTwoRank

variable {Y : Type} [Group Y] [Finite Y] {p f n : ℕ} [Fact p.Prime]


theorem exists_g2_component (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hIH : CITBelowU p f n)
    (hlt : Nat.card Y < n) {Λ : Set (Subgroup Y)} (hΛ : HypOmegaMod p f Λ)
    {K J : Subgroup Y} {zK zJ : Y} (hK : K ∈ Λ) (hv : AViol Λ K J zK zJ) :
    ∃ (D : OmegaLie p f (oddQuotientFamily Λ)) (i : Fin D.card)
      (R : Subgroup (D.model i).K), D.tag i = .G2 ∧ R ∈ D.cls i ∧
        K.map (oddQuot Y) = R.map (D.hom i) := by
  obtain ⟨a, hQ⟩ := quotViol_of_aViol hp2 hq hΛ hK hv
  have hΦ : HypOmegaMod p f (oddQuotientFamily Λ) :=
    oddQuotHyp p f hp2 hq Y Λ hΛ (classicalInvolutionOddCore Y)
      (CFSG.ComponentClassification.OddCore.odd_card Y)
  have hO : classicalInvolutionOddCore (Y ⧸ classicalInvolutionOddCore Y) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hlt' : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hlt
  obtain ⟨D⟩ := ih8_exists_omegaLie hIH hΦ.conjInvariant hΦ.classical
    ⟨_, mem_oddQuotientFamily hK⟩ hO hlt'
  obtain ⟨i, R, S, hR, hS, hKR, hJS⟩ := hQ.exists_components D
  refine ⟨D, i, R, ?_, hR, hKR⟩
  by_contra hi
  rw [hKR, hJS] at hQ
  by_cases hD : D.tag i = .trialityD4
  · exact quotViol_false_of_trialityD4 hp2 hq hΦ D hD hR hS hQ
  · exact hQ.false_of_classical hp2 hq hΦ D hi hD hR hS

theorem false_of_violation_and_swap (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hq : 5 ≤ p ^ f)
    (hIH : CITBelowU p f n) (hlt : Nat.card Y < n) {Λ : Set (Subgroup Y)}
    (hΛ : HypOmegaMod p f Λ) {K J : Subgroup Y} {zK zJ : Y} (hK : K ∈ Λ)
    (hv : AViol Λ K J zK zJ) {s : Y} (hsz : s * zK = zK * s) (hne : conjSub s K ≠ K) :
    False := by
  obtain ⟨D, i, R, hG2, hR, hKR⟩ := exists_g2_component hp2 hq hIH hlt hΛ hK hv
  have hΦ : HypOmegaMod p f (oddQuotientFamily Λ) :=
    oddQuotHyp p f hp2 hq Y Λ hΛ (classicalInvolutionOddCore Y)
      (CFSG.ComponentClassification.OddCore.odd_card Y)
  have hi : D.tag i = .G2 ∨ D.tag i = .trialityD4 := Or.inl hG2
  have hKs : conjSub s K ∈ Λ := hΛ.conjInvariant s K hK
  have hzK := hv.hzK
  have hzs : IsUniqueInvolution (conjSub s K) zK := by
    have := hzK.conj s
    have e : s * zK * s⁻¹ = zK := by rw [hsz]; group
    rwa [e] at this
  have hzbar : IsUniqueInvolution (K.map (oddQuot Y)) (oddQuot Y zK) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_oddCore_inf K) hzK
  have hzbar' : IsUniqueInvolution ((conjSub s K).map (oddQuot Y)) (oddQuot Y zK) :=
    isUniqueInvolution_map_mk_of_odd (odd_natCard_oddCore_inf _) hzs
  have hKmem : K.map (oddQuot Y) ∈ compMembers D i := ⟨R, hR, hKR⟩
  have hKsmem : (conjSub s K).map (oddQuot Y) ∈ compMembers D i :=
    twin_mem_compMembers hp2 D hi hKmem
      ⟨mem_oddQuotientFamily hKs, oddQuot Y zK, hzbar, hzbar'⟩
  obtain ⟨R₂, -, hKR₂⟩ := hKsmem
  have hs : conjSub (oddQuot Y s) (R.map (D.hom i)) = R₂.map (D.hom i) := by
    rw [← hKR, ← hKR₂]
    exact (AscQuot.map_conjSub (oddQuot Y) s K).symm
  have hc₁ : IsUniqueInvolution (R.map (D.hom i)) (oddQuot Y zK) := hKR ▸ hzbar
  have hc₂ : IsUniqueInvolution (R₂.map (D.hom i)) (oddQuot Y zK) := hKR₂ ▸ hzbar'
  have hRR : R₂ = R := false_of_twin_swap hp2 hp3 hΦ D hG2 hR hc₁ hc₂ hs
  have himg : (conjSub s K).map (oddQuot Y) = K.map (oddQuot Y) := by
    rw [hKR, hKR₂, hRR]
  exact hne (eq_of_map_eq_of_twin hΛ hKs hK hzs hzK himg)

end CFSG.ClassicalInvolution.Asc77.R10
