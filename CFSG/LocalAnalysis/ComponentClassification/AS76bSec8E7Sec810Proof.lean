module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Sec810
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDescent
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Frame
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7ResCentVFinal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7JData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom exists_isActionHom)
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull (outerAutomorphismGroup)


section Frames

variable {K : Type} [Field K]

theorem zx_e7FramePt_eq_of_resCent [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hr : ∀ σ ∈ F, IsRoot .E7 σ) (ho : F.Pairwise fun σ σ' => iform σ σ' = 0)
    (hcomm : ∀ z ∈ e7FrameLine K F, ∀ g ∈ Exc.cent (e7FramePt K F), z * g = g * z)
    (hres : Exc.ResCent (e7FramePt K F) (e7FrameLine K F)) :
    Exc.zx (e7FramePt K F) = e7FrameLine K F := by
  ext w
  constructor
  · rintro ⟨hw, hwc, hw2⟩
    exact Exc.centre_inv_of_resCent hres w hw hwc hw2
  · intro hw
    refine ⟨e7FrameLine_le_cent hr ho hw, fun c hc => hcomm w hw c hc, ?_⟩
    obtain ⟨d, rfl⟩ := (mem_e7FrameLine hr ho).1 hw
    exact e7FrameElt_mul_self hr ho d

theorem zx_e7FramePt_U [CharP K 2] :
    Exc.zx (e7FramePt K e7FrameU) = e7FrameLine K e7FrameU := by
  obtain ⟨-, -, hF, ho⟩ := e7Split_facts (F := e7FrameU) (by simp)
  exact zx_e7FramePt_eq_of_resCent (fun σ hσ => (hF σ hσ).1) ho commute_e7FrameLine_U
    (resCent_e7FrameU commute_e7FrameLine_U)

theorem zx_e7FramePt_V [Finite K] [CharP K 2] :
    Exc.zx (e7FramePt K e7FrameV) = e7FrameLine K e7FrameV := by
  obtain ⟨-, -, hF, ho⟩ := e7Split_facts (F := e7FrameV) (by simp)
  exact zx_e7FramePt_eq_of_resCent (fun σ hσ => (hF σ hσ).1) ho commute_e7FrameLine_V
    resCent_e7FrameV

end Frames

theorem inf_eq_bot_e7
    (h32 : Lemma32) (h4 : Asc75Theorem4)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : Nat.card K = 2 ∨ 4 ≤ Nat.card K)
    {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
    {ψ : normalizer (A : Set G) →* MulAut (adjointGroup .E7 K)}
    (hψ : IsActionHom A
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ψ)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) : T ⊓ A = ⊥ := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  have : Finite (ModGL .E7 K) := finite_modGL
  have : Finite (adjointGroup .E7 K) := Subtype.finite
  have hZC : center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨hneU, hndU, hFU, hoU⟩ := e7Split_facts (F := e7FrameU) (by simp)
  obtain ⟨hneV, hndV, hFV, hoV⟩ := e7Split_facts (F := e7FrameV) (by simp)
  have hRU := resCent_e7FrameU (K := K) commute_e7FrameLine_U
  have hRV := resCent_e7FrameV (K := K)
  rcases hq with hq2 | hq4
  ·
    refine Exc.inf_eq_bot_of_resCent_card hZC hψ h4 h32 h34 hc hOut hZA classesCover_e7Reps ?_
    intro y hy
    simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl residualMem_e7FramePt_x
    · exact Or.inl residualMem_e7FramePt_y
    · exact Or.inl residualMem_e7FramePt_z
    · refine Or.inr ⟨_, hRU, ?_⟩
      rw [card_e7FrameLine hneU hndU hFU hoU, hq2]
      norm_num
    · refine Or.inr ⟨_, hRV, ?_⟩
      rw [card_e7FrameLine hneV hndV hFV hoV, hq2]
      norm_num
  ·
    have hJ4 := e7_hJ hq4
    have hzU : Exc.zx (e7FramePt K e7FrameU) = e7FrameLine K e7FrameU := zx_e7FramePt_U
    have hzV : Exc.zx (e7FramePt K e7FrameV) = e7FrameLine K e7FrameV := zx_e7FramePt_V
    have hres : ∀ y ∈ e7Reps K, Exc.ResidualMem y ∨ Exc.ResCent y (Exc.zx y) := by
      intro y hy
      simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl residualMem_e7FramePt_x
      · exact Or.inl residualMem_e7FramePt_y
      · exact Or.inl residualMem_e7FramePt_z
      · rw [hzU]
        exact Or.inr hRU
      · rw [hzV]
        exact Or.inr hRV
    have hJ' : ∀ y ∈ e7Reps K, ∃ Z u, Exc.CentreData y Z ∧ Exc.Regular Z u := fun y hy => by
      obtain ⟨Z, u, h1, h2, -⟩ := hJ4 y hy
      exact ⟨Z, u, h1, h2⟩
    refine Exc.inf_eq_bot_of_split hZC hψ h4 h32 h34 hc hOut hZA classesCover_e7Reps hJ4
      (fun R' T' g' hc' t ht ht1 htN x hx => Exc.actsIn_zx_of_resCent_reps hZC hψ h4 h32 h34
        hc' hOut hZA classesCover_e7Reps hres charTwo_e7Reps hJ' ht ht1 htN hx) ?_
    intro y hy
    simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl residualMem_e7FramePt_x
    · exact Or.inl residualMem_e7FramePt_y
    · exact Or.inl residualMem_e7FramePt_z
    · refine Or.inr ⟨K, inferInstance, inferInstance, inferInstance, e7FrameElt K e7FrameUHead,
        e7FrameElt K [e7FrameUTail], hq4, ?_⟩
      rw [hzU]
      exact lineSplit_e7FrameU
    · refine Or.inr ⟨K, inferInstance, inferInstance, inferInstance, e7FrameElt K e7FrameVHead,
        e7FrameElt K [e7FrameVTail], hq4, ?_⟩
      rw [hzV]
      exact lineSplit_e7FrameV

theorem e7Sec810 (h32 : Lemma32)
    (h33 : Lemma33Three) (h4 : Asc75Theorem4) : E7Sec810 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | e7 m hm K hK e =>
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hm hK
    have h34 : Asc08Lemma34 := asc08Lemma34
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    have : Finite (ModGL .E7 K) := finite_modGL
    have : Finite (adjointGroup .E7 K) := Subtype.finite
    have hZC : center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
    have e₁ : AdjointQuotient .E7 K ≃* adjointGroup .E7 K :=
      (QuotientGroup.quotientMulEquivOfEq hZC).trans QuotientGroup.quotientBot
    have hOut := odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_E
      (S := rankTwoQuot A) (Or.inr (Or.inl rfl)) hm ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩)
    obtain ⟨ψ, hψ⟩ := exists_isActionHom (RankTwoHypIIY.autModel_mulAut hZC) hAp (e.trans e₁)
    have hq : Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
      rcases Nat.lt_or_ge m 2 with h | h
      · left
        rw [hK, show m = 1 by omega]
        norm_num
      · right
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h
    have hgood : ∀ {R T : Subgroup G} {g : G}, Sec3 A R T g → T ⊓ A = ⊥ := fun hc =>
      inf_eq_bot_e7 h32 h4 hq hψ hc hOut hZA
    obtain ⟨g, hg, R, T, hR, hT, -, -, hTR, -, -⟩ := section3Config_of h32 h33 h4 h34 G A hA
    have hc : Sec3 A R T g := ⟨hA, hR, hg, hT, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
    exact ⟨R, T, g, hc, hgood hc, hgood hc.swap⟩
  | g2 => simp [ExcModel.tag] at hD
  | f4 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
