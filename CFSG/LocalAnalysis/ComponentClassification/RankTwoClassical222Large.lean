module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Core
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalOddCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseDSetup

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

section Alternatives

variable {A : Subgroup G} {D : ClassicalModel A} {p : G}

theorem caseI_of_case1 (h : Case1 D p) : CaseI D p := by
  unfold CaseI
  split
  · exact h
  · exact h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h

theorem caseI_of_case23 (hfam : D.family = .symplectic) (h : Case23 D p) : CaseI D p := by
  simp only [CaseI, hfam]
  exact Or.inr h

theorem caseI_of_case4 (hfam : D.family = .orthPlus ∨ D.family = .orthMinus) (h : Case4 D p) :
    CaseI D p := by
  rcases hfam with hfam | hfam
  · simp only [CaseI, hfam]
    exact Or.inr h
  · simp only [CaseI, hfam]
    exact Or.inr h

end Alternatives

section Core

variable {A : Subgroup G}

@[expose] def CoreAlt (D : ClassicalModel A) (p : G) (Z : Subgroup G) : Prop :=
  (Z = D.alpha p ∧ D.IsAlphaClass p ∧ RegularOn A Z (nonidentity Z) ∧ AutCyclic A Z (D.q - 1)) ∨
    (D.family = .symplectic ∧ ∃ (ℓ : ℕ) (a b : G),
      (((1 < ℓ ∧ D.SuzukiType p .b ℓ ∧ D.SuzukiType a .a (ℓ - 1)) ∨
        (D.SuzukiType p .c ℓ ∧ D.SuzukiType a .a ℓ)) ∧ D.SuzukiType b .b 1) ∧
      Z = D.alpha a ⊔ D.alpha b ∧ D.alpha b ≤ centralizer (D.alpha a : Set G) ∧
      p ∉ D.alpha a ∧ p ∉ D.alpha b ∧
      RegularOn A Z {j | j ∈ Z ∧ j ∉ D.alpha a ∧ j ∉ D.alpha b} ∧
      AutDiagonal A Z (D.alpha a) (D.alpha b) (D.q - 1)) ∨
    ((D.family = .orthPlus ∨ D.family = .orthMinus) ∧ (∃ ℓ : ℕ, D.SuzukiType p .c ℓ) ∧
      RegularOn A Z (nonidentity Z) ∧ AutCyclic A Z (D.q - 1))

theorem exists_core (hF : Classical222Facts) [Finite G] (D : ClassicalModel A)
    (hA : CFSG.Open.IsQuasisimple ↥A) (hZ : Odd (Nat.card (center ↥A))) (hq : 4 ≤ D.q)
    {p : G} (hp : p ∈ A) (hp2 : orderOf p = 2) :
    ∃ Z : Subgroup G, DeltaNormal A p Z ∧ DeltaCentral A p Z ∧ CoreAlt D p Z := by
  obtain ⟨hDA, hAA, -, hJ23, hJ4⟩ := hF
  have halpha : D.IsAlphaClass p →
      ∃ Z : Subgroup G, DeltaNormal A p Z ∧ DeltaCentral A p Z ∧ CoreAlt D p Z := fun hcls =>
    ⟨D.alpha p, D.deltaNormal_alpha hZ hp hp2, hDA D.family G A D rfl hA hZ hq p hcls,
      Or.inl ⟨rfl, hcls, hAA D.family G A D rfl hA hZ hq p hcls⟩⟩
  have hJ23' : ∀ ℓ, D.family = .symplectic → (1 < ℓ ∧ D.SuzukiType p .b ℓ) ∨
      D.SuzukiType p .c ℓ →
      ∃ Z : Subgroup G, DeltaNormal A p Z ∧ DeltaCentral A p Z ∧ CoreAlt D p Z := by
    intro ℓ hfam h
    obtain ⟨a, b, htyp, hb, hN, hC, hba, hpa, hpb, hreg, hdiag⟩ :=
      hJ23 G A D hfam hA hZ hq p ℓ h
    exact ⟨_, hN, hC, Or.inr (Or.inl ⟨hfam, ℓ, a, b, ⟨htyp, hb⟩, rfl, hba, hpa, hpb, hreg,
      hdiag⟩)⟩
  cases hfam : D.family with
  | linear =>
    apply halpha
    simp only [ClassicalModel.IsAlphaClass, hfam]
    exact D.exists_hasRank hZ hp hp2
  | unitary =>
    apply halpha
    simp only [ClassicalModel.IsAlphaClass, hfam]
    exact D.exists_hasRank hZ hp hp2
  | symplectic =>
    obtain ⟨L, ℓ, hL⟩ := D.exists_suzukiType_of_family (Or.inl hfam) hZ hp hp2
    cases L with
    | a =>
      apply halpha
      simp only [ClassicalModel.IsAlphaClass, hfam]
      exact Or.inl ⟨ℓ, hL⟩
    | b =>
      have hpos := D.pos_of_hasRank (D.hasRank_of_suzukiType hL)
      rcases Nat.lt_or_ge 1 ℓ with h1 | h1
      · exact hJ23' ℓ hfam (Or.inl ⟨h1, hL⟩)
      · obtain rfl : ℓ = 1 := by omega
        apply halpha
        simp only [ClassicalModel.IsAlphaClass, hfam]
        exact Or.inr hL
    | c => exact hJ23' ℓ hfam (Or.inr hL)
  | orthPlus =>
    obtain ⟨L, ℓ, hL⟩ := D.exists_suzukiType_of_family (Or.inr (Or.inl hfam)) hZ hp hp2
    cases L with
    | a =>
      apply halpha
      simp only [ClassicalModel.IsAlphaClass, hfam]
      exact ⟨ℓ, hL⟩
    | b => exact (orthTypeAC G A D (Or.inl hfam) p ℓ hL).elim
    | c =>
      obtain ⟨Z, hN, hC, hreg, hcyc⟩ := hJ4 G A D (Or.inl hfam) hA hZ hq p ℓ hL
      exact ⟨Z, hN, hC, Or.inr (Or.inr ⟨Or.inl hfam, ⟨ℓ, hL⟩, hreg, hcyc⟩)⟩
  | orthMinus =>
    obtain ⟨L, ℓ, hL⟩ := D.exists_suzukiType_of_family (Or.inr (Or.inr hfam)) hZ hp hp2
    cases L with
    | a =>
      apply halpha
      simp only [ClassicalModel.IsAlphaClass, hfam]
      exact ⟨ℓ, hL⟩
    | b => exact (orthTypeAC G A D (Or.inr hfam) p ℓ hL).elim
    | c =>
      obtain ⟨Z, hN, hC, hreg, hcyc⟩ := hJ4 G A D (Or.inr hfam) hA hZ hq p ℓ hL
      exact ⟨Z, hN, hC, Or.inr (Or.inr ⟨Or.inr hfam, ⟨ℓ, hL⟩, hreg, hcyc⟩)⟩

end Core

theorem classical222Large_of (hF : Classical222Facts) : Classical222Large := by
  intro G _ _ A T D hq H
  have hA := H.quasisimple
  have hZ := D.odd_card_center hA hq
  have hNP : ∀ p ∈ A, orderOf p = 2 → NoPairOrbit A p := by
    intro p hp hp2
    obtain ⟨ℓ, hℓ⟩ := D.exists_hasRank hZ hp hp2
    exact hF.2.2.1 D.family G A D rfl hA hZ hq p ℓ hℓ
  have h212 := H.normalizer_cond_of hZ hNP
  have key : ∀ t ∈ T, t ≠ 1 → ∀ p : G, IsAPart A t p →
      (∀ t' ∈ T, t' ≠ 1 → ∀ p' : G, IsAPart A t' p' → ∃ a ∈ A, a * p * a⁻¹ = p') ∧
      APartsLe A T (jGroup A p) ∧ Nat.card T ≤ D.q ∧ CaseI D p := by
    intro t ht ht1 p hp
    have hp2 := H.orderOf_aPart hZ ht ht1 hp
    have hp1 := H.aPart_ne_one ht ht1 hp
    obtain ⟨Z, hN, hC, halt⟩ := exists_core hF D hA hZ hq hp.1 hp2
    have hJ := hN.jGroup_eq hC
    have hPZ : ∀ t' ∈ T, ∀ p' : G, IsAPart A t' p' → p' ∈ Z := fun t' ht' p' hp' =>
      H.aPart_mem_of_deltaCentral hZ h212 ht ht1 hp hC ht' hp'
    have hpZ : p ∈ Z := hPZ t ht p hp
    rcases halt with ⟨hZα, -, hreg, hcyc⟩ | ⟨hfam, ℓ, a, b, htyp, hZab, hba, hpa, hpb, hreg,
        hdiag⟩ | ⟨hfam, hc, hreg, hcyc⟩
    ·
      have hcard : Nat.card Z = D.q := by
        rw [card_eq_of_regularOn hreg hcyc hpZ hp1]
        omega
      refine ⟨fun t' ht' ht'1 p' hp' => ?_, by rw [hJ]; exact hPZ, ?_, ?_⟩
      · obtain ⟨a, ha, hap⟩ :=
          hreg.1 p ⟨hpZ, hp1⟩ p' ⟨hPZ t' ht' p' hp', H.aPart_ne_one ht' ht'1 hp'⟩
        exact ⟨a, (mem_inf.mp ha).1, hap⟩
      · exact (H.card_le_of_forall_mem hZ hPZ).trans hcard.le
      · refine caseI_of_case1 ⟨by rw [hJ, hZα], ?_, ?_⟩
        · rw [hJ]
          exact hreg
        · rw [hJ]
          exact hcyc
    ·
      obtain ⟨k, hak⟩ : ∃ k, D.SuzukiType a .a k :=
        htyp.1.elim (fun h => ⟨_, h.2.2⟩) fun h => ⟨_, h.2⟩
      have hb := htyp.2
      obtain ⟨hbA, hb2⟩ := D.mem_of_suzukiType hb
      obtain ⟨haA, ha2⟩ := D.mem_of_suzukiType hak
      have hout : ∀ t' ∈ T, t' ≠ 1 → ∀ v : G, IsAPart A t' v → v ∉ D.alpha a ∧ v ∉ D.alpha b := by
        intro t' ht' ht'1 v hv
        have hv1 := H.aPart_ne_one ht' ht'1 hv
        have hcore : ∀ x : G, D.IsAlphaClass v → v ∈ D.alpha x → x ∈ A → orderOf x = 2 →
            p ∈ D.alpha x := by
          intro x hcls hvx hxA hx2
          have hCv := hF.1 D.family G A D rfl hA hZ hq v hcls
          have hpv := H.aPart_mem_of_deltaCentral hZ h212 ht' ht'1 hv hCv ht hp
          rwa [D.alpha_eq_of_mem hfam hZ hxA hx2 hvx hv1] at hpv
        refine ⟨fun hva => hpa ?_, fun hvb => hpb ?_⟩
        · refine hcore a ?_ hva haA ha2
          simp only [ClassicalModel.IsAlphaClass, hfam]
          exact Or.inl ⟨k, D.suzukiType_of_mem_alpha hfam hZ hak hva hv1⟩
        · refine hcore b ?_ hvb hbA hb2
          simp only [ClassicalModel.IsAlphaClass, hfam]
          exact Or.inr (D.suzukiType_of_mem_alpha hfam hZ hb hvb hv1)
      have hΓ : ∀ t' ∈ T, t' ≠ 1 → ∀ p' : G, IsAPart A t' p' →
          p' ∈ {j | j ∈ Z ∧ j ∉ D.alpha a ∧ j ∉ D.alpha b} := fun t' ht' ht'1 p' hp' =>
        ⟨hPZ t' ht' p' hp', hout t' ht' ht'1 p' hp'⟩
      refine ⟨fun t' ht' ht'1 p' hp' => ?_, by rw [hJ]; exact hPZ, ?_, ?_⟩
      · obtain ⟨c, hc, hcp⟩ := hreg.1 p (hΓ t ht ht1 p hp) p' (hΓ t' ht' ht'1 p' hp')
        exact ⟨c, (mem_inf.mp hc).1, hcp⟩
      · have hle := H.card_le_of_sup hZ (hba.trans (centralizer_le_normalizer _))
          (fun t' ht' p' hp' => hZab ▸ hPZ t' ht' p' hp')
          (fun t' ht' ht'1 p' hp' => (hout t' ht' ht'1 p' hp').1)
        rwa [D.card_alpha_symplectic hfam hZ hbA hb2] at hle
      · refine caseI_of_case23 hfam ⟨ℓ, a, b, htyp.1, htyp.2, by rw [hJ, hZab], hpa, hpb, ?_, ?_⟩
        · rw [hJ]
          exact hreg
        · rw [hJ]
          exact hdiag
    ·
      have hcard : Nat.card Z = D.q := by
        rw [card_eq_of_regularOn hreg hcyc hpZ hp1]
        omega
      refine ⟨fun t' ht' ht'1 p' hp' => ?_, by rw [hJ]; exact hPZ, ?_, ?_⟩
      · obtain ⟨a, ha, hap⟩ :=
          hreg.1 p ⟨hpZ, hp1⟩ p' ⟨hPZ t' ht' p' hp', H.aPart_ne_one ht' ht'1 hp'⟩
        exact ⟨a, (mem_inf.mp ha).1, hap⟩
      · exact (H.card_le_of_forall_mem hZ hPZ).trans hcard.le
      · refine caseI_of_case4 hfam ⟨hc, ?_, ?_⟩
        · rw [hJ]
          exact hreg
        · rw [hJ]
          exact hcyc
  refine ⟨hZ, fun t ht ht1 t' ht' ht'1 p p' hp hp' => (key t ht ht1 p hp).1 t' ht' ht'1 p' hp',
    fun t ht ht1 p hp => ?_⟩
  obtain ⟨-, hle, hcard, hI⟩ := key t ht ht1 p hp
  exact Or.inl ⟨hle, hcard, hI⟩

theorem jSylowAt_of (hF : Classical222Facts) [Finite G] {A : Subgroup G} (D : ClassicalModel A)
    (hA : CFSG.Open.IsQuasisimple ↥A) (hZ : Odd (Nat.card (center ↥A))) (hq : 4 ≤ D.q) {p : G}
    (hp : p ∈ A) (hp2 : orderOf p = 2) : JSylowAt A p := by
  obtain ⟨Z, hN, hC, -⟩ := exists_core hF D hA hZ hq hp hp2
  exact hN.jSylowAt hC

theorem classicalJSylow_of (hF : Classical222Facts) : ClassicalJSylow := by
  refine ⟨fun G _ _ A D _ hA hZ hq p ℓ hp => ?_, fun G _ _ A D _ hA hZ hq p ℓ hp => ?_,
    fun L G _ _ A D _ hA hZ hq p ℓ hp => ?_, fun L G _ _ A D _ hA hZ hq p ℓ hp => ?_,
    fun L G _ _ A D _ hA hZ hq p ℓ hp => ?_⟩
  · obtain ⟨hpA, hp2⟩ := D.mem_of_hasRank hp
    exact jSylowAt_of hF D hA hZ hq hpA hp2
  · obtain ⟨hpA, hp2⟩ := D.mem_of_hasRank hp
    exact jSylowAt_of hF D hA hZ hq hpA hp2
  all_goals
    obtain ⟨hpA, hp2⟩ := D.mem_of_suzukiType hp
    exact jSylowAt_of hF D hA hZ hq hpA hp2

theorem Classical222.large (h : Classical222) : Classical222Large := by
  intro G _ _ A T D hq H
  obtain ⟨hL, hU, hS, hP, hM⟩ := h
  cases hfam : D.family with
  | linear =>
    refine (hL G A T D hfam H).mono (fun p hp => ?_) fun t hII => ?_
    · simp only [CaseI, hfam]
      exact hp
    · have := hII.1.2.2
      omega
  | unitary =>
    refine (hU G A T D hfam H).mono (fun p hp => ?_) fun t hII => hII
    simp only [CaseI, hfam]
    exact hp
  | symplectic =>
    refine (hS G A T D hfam H).mono (fun p hp => ?_) fun t hII => ?_
    · simp only [CaseI, hfam]
      exact hp
    · have := hII.1.2.2
      omega
  | orthPlus =>
    refine (hP G A T D hfam H).mono (fun p hp => ?_) fun t hII => hII
    simp only [CaseI, hfam]
    exact hp
  | orthMinus =>
    refine (hM G A T D hfam H).mono (fun p hp => ?_) fun t hII => hII
    simp only [CaseI, hfam]
    exact hp

theorem Classical222.two (h : Classical222) : Classical222Two := by
  intro G _ _ A T D hq2 H
  obtain ⟨hL, hU, hS, hP, hM⟩ := h
  have hT4 := H.four_le
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    rcases T.bot_or_exists_ne_one with hbot | h
    · rw [hbot, Subgroup.card_bot] at hT4
      omega
    · exact h
  refine ⟨t, ht, ht1, ?_⟩
  cases hfam : D.family with
  | linear =>
    obtain ⟨hZ, -, hc⟩ := hL G A T D hfam H
    obtain ⟨p, hp⟩ := H.exists_aPart hZ ht
    rcases hc t ht ht1 p hp with ⟨-, hTq, -⟩ | ⟨-, hrank, -⟩
    · omega
    · simp only [CaseQTwo, hfam]
      exact hrank
  | unitary =>
    obtain ⟨hZ, -, hc⟩ := hU G A T D hfam H
    obtain ⟨p, hp⟩ := H.exists_aPart hZ ht
    rcases hc t ht ht1 p hp with ⟨-, hTq, -⟩ | hII
    · omega
    · exact hII.elim
  | symplectic =>
    obtain ⟨hZ, -, hc⟩ := hS G A T D hfam H
    obtain ⟨p, hp⟩ := H.exists_aPart hZ ht
    rcases hc t ht ht1 p hp with ⟨-, hTq, -⟩ | ⟨⟨-, hT4', -⟩, -, a, ha, haN, haC⟩
    · omega
    · simp only [CaseQTwo, hfam]
      exact ⟨hZ, hT4', a, ha, haN, haC⟩
  | orthPlus =>
    obtain ⟨hZ, -, hc⟩ := hP G A T D hfam H
    obtain ⟨p, hp⟩ := H.exists_aPart hZ ht
    rcases hc t ht ht1 p hp with ⟨-, hTq, -⟩ | hII
    · omega
    · exact hII.elim
  | orthMinus =>
    obtain ⟨hZ, -, hc⟩ := hM G A T D hfam H
    obtain ⟨p, hp⟩ := H.exists_aPart hZ ht
    rcases hc t ht ht1 p hp with ⟨-, hTq, -⟩ | hII
    · omega
    · exact hII.elim

end CFSG.ComponentClassification.RankTwoClassical
