module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.E8Pilot CFSG.StandardType.MpTypeDet CFSG.StandardType.NbrInnerMore


theorem rk2_cls_det {X : Type} [Group X] {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hc : lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD)
    (hM : CFSG.StandardType.MarkedModel lab X) {t : StatedLieTag} {n f' : ℕ}
    (h : CFSG.Blueprint.LieModel X t n 2 f') :
    t = CFSG.StandardType.markTag lab ∧ n = CFSG.StandardType.markRank lab ∧
      f' = CFSG.StandardType.markDeg lab := by
  obtain ⟨tg, r, nn⟩ := lab
  unfold CFSG.StandardType.MarkedModel at hM
  dsimp only at hl hc
  have hc2 : CFSG.StandardType.markChar ⟨tg, r, nn⟩ = 2 := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hc2] at hM
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · rcases (show r = 1 ∨ 2 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSL 2 2 nn := hM
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.RankOne.sl2EvenTypeDet X nn t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hM' : CFSG.Blueprint.LieModel X .PSL (r + 1) 2 nn := hM
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by omega) hM' h
      exact ⟨h1, h2, h3⟩
  · rcases (show r = 2 ∨ 3 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSU 3 2 nn := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet X nn t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hM' : CFSG.Blueprint.LieModel X .PSU (r + 1) 2 nn := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := r + 1) (by omega) X nn t n f' hM'
          h.admissible h
      exact ⟨h1, h2, h3⟩
  · have hM' : CFSG.Blueprint.LieModel X .PSp r 2 nn := hM
    obtain ⟨h1, h2, h3⟩ :=
      CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet r X nn t n f' hM' h.admissible h
    exact ⟨h1, h2, h3⟩
  · have hM' : CFSG.Blueprint.LieModel X .PSp r 2 nn := hM
    obtain ⟨h1, h2, h3⟩ :=
      CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet r X nn t n f' hM' h.admissible h
    exact ⟨h1, h2, h3⟩
  · rcases (show r = 3 ∨ 4 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSL 4 2 nn := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) hM' h
      exact ⟨h1, h2, h3⟩
    · have hr3 : r ≠ 3 := by omega
      have hM' : CFSG.Blueprint.LieModel X .POmegaPlus r 2 nn := by
        have h' := hM
        simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
          CFSG.StandardType.markDeg, if_neg hr3] at h'
        exact h'
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt r X .POmegaPlus nn t n
        f' (Or.inl rfl) hM' h.admissible h
      simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
        CFSG.StandardType.markDeg, if_neg hr3]
      exact ⟨h1, h2, h3⟩
  · rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSL 2 2 (2 * nn) := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.RankOne.sl2EvenTypeDet X (2 * nn) t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hM' : CFSG.Blueprint.LieModel X .PSU 4 2 nn := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := 4) le_rfl X nn t n f' hM'
          h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hr2 : r ≠ 2 := by omega
      have hr3 : r ≠ 3 := by omega
      have hM' : CFSG.Blueprint.LieModel X .POmegaMinus r 2 nn := by
        have h' := hM
        simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
          CFSG.StandardType.markDeg, if_neg hr2, if_neg hr3] at h'
        exact h'
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt r X .POmegaMinus nn t
        n f' (Or.inr rfl) hM' h.admissible h
      simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
        CFSG.StandardType.markDeg, if_neg hr2, if_neg hr3]
      exact ⟨h1, h2, h3⟩

theorem rk2_ord_big_ne_small {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {s t : StatedLieTag}
    (hs : s = .E6 ∨ s = .E7 ∨ s = .E8 ∨ s = .F4 ∨ s = .twistedE6)
    (ht : t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedF4) (m n : ℕ) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder s m a ≠ CFSG.SeitzReduction.F4Pilot.evenLieOrder t n b := by
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    simp only [CFSG.SeitzReduction.F4Pilot.evenLieOrder]
  · exact (ordTrialityD4_ne_ordE6 hb ha).symm
  · exact (ordSuzuki_ne_ordE6 hb ha).symm
  · exact (ordTwistedF4_ne_ordE6 hb ha).symm
  · exact (ordTrialityD4_ne_ordE7 hb ha).symm
  · exact (ordSuzuki_ne_ordE7 hb ha).symm
  · exact (ordTwistedF4_ne_ordE7 hb ha).symm
  · exact (ordTrialityD4_ne_ordE8 hb ha).symm
  · exact (ordSuzuki_ne_ordE8 hb ha).symm
  · exact (ordTwistedF4_ne_ordE8 hb ha).symm
  · exact (ordTrialityD4_ne_ordF4 hb ha).symm
  · exact (ordSuzuki_ne_ordF4 hb ha).symm
  · exact (ordTwistedF4_ne_ordF4 hb ha).symm
  · exact (ordTrialityD4_ne_ordTwistedE6 hb ha).symm
  · exact (ordSuzuki_ne_ordTwistedE6 hb ha).symm
  · exact (ordTwistedF4_ne_ordTwistedE6 hb ha).symm

theorem rk2_rigid {G : Type} [Group G] [Finite G] {K : Subgroup G} {lab₁ lab₂ : GLALabel}
    (h₁ : LabelOf K lab₁) (h₂ : LabelOf K lab₂)
    (ht : lab₂.tag = .triD4 ∨ lab₂.tag = .twB2 ∨ lab₂.tag = .twF4) : rk2SmallTag lab₁ := by
  obtain ⟨-, hl₁, hM₁⟩ := labelOf_model h₁
  obtain ⟨-, hl₂, hM₂⟩ := labelOf_model h₂
  obtain ⟨t₂, r₂, n₂⟩ := lab₂
  obtain ⟨t₁, r₁, n₁⟩ := lab₁
  simp only at ht
  have hn₁ : 1 ≤ n₁ := hl₁.1
  have hn₂ : 1 ≤ n₂ := hl₂.1
  have hc₂ : CFSG.StandardType.markChar ⟨t₂, r₂, n₂⟩ = 2 := by
    rcases ht with rfl | rfl | rfl <;> rfl
  have hM₂' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₂ hc₂
  have e₂ := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₂'
  have hnc : ¬ (t₁ = .A ∨ t₁ = .twA ∨ t₁ = .B ∨ t₁ = .C ∨ t₁ = .D ∨ t₁ = .twD) := by
    intro hc
    obtain ⟨hs, -, -⟩ := rk2_cls_det hl₁ hc hM₁ hM₂'
    rcases ht with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (first
        | (simp [CFSG.StandardType.markTag] at hs; done)
        | (by_cases h2 : r₁ = 2 <;> by_cases h3 : r₁ = 3 <;>
            simp [CFSG.StandardType.markTag, h2, h3] at hs <;> done))
  have hbig : (t₁ = .E6 ∨ t₁ = .E7 ∨ t₁ = .E8 ∨ t₁ = .F4 ∨ t₁ = .twE6) → False := by
    intro hb
    have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁
      (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> rfl)
    have e₁ := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    have ht' : CFSG.StandardType.markTag ⟨t₂, r₂, n₂⟩ = .trialityD4 ∨
        CFSG.StandardType.markTag ⟨t₂, r₂, n₂⟩ = .twistedB2 ∨
        CFSG.StandardType.markTag ⟨t₂, r₂, n₂⟩ = .twistedF4 := by
      rcases ht with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hb' : CFSG.StandardType.markTag ⟨t₁, r₁, n₁⟩ = .E6 ∨
        CFSG.StandardType.markTag ⟨t₁, r₁, n₁⟩ = .E7 ∨ CFSG.StandardType.markTag ⟨t₁, r₁, n₁⟩ = .E8 ∨
        CFSG.StandardType.markTag ⟨t₁, r₁, n₁⟩ = .F4 ∨
        CFSG.StandardType.markTag ⟨t₁, r₁, n₁⟩ = .twistedE6 := by
      rcases hb with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    have hd₁ : CFSG.StandardType.markDeg ⟨t₁, r₁, n₁⟩ = n₁ := by
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hd₂ : CFSG.StandardType.markDeg ⟨t₂, r₂, n₂⟩ = n₂ := by
      rcases ht with rfl | rfl | rfl <;> rfl
    exact rk2_ord_big_ne_small (a := n₁) (b := n₂) hn₁ hn₂ hb' ht' _ _
      (by rw [← hd₁, ← hd₂]; exact e₁.symm.trans e₂)
  cases t₁
  · exact absurd (Or.inl rfl) hnc
  · exact absurd (Or.inr (Or.inl rfl)) hnc
  · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hnc
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hnc
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hnc
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hnc
  · exact (hbig (Or.inl rfl)).elim
  · exact (hbig (Or.inr (Or.inl rfl))).elim
  · exact (hbig (Or.inr (Or.inr (Or.inl rfl)))).elim
  · exact (hbig (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).elim
  · exact (hbig (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).elim
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem rk2_E6two_unique {G : Type} [Group G] [Finite G] {K : Subgroup G} {lab : GLALabel}
    (h : LabelOf K lab) (h₂ : LabelOf K ⟨.E6, 0, 1⟩) : lab = ⟨.E6, 0, 1⟩ := by
  obtain ⟨-, hl₁, hM₁⟩ := labelOf_model h
  obtain ⟨-, hl₂, hM₂⟩ := labelOf_model h₂
  have hM₂' : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .E6 0 2 1 := hM₂
  have e₂ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordE6 (2 ^ 1) :=
    CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₂'
  obtain ⟨t₁, r₁, n₁⟩ := lab
  have hn₁ : 1 ≤ n₁ := hl₁.1
  have hnc : ¬ (t₁ = .A ∨ t₁ = .twA ∨ t₁ = .B ∨ t₁ = .C ∨ t₁ = .D ∨ t₁ = .twD) := by
    intro hc
    obtain ⟨hs, -, -⟩ := rk2_cls_det hl₁ hc hM₁ hM₂'
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (first
        | (simp [CFSG.StandardType.markTag] at hs; done)
        | (by_cases h2 : r₁ = 2 <;> by_cases h3 : r₁ = 3 <;>
            simp [CFSG.StandardType.markTag, h2, h3] at hs <;> done))
  have hr₁ : ∀ {t : LargeEvenLieTag}, LargeEvenInLambda2 ⟨t, r₁, n₁⟩ →
      (t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨ t = .twE6 ∨ t = .triD4 ∨ t = .G2 ∨ t = .twB2 ∨
        t = .twF4 ∨ t = .B2der ∨ t = .G2der ∨ t = .twF4der) → r₁ = 0 := by
    intro t hl ht
    have h2 := hl.2
    simp only [LargeEvenInLambda2] at h2
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  cases t₁
  · exact absurd (Or.inl rfl) hnc
  · exact absurd (Or.inr (Or.inl rfl)) hnc
  · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hnc
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hnc
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hnc
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hnc
  ·
    have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordE6 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    have hn : n₁ = 1 := eq_of_ordE6_eq hn₁ le_rfl (e₁.symm.trans e₂)
    have hr : r₁ = 0 := hr₁ hl₁ (Or.inl rfl)
    subst hn hr
    rfl
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordE7 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordE6_ne_ordE7 le_rfl hn₁ (e₂.symm.trans e₁)).elim
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordE8 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordE6_ne_ordE8 le_rfl hn₁ (e₂.symm.trans e₁)).elim
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordF4 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordE6_ne_ordF4 le_rfl hn₁ (e₂.symm.trans e₁)).elim
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordTwistedE6 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordE6_ne_ordTwistedE6 le_rfl hn₁ (e₂.symm.trans e₁)).elim
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordTrialityD4 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordTrialityD4_ne_ordE6 hn₁ le_rfl (e₁.symm.trans e₂)).elim
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordG2 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordG2_ne_ordE6 hn₁ le_rfl (e₁.symm.trans e₂)).elim
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordSuzuki (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordSuzuki_ne_ordE6 hn₁ le_rfl (e₁.symm.trans e₂)).elim
  · have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordTwistedF4 (2 ^ n₁) :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordTwistedF4_ne_ordE6 hn₁ le_rfl (e₁.symm.trans e₂)).elim
  ·
    have hr : r₁ = 0 := hr₁ hl₁ (by simp)
    have hn : n₁ = 1 := by
      have h2 := hl₁.2
      simp only [LargeEvenInLambda2] at h2
      simp_all
    subst hr hn
    have h360 := card_of_B2der hM₁
    have : (360 : ℕ) = ordE6 (2 ^ 1) := h360.symm.trans e₂
    norm_num [ordE6] at this
  ·
    have hr : r₁ = 0 := hr₁ hl₁ (by simp)
    have hn : n₁ = 1 := by
      have h2 := hl₁.2
      simp only [LargeEvenInLambda2] at h2
      simp_all
    subst hr hn
    have h6048 := card_of_G2der hM₁
    have : (6048 : ℕ) = ordE6 (2 ^ 1) := h6048.symm.trans e₂
    norm_num [ordE6] at this
  ·
    have hM₁' := CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM₁ rfl
    have e₁ : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordTits :=
      CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁'
    exact (ordTits_ne_ordE6 (f := 1) le_rfl (e₁.symm.trans e₂)).elim

end CFSG.LocalAnalysis.GLTheoremA
