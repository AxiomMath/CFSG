module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheckDefs

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

@[irreducible] def cSideAllV0 : Finset V0 := Finset.univ

@[irreducible] def cSideAllSL2 : Finset SL2 := Finset.univ

@[irreducible] def cSideAllL0 : Finset (SL2 × SL2) := Finset.univ

theorem mem_cSideAllL0 (g : SL2 × SL2) : g ∈ cSideAllL0 := by
  unfold cSideAllL0
  simp

def cSideFixC (g : SL2 × SL2) : Finset V0 :=
  cSideAllV0.filter fun M => actFun g M = M

theorem cSideFixC_eq (g : SL2 × SL2) : cSideFixC g = cSideFix g := by
  simp only [cSideFixC, cSideFix, cSideAllV0]

instance (F : Finset V0) : Decidable (cSideZeroOn F) :=
  decidable_of_iff ((F.filter fun M => M ≠ 0).card = 0) (by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp only [cSideZeroOn, ne_eq, not_not])

instance (F : Finset V0) : Decidable (cSideNondegOn F) :=
  decidable_of_iff
    ((F.filter fun M => M ≠ 0 ∧ (F.filter fun N => q0Polar M N ≠ 0).card = 0).card = 0) (by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro h M hM hM0
      by_contra hne
      refine h hM ⟨hM0, ?_⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro N hN hN0
      exact hne ⟨N, hN, hN0⟩
    · intro h M hM ⟨hM0, hcard⟩
      obtain ⟨N, hN, hN0⟩ := h M hM hM0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
      exact hcard hN hN0)

instance (F : Finset V0) : Decidable (cSidePlaneOn F) :=
  decidable_of_iff
    (0 < (F.filter fun M => M ≠ 0 ∧ q0Fun M = 0 ∧
      0 < (F.filter fun N => N ≠ 0 ∧ M ≠ N ∧ q0Fun N = 0 ∧ q0Polar M N = 0).card).card) (by
    simp only [Finset.card_pos, Finset.Nonempty, Finset.mem_filter, cSidePlaneOn]
    constructor
    · rintro ⟨M, ⟨hM, hM0, hMq, N, ⟨hN, hN0, hMN, hNq, hP⟩⟩⟩
      exact ⟨M, hM, N, hN, hM0, hN0, hMN, hMq, hNq, hP⟩
    · rintro ⟨M, hM, N, hN, hM0, hN0, hMN, hMq, hNq, hP⟩
      exact ⟨M, ⟨hM, hM0, hMq, N, ⟨hN, hN0, hMN, hNq, hP⟩⟩⟩)

instance (g : SL2 × SL2) : Decidable (cSideSwapCent g) :=
  decidable_of_iff
    (0 < (cSideAllSL2.filter fun x : SL2 => x * frobSL g.2 = g.1 * x).card ∧
      0 < (cSideAllSL2.filter fun x : SL2 => x * frobSL g.1 = g.2 * x).card) (by
    simp only [cSideSwapCent, Finset.card_pos, Finset.Nonempty, Finset.mem_filter,
      cSideAllSL2, Finset.mem_univ, true_and])

instance (F : Finset V0) : Decidable (cSideGood2 F) := by unfold cSideGood2; infer_instance
instance (F : Finset V0) : Decidable (cSideGood5 F) := by unfold cSideGood5; infer_instance

theorem cSideZeroOn_fixC_iff (g : SL2 × SL2) :
    cSideZeroOn (cSideFixC g) ↔ ∀ M ∈ cSideFix g, M = 0 := by
  rw [cSideFixC_eq]
  exact Iff.rfl

theorem cSideGood2_fixC_iff (g : SL2 × SL2) :
    cSideGood2 (cSideFixC g) ↔ (cSideFix g).card = 16 ∧ cSideNondegAt g ∧ cSidePlaneAt g := by
  rw [cSideFixC_eq]
  exact Iff.rfl

theorem cSideGood5_fixC_iff (g : SL2 × SL2) :
    cSideGood5 (cSideFixC g) ↔ (cSideFix g).card = 16 ∧ cSideNondegAt g ∧ ¬ cSidePlaneAt g := by
  rw [cSideFixC_eq]
  exact Iff.rfl

@[irreducible] def cSideReps : Finset SL2 :=
  cSideAllSL2.filter fun g =>
    ((g : V0) 0 0 ≠ 0 ∧ (g : V0) 0 1 = 0) ∨ ((g : V0) 0 0 = 0 ∧ (g : V0) 1 1 = 0)

@[irreducible] def cSideOrbitE11 : Finset V0 :=
  (cSideReps ×ˢ cSideReps).image fun g => actFun g cSideE11

@[irreducible] def cSideOrbitOne : Finset V0 :=
  cSideAllSL2.image fun h => actFun (h, 1) 1

theorem exists_of_mem_cSideOrbitE11 {N : V0} (h : N ∈ cSideOrbitE11) :
    ∃ g : SL2 × SL2, actFun g cSideE11 = N := by
  unfold cSideOrbitE11 at h
  obtain ⟨g, _, hg⟩ := Finset.mem_image.1 h
  exact ⟨g, hg⟩

theorem exists_of_mem_cSideOrbitOne {N : V0} (h : N ∈ cSideOrbitOne) :
    ∃ g : SL2 × SL2, actFun g 1 = N := by
  unfold cSideOrbitOne at h
  obtain ⟨g, _, hg⟩ := Finset.mem_image.1 h
  exact ⟨(g, 1), hg⟩

theorem cSide_bool_imp2 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    ((!(decide A && decide B) || decide C) = true) ↔ (A → B → C) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> simp [hA, hB, hC]

def cSideB1 (g : SL2 × SL2) : Bool :=
  !(decide (g.1 = 1 ∨ g.2 = 1) && decide ((g ^ 3 = 1 ∨ g ^ 5 = 1) ∧ g ≠ 1)) ||
    decide (cSideZeroOn (cSideFixC g))

def cSideB2 (g : SL2 × SL2) : Bool :=
  !(decide (g ^ 3 = 1 ∧ g.1 ≠ 1) && decide (g.2 ≠ 1)) || decide (cSideGood2 (cSideFixC g))

def cSideB3 (g : SL2 × SL2) : Bool :=
  !(decide (g ^ 2 = 1) && decide (g ≠ 1)) || decide ((cSideFixC g).card = 16)

def cSideB5 (g : SL2 × SL2) : Bool :=
  !decide (g ^ 5 = 1 ∧ g.1 ≠ 1 ∧ g.2 ≠ 1) ||
    (let s := decide (cSideSwapCent g)
     (!s || decide (cSideZeroOn (cSideFixC g))) && (s || decide (cSideGood5 (cSideFixC g))))

theorem cSideB5_iff (g : SL2 × SL2) : cSideB5 g = true ↔
    (g ^ 5 = 1 → g.1 ≠ 1 → g.2 ≠ 1 →
      (cSideSwapCent g → ∀ M ∈ cSideFix g, M = 0) ∧
      (¬ cSideSwapCent g → (cSideFix g).card = 16 ∧ cSideNondegAt g ∧ ¬ cSidePlaneAt g)) := by
  unfold cSideB5
  rw [← cSideZeroOn_fixC_iff, ← cSideGood5_fixC_iff]
  by_cases hA : g ^ 5 = 1 ∧ g.1 ≠ 1 ∧ g.2 ≠ 1
  · by_cases hS : cSideSwapCent g
    · simp [hA, hS]
    · simp [hA, hS]
  · simp only [decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true, Bool.not_eq_true]
    constructor
    · intro _ h5 h1 h2
      exact absurd ⟨h5, h1, h2⟩ hA
    · intro _
      left
      simpa using hA

instance : Decidable cSideK1 :=
  decidable_of_iff (∀ g : SL2 × SL2, cSideB1 g = true) (by
    unfold cSideK1
    refine forall_congr' fun g => ?_
    unfold cSideB1
    rw [cSide_bool_imp2, cSideZeroOn_fixC_iff]
    constructor
    · intro h h35 hg hc
      exact h hc ⟨h35, hg⟩
    · intro h hc ⟨h35, hg⟩
      exact h h35 hg hc)

instance : Decidable cSideK2 :=
  decidable_of_iff (∀ g : SL2 × SL2, cSideB2 g = true) (by
    unfold cSideK2
    refine forall_congr' fun g => ?_
    unfold cSideB2
    rw [cSide_bool_imp2, cSideGood2_fixC_iff]
    simp only [and_imp])

instance : Decidable cSideK3 :=
  decidable_of_iff (∀ g : SL2 × SL2, cSideB3 g = true) (by
    unfold cSideK3
    refine forall_congr' fun g => ?_
    unfold cSideB3
    rw [cSide_bool_imp2, cSideFixC_eq])

instance : Decidable cSideK4a := by unfold cSideK4a; infer_instance

instance : Decidable cSideK4d := by unfold cSideK4d; infer_instance

instance : Decidable cSideK6a := by unfold cSideK6a; infer_instance
instance : Decidable cSideK6c := by unfold cSideK6c; infer_instance

def cSideRep4b : Prop := ∀ N : V0, N ≠ 0 → det0 N = 0 → N ∈ cSideOrbitE11

def cSideRep4c : Prop := ∀ N : V0, det0 N = 1 → N ∈ cSideOrbitOne

def cSideRep5 : Prop := (cSideAllL0.filter fun g => cSideB5 g = false).card = 0

instance : Decidable cSideRep4b := by unfold cSideRep4b; infer_instance
instance : Decidable cSideRep4c := by unfold cSideRep4c; infer_instance
instance : Decidable cSideRep5 := by unfold cSideRep5; infer_instance

def cSideModelOK (_ : Unit := ()) : Bool :=
  decide cSideK6a && decide cSideK6c && decide cSideK4a && decide cSideK4d && decide cSideRep4b &&
    decide cSideRep4c && decide cSideK3 && decide cSideK1 && decide cSideK2 && decide cSideRep5

theorem cSideK4b_of_rep (h : cSideRep4b) : cSideK4b := by
  intro N hN hdet
  exact exists_of_mem_cSideOrbitE11 (h N hN hdet)

theorem cSideK4c_of_rep (h : cSideRep4c) : cSideK4c := by
  intro N hdet
  exact exists_of_mem_cSideOrbitOne (h N hdet)

theorem cSideK5_of_rep (h : cSideRep5) : (∀ g : SL2 × SL2, g ^ 5 = 1 → g.1 ≠ 1 → g.2 ≠ 1 →
    cSideSwapCent g → ∀ M ∈ cSideFix g, M = 0) ∧ (∀ g : SL2 × SL2, g ^ 5 = 1 → g.1 ≠ 1 → g.2 ≠ 1
    → ¬ cSideSwapCent g → (cSideFix g).card = 16 ∧ cSideNondegAt g ∧ ¬ cSidePlaneAt g) := by
  unfold cSideRep5 at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have hB : ∀ g, cSideB5 g = true := fun g => by
    simpa using h (mem_cSideAllL0 g)
  refine ⟨fun g h5' h1' h2' hs => ?_, fun g h5' h1' h2' hs => ?_⟩
  · exact ((cSideB5_iff g).1 (hB g) h5' h1' h2').1 hs
  · exact ((cSideB5_iff g).1 (hB g) h5' h1' h2').2 hs

theorem cSideModelProp_of_ok (h : cSideModelOK () = true) : cSideModelProp := by
  unfold cSideModelOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h6a, h6c⟩, h4a⟩, h4d⟩, h4b⟩, h4c⟩, h3⟩, h1⟩, h2⟩, h5⟩ := h
  exact ⟨h1, h2, h3, ⟨h4a, cSideK4b_of_rep h4b, cSideK4c_of_rep h4c, h4d⟩,
    cSideK5_of_rep h5, h6a, h6c⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
