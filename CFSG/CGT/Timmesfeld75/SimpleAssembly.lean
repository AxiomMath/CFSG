module

public import CFSG.CGT.Timmesfeld75.MaxPairDichotomy
public import CFSG.CGT.Timmesfeld75.Lemma25
import CFSG.CGT.Timmesfeld75.Sec5NineLift
public import CFSG.CGT.Timmesfeld75.SimpleCase

public section

namespace CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

theorem transitive_of_step57 (h57 : Step57) {T T₁ : Subgroup G} (hyp : StepHyp T T₁) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  intro x hx hx1 y hy hy1
  obtain ⟨h, hh, hxy⟩ := h57 G T T₁ hyp x hx hx1 y hy hy1
  exact ⟨h, hSub_le_normalizer inf_le_right hh, hxy⟩

theorem isBenderGroup_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.BenderSuzuki.IsBenderGroup B) : CFSG.BenderSuzuki.IsBenderGroup A := by
  rcases h with ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩
  · exact CFSG.BenderSuzuki.IsBenderGroup.isPSL2 n hn (e.trans e')
  · exact CFSG.BenderSuzuki.IsBenderGroup.isSuzuki n hn (e.trans e')
  · exact CFSG.BenderSuzuki.IsBenderGroup.isPSU3 n hn (e.trans e')

theorem exponents_of_step511 {c l n m : ℕ} (hc : 4 < c) (hl : 1 < l) (hdiv : c / l = 2 ^ m)
    (hcard : c = (2 ^ m) ^ n) : 1 ≤ m ∧ 2 ≤ n ∧ ¬ (n = 2 ∧ m = 1) := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hcard
      omega
    · exact h
  refine ⟨hm, ?_, ?_⟩
  · rcases n with _ | _ | n
    · simp at hcard
      omega
    · have h1 : c / l < c := Nat.div_lt_self (by omega) hl
      rw [hdiv] at h1
      simp at hcard
      omega
    · omega
  · rintro ⟨rfl, rfl⟩
    norm_num at hcard
    omega

theorem listGroup_of_naturalSL (h68 : Step68) (h79 : Step79) (h711 : Step711) (h81 : Step81)
    (h82 : Step82) {T T₁ : Subgroup G} (hyp : StepHyp T T₁) {n m : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hne : ¬ (n = 2 ∧ m = 1)) (hq : Nat.card T / Nat.card (normIn T T₁) = 2 ^ m)
    (hT : Nat.card T = (2 ^ m) ^ n) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) :
    ListGroup G := by
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · have h23 : n = 2 ∨ n = 3 := by omega
    rcases h23 with rfl | rfl
    · exact h68 G T T₁ hyp m (by omega) hq hT hnat
    · rcases Nat.eq_or_lt_of_le hm with hm1 | hm2
      · obtain rfl : m = 1 := hm1.symm
        exact h81 G T T₁ hyp hq hT hnat
      · exact h711 G T T₁ hyp m hm2 hq hT hnat
  · by_cases h41 : n = 4 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h41
      exact h82 G T T₁ hyp hq hT hnat
    · exact h79 G T T₁ hyp n m hn4 hm h41 hq hT hnat

theorem listGroup_of_maxPair (h511 : Step511) (h69 : Step69) (h68 : Step68) (h610 : Step610)
    (h79 : Step79) (h711 : Step711) (h81 : Step81) (h82 : Step82) {T T₁ : Subgroup G}
    (hyp : StepHyp T T₁) : ListGroup G := by
  by_cases h4 : Nat.card T = 4
  · exact h69 G T T₁ hyp h4
  have h4' : 4 < Nat.card T := lt_of_le_of_ne hyp.card (Ne.symm h4)
  have := hyp.finite
  have hl : 1 < Nat.card (normIn T T₁) :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 hyp.pair.nontriv
  obtain ⟨n, m, hdiv, hcard, hnat | ⟨h16, hnorm, hhat⟩⟩ := h511 G T T₁ hyp h4'
  · obtain ⟨hm, hn, hne⟩ := exponents_of_step511 h4' hl hdiv hcard
    exact listGroup_of_naturalSL h68 h79 h711 h81 h82 hyp hm hn hne hdiv hcard hnat
  · exact h610 G T T₁ hyp h16 hnorm hhat

theorem simpleCase_of_strongWC (hAsc : AschbacherNoPolarInput) (hBL : BenderListInput)
    (hBT : BenderTransitiveInput) {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {T : Subgroup G} (hS : StrongWC T) (h4 : 4 ≤ Nat.card T) :
    ListGroup G ∧ ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  have hTbot : T ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h4
    omega
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hTbot
  have hord : orderOf t = 2 := orderOf_eq_prime (hS.1.2 t ht) fun h => ht1 (Subtype.ext h)
  have heven : Even (Nat.card G) := even_iff_two_dvd.2 (hord ▸ orderOf_dvd_natCard t)
  rcases lemma25_top hAsc hS (normalClosure_eq_top_of_simple hTbot) with hZ | hB
  · exact absurd hZ (not_zStarCase_of_simple G hna heven)
  · have hc : Subgroup.center G = ⊥ := center_eq_bot_of_simple_nonabelian G hna
    have hBender : CFSG.BenderSuzuki.IsBenderGroup G :=
      isBenderGroup_of_mulEquiv
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)) hB
    exact ⟨hBL G hBender, hBT G T hS hTbot hBender⟩

theorem simpleCase_of_induction (hAsc : AschbacherNoPolarInput) (hBL : BenderListInput)
    (hBT : BenderTransitiveInput) (h57 : Step57) (h511 : Step511) (h69 : Step69) (h68 : Step68)
    (h610 : Step610) (h79 : Step79) (h711 : Step711) (h81 : Step81) (h82 : Step82)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {T : Subgroup G} (hT : IsWC T) (h4 : 4 ≤ Nat.card T) (hind : SimpleCaseUpTo (Nat.card G)) :
    ListGroup G ∧ ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := by
  rcases exists_maxPair_or_strongWC hT with ⟨T₁, hmp⟩ | hS
  · have hyp : StepHyp T T₁ := ⟨inferInstance, inferInstance, hna, hmp, h4, hind⟩
    exact ⟨listGroup_of_maxPair h511 h69 h68 h610 h79 h711 h81 h82 hyp,
      transitive_of_step57 h57 hyp⟩
  · exact simpleCase_of_strongWC hAsc hBL hBT hna hS h4

theorem simpleCaseUpTo_of_steps (hAsc : AschbacherNoPolarInput) (hBL : BenderListInput)
    (hBT : BenderTransitiveInput) (h57 : Step57) (h511 : Step511) (h69 : Step69) (h68 : Step68)
    (h610 : Step610) (h79 : Step79) (h711 : Step711) (h81 : Step81) (h82 : Step82) :
    ∀ n : ℕ, SimpleCaseUpTo n := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro G _ _ _ hlt hna T hT h4
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
    · exact ih G hlt' hna T hT h4
    · have hind : SimpleCaseUpTo (Nat.card G) := heq ▸ ih
      exact simpleCase_of_induction hAsc hBL hBT h57 h511 h69 h68 h610 h79 h711 h81 h82 hna hT h4
        hind

theorem simpleCaseStmt_of_steps (hAsc : AschbacherNoPolarInput) (hBL : BenderListInput)
    (hBT : BenderTransitiveInput) (h57 : Step57) (h511 : Step511) (h69 : Step69) (h68 : Step68)
    (h610 : Step610) (h79 : Step79) (h711 : Step711) (h81 : Step81) (h82 : Step82) :
    SimpleCaseStmt := by
  intro G _ _ _ hna T hT h4
  exact simpleCaseUpTo_of_steps hAsc hBL hBT h57 h511 h69 h68 h610 h79 h711 h81 h82
    (Nat.card G + 1) G (Nat.lt_succ_self _) hna T hT h4

end CFSG.CGT.Timmesfeld75
