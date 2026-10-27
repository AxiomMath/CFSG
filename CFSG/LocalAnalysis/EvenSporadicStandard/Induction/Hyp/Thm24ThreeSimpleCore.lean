module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Alt
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.StdBareStandard
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def pinnedNames : List TauCeti.SporadicName := .HS :: Sol78Rows

@[expose] def pinnedOrder : TauCeti.SporadicName → ℕ
  | .HS => 44352000
  | .Suz => 448345497600
  | .ONan => 460815505920
  | .Co1 => 4157776806543360000
  | .HN => 273030912000000
  | .B => 4154781481226426191177580544000000
  | .M => 808017424794512875886459904961710757005754368000000000
  | .Fi22 => 64561751654400
  | .Fi23 => 4089470473293004800
  | .Fi24Prime => 1255205709190661721292800
  | .Ru => 145926144000
  | _ => 0

@[expose] def smallOrders : List ℕ := [604800, 4030387200, 145926144000, 448345497600]

@[expose] def co1CentralizerOrders : List ℕ := [89181388800, 389283840, 2012774400]

@[expose] def OrderCriterion (N : ℕ) : Prop :=
  (∀ n : ℕ, n.factorial / 2 ≠ N) ∧ (∀ g ∈ smallOrders, N ∣ g → g ≤ N) ∧
    ∀ c ∈ co1CentralizerOrders, ¬ N ∣ c

private theorem factorial_div_two_ne_of_between' {n₀ N : ℕ} (h1 : n₀.factorial / 2 < N)
    (h2 : N < (n₀ + 1).factorial / 2) (n : ℕ) : n.factorial / 2 ≠ N := by
  intro h
  rcases Nat.lt_or_ge n₀ n with hn | hn
  · have : (n₀ + 1).factorial ≤ n.factorial := Nat.factorial_le hn
    have : (n₀ + 1).factorial / 2 ≤ n.factorial / 2 := Nat.div_le_div_right this
    omega
  · have : n.factorial ≤ n₀.factorial := Nat.factorial_le hn
    have : n.factorial / 2 ≤ n₀.factorial / 2 := Nat.div_le_div_right this
    omega

theorem orderCriterion_of_mem {s : TauCeti.SporadicName} (hs : s ∈ pinnedNames) :
    OrderCriterion (pinnedOrder s) := by
  simp only [pinnedNames, Sol78Rows, List.mem_cons, List.not_mem_nil, or_false] at hs
  have key : ∀ N : ℕ, (∀ n : ℕ, n.factorial / 2 ≠ N) →
      (N ∣ 604800 → 604800 ≤ N) → (N ∣ 4030387200 → 4030387200 ≤ N) →
      (N ∣ 145926144000 → 145926144000 ≤ N) → (N ∣ 448345497600 → 448345497600 ≤ N) →
      ¬ N ∣ 89181388800 → ¬ N ∣ 389283840 → ¬ N ∣ 2012774400 → OrderCriterion N := by
    intro N halt h1 h2 h3 h4 h5 h6 h7
    refine ⟨halt, ?_, ?_⟩
    · intro g hg
      simp only [smallOrders, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> assumption
    · intro c hc
      simp only [co1CentralizerOrders, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> assumption
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [pinnedOrder]
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 11)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 14)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 14)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 20)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 17)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 31)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 43)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 16)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 20)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 24)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num
  ·
    refine key _ (fun n => factorial_div_two_ne_of_between' (n₀ := 14)
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial]) n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      norm_num

structure Thm24ThreeSimpleInputs : Prop where
  rankTwo : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ L : Subgroup G,
      CFSG.Open.standardComponentIsStandard L →
      2 ≤ CFSG.Open.pRank 2 (centralizer (L : Set G)) →
        (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
          (IsSporadic G .J2 ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .Ru ∨
            IsSporadic G .Co1)
  card_J2 : ∀ (Y : Type) [Group Y], IsSporadic Y .J2 → Nat.card Y = 604800
  card_He : ∀ (Y : Type) [Group Y], IsSporadic Y .He → Nat.card Y = 4030387200
  card_Ru : ∀ (Y : Type) [Group Y], IsSporadic Y .Ru → Nat.card Y = 145926144000
  card_Suz : ∀ (Y : Type) [Group Y], IsSporadic Y .Suz → Nat.card Y = 448345497600
  co1 : ∀ (Y : Type) [Group Y], IsSporadic Y .Co1 → ∀ u : Y, orderOf u = 2 →
    Nat.card (centralizer ({u} : Set Y)) = 89181388800 ∨
      Nat.card (centralizer ({u} : Set Y)) = 389283840 ∨
      Nat.card (centralizer ({u} : Set Y)) = 2012774400
  card_pinned : ∀ s ∈ pinnedNames, ∀ (T : Type) [Group T] [IsSimpleGroup T], IsSporadic T s →
    Nat.card T = pinnedOrder s

theorem thm24ThreeCover_simple_of_order (inp : Thm24ThreeSimpleInputs)
    {s' : TauCeti.SporadicName} {N : ℕ}
    (hcard : ∀ (T : Type) [Group T] [IsSimpleGroup T], IsSporadic T s' → Nat.card T = N)
    (hcrit : OrderCriterion N)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (A : Subgroup G) (hA : SolStd A)
    (hcov : IsSporadic (↥A ⧸ center ↥A) s')
    (hrk : 2 ≤ CFSG.pRank 2 ↥(centralizer (A : Set G))) : False := by
  obtain ⟨hstd, t, ht2, hcomp⟩ := hA
  obtain ⟨halt, hsmall, hco1⟩ := hcrit
  have hq : CFSG.IsQuasisimple ↥A := hcomp.isQuasisimple
  have hAstd : CFSG.Open.standardComponentIsStandard A :=
    standardComponentIsStandard_of_stdBare'
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥A).2.2.1.1 hq)
      (even_card_centralizer_of_le_centralizer ht2 hcomp.le) hstd
  have hrk' : 2 ≤ CFSG.Open.pRank 2 (centralizer (A : Set G)) := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hrk
  have hN : Nat.card (↥A ⧸ center ↥A) = N := by
    haveI : IsSimpleGroup (↥A ⧸ center ↥A) := hq.2.1
    exact hcard _ hcov
  have hdvd : N ∣ Nat.card A := by
    rw [← hN]
    exact Subgroup.card_quotient_dvd_card (center ↥A)
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hNle : N ≤ Nat.card A := Nat.le_of_dvd hApos hdvd
  have hAlt : Nat.card A < Nat.card G := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group A) fun h => ?_
    have htop : A = ⊤ := Subgroup.eq_top_of_card_eq A h
    have hcen : center G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h' | h'
      · exact h'
      · exfalso
        obtain ⟨a, b, hab⟩ := hna
        exact hab (Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top b) a)
    have ht : t ∈ center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ centralizer ({t} : Set G) := hcomp.le (htop ▸ Subgroup.mem_top g)
      exact mem_centralizer_singleton_iff.1 hg
    rw [hcen, Subgroup.mem_bot] at ht
    rw [ht, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  rcases inp.rankTwo G hna hkp A hAstd hrk' with ⟨n, hn9, ⟨e⟩⟩ | hJ2 | hSuz | hHe | hRu | hCo
  ·
    obtain ⟨F, _, _, hF5, ⟨ψ⟩⟩ := Balance.exists_alternating_of_component
      (fStarSimple_top G hna) (n := n) (Or.inr (by omega)) (Subgroup.topEquiv.trans e) ht2 hcomp
    have : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup hF5
    have : IsSimpleGroup ↥A := ψ.isSimpleGroup
    have h1 := Balance.card_quotient_center_eq hq
    have h2 : Nat.card A = (Nat.card F).factorial / 2 := by
      rw [Nat.card_congr ψ.toEquiv]
      exact Balance.card_alternatingGroup_of_five_le hF5
    exact halt (Nat.card F) (by rw [← h2, ← h1, hN])
  · have hg := inp.card_J2 G hJ2
    have h1 : N ∣ Nat.card G := hdvd.trans (Subgroup.card_subgroup_dvd_card A)
    have h2 := hsmall 604800 (by simp [smallOrders]) (hg ▸ h1)
    omega
  · have hg := inp.card_Suz G hSuz
    have h1 : N ∣ Nat.card G := hdvd.trans (Subgroup.card_subgroup_dvd_card A)
    have h2 := hsmall 448345497600 (by simp [smallOrders]) (hg ▸ h1)
    omega
  · have hg := inp.card_He G hHe
    have h1 : N ∣ Nat.card G := hdvd.trans (Subgroup.card_subgroup_dvd_card A)
    have h2 := hsmall 4030387200 (by simp [smallOrders]) (hg ▸ h1)
    omega
  · have hg := inp.card_Ru G hRu
    have h1 : N ∣ Nat.card G := hdvd.trans (Subgroup.card_subgroup_dvd_card A)
    have h2 := hsmall 145926144000 (by simp [smallOrders]) (hg ▸ h1)
    omega
  ·
    have h1 : N ∣ Nat.card (centralizer ({t} : Set G)) :=
      hdvd.trans (Subgroup.card_dvd_of_le hcomp.le)
    rcases inp.co1 G hCo t ht2 with h | h | h
    · exact hco1 89181388800 (by simp [co1CentralizerOrders]) (h ▸ h1)
    · exact hco1 389283840 (by simp [co1CentralizerOrders]) (h ▸ h1)
    · exact hco1 2012774400 (by simp [co1CentralizerOrders]) (h ▸ h1)

theorem thm24ThreeCover_simple (inp : Thm24ThreeSimpleInputs) {s' : TauCeti.SporadicName}
    (hs' : s' ∈ pinnedNames) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (A : Subgroup G) (hA : SolStd A) (hcov : IsSporadic (↥A ⧸ center ↥A) s')
    (hrk : 2 ≤ CFSG.pRank 2 ↥(centralizer (A : Set G))) : False :=
  thm24ThreeCover_simple_of_order inp (inp.card_pinned s' hs') (orderCriterion_of_mem hs') G hna hkp
    A hA hcov hrk

theorem thm24Three_simple_of_inputs (inp : Thm24ThreeSimpleInputs) {s' : TauCeti.SporadicName}
    (hs' : s' ∈ Sol78Rows) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (A : Subgroup G) (hA : SolStd A) (hcov : OddCover s' A)
    (hrk : 2 ≤ CFSG.pRank 2 ↥(centralizer (A : Set G))) : False :=
  thm24ThreeCover_simple inp (List.mem_cons_of_mem _ hs') G hna hkp A hA hcov.2.2 hrk

end CFSG.EvenSporadicStandard.Induction.Hyp
