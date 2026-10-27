module

public import CFSG.LocalAnalysis.OddStandard.ChildSmallAltOdd
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndBalanced
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndUnbalanced
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndEvenLie
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndSporadic
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveOrderTwo

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

set_option linter.unusedVariables false in
theorem oddLieType_of_lieModel_odd {G : Type} [Group G]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (hp : p.Prime) (hp2 : p ≠ 2) (ht : t ≠ .twistedB2) :
    OddLieType G :=
  ⟨t, n, p, f, hp, hp2, CFSG.Blueprint.LieModel.admissible h, h⟩

theorem ne_two_of_pow_mod_four' {p f : ℕ} (hf : 1 ≤ f)
    (h : p ^ f % 4 = 3 ∨ p ^ f % 4 = 1) : p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rcases g with _ | g
  · simp at h
  · have : 2 ^ (g + 1 + 1) = 4 * 2 ^ g := by ring
    rw [this] at h
    omega

theorem isPerfect_of_simple_nonabelian' {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · have hcomm := (commutator_eq_bot_iff G).mp h
    obtain ⟨x, y, hxy⟩ := hnonab
    exact (hxy (hcomm.is_comm.comm x y)).elim
  · exact h

theorem smallAltFiveCyclic_of_inputs
    (hU : KProperSimpleUnbalancedUOutcome)
    (hHar : ComponentClassification.HSFLit.HaradaInput)
    (hGH : ComponentClassification.UFrontier.GH74ModelsInput) : SmallAltFiveCyclic := by
  intro G _ _ L hS hθ hodd S hcyc
  obtain ⟨θ⟩ := hθ
  have := hS.simple
  have hL := hS.standard
  have : Group.IsPerfect G := isPerfect_of_simple_nonabelian' hS.nonab
  have hcard2 := small_alt_five_original_cyclic_sylow_centralizer_has_order_two hL hodd θ S hcyc
  by_cases hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥
  swap
  · push Not at hbal
    obtain ⟨z, hz, hne⟩ := hbal
    rcases smallAltFive_of_unbalanced hU hS θ ⟨z, hz, hne⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2S : 2 ∣ Nat.card (S : Subgroup (centralizer (L : Set G))) := by rw [hcard2]
  obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card'
    (G := (S : Subgroup (centralizer (L : Set G)))) 2 h2S
  have htS : ((t' : centralizer (L : Set G)) : G) ∈
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype :=
    ⟨t', t'.2, rfl⟩
  have ht : orderOf ((t' : centralizer (L : Set G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht']
  have hs : Sector L S ((t' : centralizer (L : Set G)) : G) := ⟨hL, hcyc, htS, ht⟩
  set t : G := ((t' : centralizer (L : Set G)) : G) with htdef
  have hcardsg : Nat.card (sg L S) = 2 := card_sg.trans hcard2
  have hbot := center_eq_bot hL hodd θ
  have hZ := inf_centralizer_eq_bot_of_center_eq_bot hbot
  let e : L ≃* alternatingGroup (Fin 5) := thetaEquiv θ (thetaZero_bijective hL hodd θ)
  have hbalt : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥ := hbal t ht
  have hF : FiveConfig t := fiveConfig_of_balanced hs hcardsg hbalt e
  obtain ⟨E, hE, hEel, hEcard, hEcent⟩ :=
    exists_selfCentralizing_klein_sup hs hcardsg hbalt hZ e
  have hsect : ∀ P : Subgroup G, IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P :=
    fun P hP => hHar.2 G E hE hEcard hEcent P hP
  have h3 : 3 ≤ Open.twoRank G :=
    SectionRank.le_pRank (by norm_num) (le_top : E ≤ ⊤) hEel (by rw [hEcard]; norm_num)
  rcases hGH G hS.nonab h3 hsect with ⟨p, f, hp, hp2, hf, h1⟩ |
    ⟨p, f, hp, hp2, hf, h1⟩ | ⟨f, h1⟩ | ⟨p, f, hp, hp2, hf, -, h1⟩ | ⟨p, f, hp, hp2, hf, -, h1⟩ |
    ⟨p, f, hp, hf, hm, h1⟩ | ⟨p, f, hp, hf, hm, h1⟩ | h1 | ⟨n, hn, hn', ⟨eA⟩⟩ | h1
  · rcases h1 with h1 | h1
    · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
    · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 Nat.prime_three (by norm_num) (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp hp2 (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp
      (ne_two_of_pow_mod_four' hf (Or.inl hm)) (by decide)))
  · exact Or.inr (Or.inl (oddLieType_of_lieModel_odd h1 hp
      (ne_two_of_pow_mod_four' hf (Or.inr hm)) (by decide)))
  · exact (fiveConfig_false_of_even_items h1 t hF).elim
  · by_cases h9 : 9 ≤ n
    · exact Or.inl ⟨n, h9, ⟨eA⟩⟩
    · obtain rfl : n = 8 := by omega
      exact absurd hF.five_dvd_card
        (not_five_dvd_card_centralizer_of_alternating_eight eA hF.orderOf_eq)
  · rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_M22 t hF.orderOf_eq hF).elim
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_M23 t hF.orderOf_eq hF).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_J3 t hF.orderOf_eq hF).elim
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_McL t hF.orderOf_eq hF).elim
    · obtain ⟨e'⟩ := h1
      exact (not_fiveConfig_of_mulEquiv_all e' fiveConfig_false_Ly t hF.orderOf_eq hF).elim

end CFSG.OddStandard
