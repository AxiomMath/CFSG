module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fusionZStar_quotient_of_isPComponent {S : Type*} [Group S] [Finite S] {F P : Subgroup S}
    (hPF : P ≤ F) (hP : IsPComponent 2 (P.subgroupOf F)) :
    IsSimpleGroup (P ⧸ Open.fusionZStar P) ∧
      (∃ x y : P ⧸ Open.fusionZStar P, x * y ≠ y * x) ∧
      60 ≤ Nat.card (P ⧸ Open.fusionZStar P) ∧ Nat.card (P ⧸ Open.fusionZStar P) ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hPq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P F hPF).mp hP
  obtain ⟨e⟩ := nonempty_quotient_center_equiv_fusionZStar P
  obtain ⟨-, hs, x, y, hxy⟩ := hPq
  have hs' : IsSimpleGroup (P ⧸ Open.fusionZStar P) := e.symm.isSimpleGroup
  have hna : ∃ x y : P ⧸ Open.fusionZStar P, x * y ≠ y * x :=
    ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul, h]))⟩
  refine ⟨hs', hna, GroupTheory.nonabelian_simple_order_at_least_sixty hs' hna, ?_⟩
  rw [← index_eq_card]
  exact index_dvd_card _

theorem card_ne_eighty_four {K : Type*} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hna : ∃ x y : K, x * y ≠ y * x) : Nat.card K ≠ 84 := by
  intro h84
  have h7 : (7 : ℕ).Prime := by norm_num
  obtain ⟨hd, hm, h5⟩ := GroupTheory.nonabelian_simple_Sylow_count_minimum hs hna h7
    (by rw [h84]; norm_num) (a := 1) (b := 12) le_rfl (by norm_num) (by rw [h84]; norm_num)
  have key : ∀ n ∈ Nat.divisors 12, n ≡ 1 [MOD 7] → 5 ≤ n → False := by decide
  exact key _ (Nat.mem_divisors.mpr ⟨hd, by norm_num⟩) hm h5

theorem simpleFixedComponents_l2_five : SimpleFixedComponents (IsL2Type 5) fun _ _ => False := by
  intro S _ _ _ _ hτ σ _ P hPF hP hPne
  have hS : Nat.card S = 60 := by
    rw [GSThmB.card_of_lieModel_psl_two (by norm_num) hτ]
    decide
  obtain ⟨-, -, h60, hdvd⟩ := fusionZStar_quotient_of_isPComponent hPF hP
  have hlt : Nat.card P < 60 := by
    rw [← hS]
    exact lt_of_le_of_ne (card_le_card_group P) (fun h => hPne (card_eq_iff_eq_top P |>.mp h))
  have := Nat.le_of_dvd Nat.card_pos hdvd
  omega

theorem simpleFixedComponents_l2_seven : SimpleFixedComponents (IsL2Type 7) fun _ _ => False := by
  intro S _ _ _ _ hτ σ _ P hPF hP hPne
  have hS : Nat.card S = 168 := by
    rw [GSThmB.card_of_lieModel_psl_two (by norm_num) hτ]
    decide
  obtain ⟨hs, hna, h60, hdvd⟩ := fusionZStar_quotient_of_isPComponent hPF hP
  have hPdvd : Nat.card P ∣ 168 := hS ▸ card_subgroup_dvd_card P
  have hlt : Nat.card P < 168 := by
    rw [← hS]
    exact lt_of_le_of_ne (card_le_card_group P) (fun h => hPne (card_eq_iff_eq_top P |>.mp h))
  have key : ∀ m ∈ Nat.divisors 168, ∀ d ∈ Nat.divisors 168, m ∣ d → d < 168 → 60 ≤ m →
      m = 84 := by decide
  have h84 := key _ (Nat.mem_divisors.mpr ⟨hdvd.trans hPdvd, by norm_num⟩) _
    (Nat.mem_divisors.mpr ⟨hPdvd, by norm_num⟩) hdvd hlt h60
  exact card_ne_eighty_four hs hna h84

theorem l2FixedInput : L2FixedInput := by
  have hL : ∀ q : ℕ, ∀ (K K' : Type) [Group K] [Group K'], (K ≃* K') → IsL2Type q K' →
      IsL2Type q K := fun q K K' _ _ e h => LieType.CurtisTits.lieModel_of_mulEquiv e.symm h
  exact ⟨properFixedComponents_of_simple (hL 5) (fun _ _ _ _ _ h => h)
      simpleFixedComponents_l2_five,
    properFixedComponents_of_simple (hL 7) (fun _ _ _ _ _ h => h) simpleFixedComponents_l2_seven⟩

end CFSG.ComponentClassification.GrSLit
