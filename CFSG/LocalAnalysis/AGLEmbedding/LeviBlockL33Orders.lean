module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Defs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusTypes
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

namespace LeviBlock

theorem ordA_false_of_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1)
    (he : 1 ≤ e) (h : ordA n q = 2 ^ e * m)
    (hcheck : ∀ n' f' : ℕ, n' ≤ e → f' ≤ e → f' * (n' * (n' + 1) / 2) = e →
      ordA n' (2 ^ f') ≠ 2 ^ e * m) : False := by
  obtain ⟨-, h2, -, h4, h5⟩ := LeviBlock.ordA_two_part hq hm he h
  subst hq
  exact hcheck n f h2 h4 h5 h

theorem ordTwistedA_false_of_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1)
    (he : 1 ≤ e) (h : ordTwistedA n q = 2 ^ e * m)
    (hcheck : ∀ n' f' : ℕ, n' ≤ e → f' ≤ e → f' * (n' * (n' + 1) / 2) = e →
      ordTwistedA n' (2 ^ f') ≠ 2 ^ e * m) : False := by
  obtain ⟨-, h2, -, h4, h5⟩ := LeviBlock.ordTwistedA_two_part hq hm he h
  subst hq
  exact hcheck n f h2 h4 h5 h

theorem ordBC_false_of_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1)
    (he : 1 ≤ e) (h : ordBC n q = 2 ^ e * m)
    (hcheck : ∀ n' f' : ℕ, n' ≤ e → f' ≤ e → f' * (n' * n') = e →
      ordBC n' (2 ^ f') ≠ 2 ^ e * m) : False := by
  obtain ⟨-, h2, -, h4, h5⟩ := LeviBlock.ordBC_two_part hq hm he h
  subst hq
  exact hcheck n f h2 h4 h5 h

theorem ordD_false_of_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1)
    (he : 1 ≤ e) (h : ordD n q = 2 ^ e * m)
    (hcheck : ∀ n' f' : ℕ, n' ≤ e → f' ≤ e → f' * (n' * (n' - 1)) = e →
      ordD n' (2 ^ f') ≠ 2 ^ e * m) : False := by
  obtain ⟨-, h2, -, h4, h5⟩ := LeviBlock.ordD_two_part hq hm he h
  subst hq
  exact hcheck n f h2 h4 h5 h

theorem ordTwistedD_false_of_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1)
    (he : 1 ≤ e) (h : ordTwistedD n q = 2 ^ e * m)
    (hcheck : ∀ n' f' : ℕ, n' ≤ e → f' ≤ e → f' * (n' * (n' - 1)) = e →
      ordTwistedD n' (2 ^ f') ≠ 2 ^ e * m) : False := by
  obtain ⟨-, h2, -, h4, h5⟩ := LeviBlock.ordTwistedD_two_part hq hm he h
  subst hq
  exact hcheck n f h2 h4 h5 h

theorem three_dvd_of_isL33U35L37HeOrder {n : ℕ} (h : IsL33U35L37HeOrder n) : 3 ∣ n := by
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

theorem ordA_not_isL33U35L37HeOrder {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsL33U35L37HeOrder (ordA n q) := by
  rintro (h | h | h | h)
  · refine ordA_false_of_two_part (n := n) hq (e := 4) (m := 351) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordA; decide)
  · refine ordA_false_of_two_part (n := n) hq (e := 4) (m := 7875) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordA; decide)
  · refine ordA_false_of_two_part (n := n) hq (e := 5) (m := 58653) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordA; decide)
  · refine ordA_false_of_two_part (n := n) hq (e := 10) (m := 3935925) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordA; decide)

theorem ordTwistedA_not_isL33U35L37HeOrder {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsL33U35L37HeOrder (ordTwistedA n q) := by
  rintro (h | h | h | h)
  · refine ordTwistedA_false_of_two_part (n := n) hq (e := 4) (m := 351) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;>
      first | omega | (unfold ordTwistedA; decide)
  · refine ordTwistedA_false_of_two_part (n := n) hq (e := 4) (m := 7875) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;>
      first | omega | (unfold ordTwistedA; decide)
  · refine ordTwistedA_false_of_two_part (n := n) hq (e := 5) (m := 58653) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;>
      first | omega | (unfold ordTwistedA; decide)
  · refine ordTwistedA_false_of_two_part (n := n) hq (e := 10) (m := 3935925) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;>
      first | omega | (unfold ordTwistedA; decide)

theorem ordBC_not_isL33U35L37HeOrder {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsL33U35L37HeOrder (ordBC n q) := by
  rintro (h | h | h | h)
  · refine ordBC_false_of_two_part (n := n) hq (e := 4) (m := 351) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordBC; decide)
  · refine ordBC_false_of_two_part (n := n) hq (e := 4) (m := 7875) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordBC; decide)
  · refine ordBC_false_of_two_part (n := n) hq (e := 5) (m := 58653) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordBC; decide)
  · refine ordBC_false_of_two_part (n := n) hq (e := 10) (m := 3935925) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordBC; decide)

theorem ordD_not_isL33U35L37HeOrder {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsL33U35L37HeOrder (ordD n q) := by
  rintro (h | h | h | h)
  · refine ordD_false_of_two_part (n := n) hq (e := 4) (m := 351) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordD; decide)
  · refine ordD_false_of_two_part (n := n) hq (e := 4) (m := 7875) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordD; decide)
  · refine ordD_false_of_two_part (n := n) hq (e := 5) (m := 58653) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordD; decide)
  · refine ordD_false_of_two_part (n := n) hq (e := 10) (m := 3935925) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordD; decide)

theorem ordTwistedD_not_isL33U35L37HeOrder {n q f : ℕ} (hq : q = 2 ^ f) :
    ¬ IsL33U35L37HeOrder (ordTwistedD n q) := by
  rintro (h | h | h | h)
  · refine ordTwistedD_false_of_two_part (n := n) hq (e := 4) (m := 351) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordTwistedD; decide)
  · refine ordTwistedD_false_of_two_part (n := n) hq (e := 4) (m := 7875) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordTwistedD; decide)
  · refine ordTwistedD_false_of_two_part (n := n) hq (e := 5) (m := 58653) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordTwistedD; decide)
  · refine ordTwistedD_false_of_two_part (n := n) hq (e := 10) (m := 3935925) (by norm_num)
      (by norm_num) (h.trans (by norm_num)) ?_
    intro n' f' h1 h2 h3
    interval_cases n' <;> interval_cases f' <;> first | omega | (unfold ordTwistedD; decide)

theorem card_alternatingGroup_not_isL33U35L37HeOrder (n : ℕ) :
    ¬ IsL33U35L37HeOrder (Nat.card (alternatingGroup (Fin n))) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h1 : Nat.card (alternatingGroup (Fin n)) = 1 := by
      rw [Nat.card_eq_fintype_card]
      refine Fintype.card_eq_one_iff.mpr ⟨⟨1, Subgroup.one_mem _⟩, ?_⟩
      intro a
      exact Subtype.ext (Equiv.ext fun x => by
        interval_cases n
        · exact x.elim0
        · exact Subsingleton.elim _ _)
    rw [h1]
    rintro (h | h | h | h) <;> omega
  · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    have hAc := nat_card_alternatingGroup (α := Fin n)
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
    rw [hAc]
    rcases Nat.lt_or_ge n 14 with hlt | hge
    · interval_cases n <;> rintro (h | h | h | h) <;> revert h <;> decide
    · have hmono : (14 : ℕ).factorial / 2 ≤ n.factorial / 2 :=
        Nat.div_le_div_right (Nat.factorial_le hge)
      have h14 : ((14 : ℕ).factorial / 2) = 43589145600 := by decide
      rw [h14] at hmono
      rintro (h | h | h | h) <;> omega

theorem not_isL33U35L37HeOrder_of_mem_linBlockOrders {f : ℕ} (hf : 1 ≤ f) :
    ∀ n ∈ linBlockOrders (GaloisField 2 f), ¬ IsL33U35L37HeOrder n := by
  rintro n ⟨m, -, rfl⟩
  exact ordA_not_isL33U35L37HeOrder (f := f) (GaloisField.card 2 f (by omega))

theorem not_isL33U35L37HeOrder_of_mem_uniBlockOrders (f s ε : ℕ) :
    ∀ n ∈ uniBlockOrders f s ε, ¬ IsL33U35L37HeOrder n := by
  rintro n (⟨k, rfl⟩ | rfl)
  · exact ordA_not_isL33U35L37HeOrder (q := (2 ^ f) ^ 2) (f := 2 * f)
      (by rw [← pow_mul, Nat.mul_comm])
  · exact ordTwistedA_not_isL33U35L37HeOrder rfl

theorem not_isL33U35L37HeOrder_of_mem_spBlockOrders {q f : ℕ} (hq : q = 2 ^ f) :
    ∀ n ∈ spBlockOrders q, ¬ IsL33U35L37HeOrder n := by
  rintro n (⟨k, rfl⟩ | ⟨m, rfl⟩ | rfl)
  · exact ordA_not_isL33U35L37HeOrder hq
  · exact ordBC_not_isL33U35L37HeOrder hq
  · rintro (h | h | h | h) <;> omega

theorem not_isL33U35L37HeOrder_of_mem_plusBlockOrders {q f : ℕ} (hq : q = 2 ^ f) :
    ∀ n ∈ plusBlockOrders q, ¬ IsL33U35L37HeOrder n := by
  rintro n (⟨k, -, rfl⟩ | ⟨m, -, rfl⟩)
  · exact ordA_not_isL33U35L37HeOrder hq
  · exact ordD_not_isL33U35L37HeOrder hq

theorem not_isL33U35L37HeOrder_of_mem_orthMinusBlockOrders {f : ℕ} :
    ∀ n ∈ orthMinusBlockOrders (2 ^ f), ¬ IsL33U35L37HeOrder n := by
  rintro n (⟨k, -, rfl⟩ | ⟨m, -, rfl⟩)
  · exact ordA_not_isL33U35L37HeOrder rfl
  · exact ordTwistedD_not_isL33U35L37HeOrder rfl

end LeviBlock

end CFSG.AGLEmbedding
