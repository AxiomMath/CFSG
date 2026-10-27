module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

private theorem tableVII_orders_pow_ne_two {y : G} (hodd : Odd (orderOf y)) (k : ℕ) :
    orderOf (y ^ k) ≠ 2 := by
  intro h2
  have hdvd := orderOf_pow_dvd (x := y) k
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

private theorem tableVII_orders_ne_even {y : G} (hodd : Odd (orderOf y)) {n : ℕ} (hn : Even n) :
    orderOf y ≠ n := by
  intro h
  rw [h] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) hn

theorem tableVII_orderOf_of_2A (h : IsF5Type a z) (hT4 : TableIVFacts a z) {c t : G}
    (hc : c ∈ oddSet a a) (ht : t ∈ orb2A a a ∩ orb2A a c) : orderOf (a * c) = 3 := by
  obtain ⟨hca, hcne, hodd, -⟩ := hc
  obtain ⟨htA, htC⟩ := ht
  have htc' : c * t = t * c := mem_Gx.1 (tableVII_mem_Gx_of_orb2A h hca htC)
  have ha2 : a ^ 2 = 1 := tableVII_sq_of_isConj_a h (IsConj.refl a)
  have haa : a * a = 1 := by rw [← pow_two, ha2]
  have ht2 : orderOf t = 2 := tableVII_orderOf_of_isConj_a h htA.1
  have hbase : c ∈ sBase a t := by
    refine ⟨hca, ?_, hcne, ?_⟩
    · rw [← htc']
      exact htC.2
    · intro he
      apply tableVII_orders_ne_even hodd even_two
      rw [he, ← mul_assoc, haa, one_mul]
      exact ht2
  obtain ⟨i, hi⟩ := (hT4.partition t htA).cover c hbase
  fin_cases i
  · have hi' : c ∈ sBase a t ∧ IsConj a (a * c) := hi
    exact absurd (tableVII_orderOf_of_isConj_a h hi'.2) (tableVII_orders_ne_even hodd even_two)
  · have hi' : c ∈ sBase a t ∧ IsConj z (a * c) := hi
    exact absurd (tableVII_orderOf_of_isConj_z h hi'.2) (tableVII_orders_ne_even hodd even_two)
  · have hi' : c ∈ sBase a t ∧ (a * c) ^ 2 = t := hi
    rw [← hi'.2] at ht2
    exact absurd ht2 (tableVII_orders_pow_ne_two hodd 2)
  · have hi' : c ∈ sBase a t ∧ IsConj z ((a * c) ^ 2) := hi
    exact absurd (tableVII_orderOf_of_isConj_z h hi'.2) (tableVII_orders_pow_ne_two hodd 2)
  · have hi' : c ∈ sBase a t ∧ orderOf (a * c) = 3 := hi
    exact hi'.2
  · have hi' : c ∈ sBase a t ∧ (a * c) ^ 3 = t := hi
    rw [← hi'.2] at ht2
    exact absurd ht2 (tableVII_orders_pow_ne_two hodd 3)

theorem tableVII_rows_of_2B (h : IsF5Type a z) (hT6 : TableVIFacts a z) {c t : G}
    (hc : c ∈ oddSet a a) (ht : t ∈ orb2B a z a ∩ orb2B a z c) :
    c ∈ tSet a z t 2 ∨ c ∈ tSet a z t 5 ∨ c ∈ tSet a z t 6 := by
  obtain ⟨hca, hcne, hodd, -⟩ := hc
  obtain ⟨htA, htC⟩ := ht
  have htc' : c * t = t * c := mem_Gx.1 (tableVII_mem_Gx_of_orb2B h hca htC)
  have hbase : c ∈ tBase a z t := ⟨hca, by rw [← htc']; exact htC.2, hcne⟩
  obtain ⟨i, hi⟩ := (hT6.partition t htA).cover c hbase
  fin_cases i
  · have hi' : c ∈ tBase a z t ∧ IsConj a (a * c) := hi
    exact absurd (tableVII_orderOf_of_isConj_a h hi'.2) (tableVII_orders_ne_even hodd even_two)
  · have hi' : c ∈ tBase a z t ∧ IsConj z (a * c) := hi
    exact absurd (tableVII_orderOf_of_isConj_z h hi'.2) (tableVII_orders_ne_even hodd even_two)
  · exact Or.inl hi
  · have hi' : c ∈ tBase a z t ∧ orderOf (a * c) = 4 ∧ IsConj z ((a * c) ^ 2) := hi
    exact absurd hi'.2.1 (tableVII_orders_ne_even hodd ⟨2, rfl⟩)
  · have hi' : c ∈ tBase a z t ∧ orderOf (a * c) = 4 ∧ IsConj a ((a * c) ^ 2) := hi
    exact absurd hi'.2.1 (tableVII_orders_ne_even hodd ⟨2, rfl⟩)
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
  · have hi' : c ∈ tBase a z t ∧ orderOf (a * c) = 6 ∧ IsConj a ((a * c) ^ 3) := hi
    exact absurd hi'.2.1 (tableVII_orders_ne_even hodd ⟨3, rfl⟩)

theorem tableVII_order_three_five (h : IsF5Type a z) (hPar : ParityFacts a z)
    (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) :
    ∀ c ∈ oddSet a a, orderOf (a * c) = 3 ∨ orderOf (a * c) = 5 := by
  intro c hc
  obtain ⟨-, -, -, t, ht, htc⟩ := id hc
  rcases tableVII_star h hPar hT5 hc ht htc with h2A | h2B
  · exact Or.inl (tableVII_orderOf_of_2A h hT4 hc h2A)
  · rcases tableVII_rows_of_2B h hT6 hc h2B with hr | hr | hr
    · have hr' : c ∈ tBase a z t ∧ orderOf (a * c) = 3 := hr
      exact Or.inl hr'.2
    · have hr' : c ∈ tBase a z t ∧ orderOf (a * c) = 5 ∧
          IsShapeCentralizerFiveC ↥(Gxy t (a * c)) := hr
      exact Or.inr hr'.2.1
    · have hr' : c ∈ tBase a z t ∧ orderOf (a * c) = 5 ∧
          IsShapeCentralizerFiveB ↥(Gxy t (a * c)) := hr
      exact Or.inr hr'.2.1

theorem tableVII_five_rows (h : IsF5Type a z) (hPar : ParityFacts a z) (hT4 : TableIVFacts a z)
    (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) {c t : G} (hc : c ∈ oddSet a a)
    (h5 : orderOf (a * c) = 5) (ht : IsConj a t) (htc : t ∈ Gxy a c) :
    t ∈ orb2B a z a ∧ (c ∈ tSet a z t 5 ∨ c ∈ tSet a z t 6) := by
  rcases tableVII_star h hPar hT5 hc ht htc with h2A | h2B
  · have h3 := tableVII_orderOf_of_2A h hT4 hc h2A
    rw [h5] at h3
    exact absurd h3 (by decide)
  · refine ⟨h2B.1, ?_⟩
    rcases tableVII_rows_of_2B h hT6 hc h2B with hr | hr | hr
    · have hr' : c ∈ tBase a z t ∧ orderOf (a * c) = 3 := hr
      rw [h5] at hr'
      exact absurd hr'.2 (by decide)
    · exact Or.inl hr
    · exact Or.inr hr

theorem tableVII_three_cases (h : IsF5Type a z) (hPar : ParityFacts a z) (hT5 : TableVFacts a z)
    (hT6 : TableVIFacts a z) {c : G} (hc : c ∈ oddSet a a) (h3 : orderOf (a * c) = 3) :
    (orb2A a a ∩ orb2A a c).Nonempty ∨ ∃ t ∈ orb2B a z a, c ∈ tSet a z t 2 := by
  obtain ⟨-, -, -, t, ht, htc⟩ := id hc
  rcases tableVII_star h hPar hT5 hc ht htc with h2A | h2B
  · exact Or.inl ⟨t, h2A⟩
  · refine Or.inr ⟨t, h2B.1, ?_⟩
    rcases tableVII_rows_of_2B h hT6 hc h2B with hr | hr | hr
    · exact hr
    · have hr' : c ∈ tBase a z t ∧ orderOf (a * c) = 5 ∧
          IsShapeCentralizerFiveC ↥(Gxy t (a * c)) := hr
      rw [h3] at hr'
      exact absurd hr'.2.1 (by decide)
    · have hr' : c ∈ tBase a z t ∧ orderOf (a * c) = 5 ∧
          IsShapeCentralizerFiveB ↥(Gxy t (a * c)) := hr
      rw [h3] at hr'
      exact absurd hr'.2.1 (by decide)

end CFSG.EvenSporadicStandard.HNRecog.Section3
