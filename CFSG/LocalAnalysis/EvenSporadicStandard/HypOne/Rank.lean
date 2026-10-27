module

public import CFSG.LocalAnalysis.LargeEvenClassification.CommutingElementaryProduct
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Corollary

public section

namespace CFSG.EvenSporadicStandard.HypOne

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def HasElemAbelianEight (Y : Type*) [Group Y] : Prop :=
  ∃ E : Subgroup Y, IsElemAbelian 2 E ∧ Nat.card E = 8

theorem HasElemAbelianEight.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : HasElemAbelianEight X) : HasElemAbelianEight Y := by
  obtain ⟨E, ⟨hcomm, hexp⟩, hcard⟩ := h
  refine ⟨E.map e.toMonoidHom, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x, hx, hx'⟩ := x.2
    obtain ⟨y, hy, hy'⟩ := y.2
    have := congrArg (fun z : E => e (z : X)) (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    apply Subtype.ext
    simp only [← hx', ← hy', Subgroup.coe_mul]
    simpa [map_mul] using this
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    simp [hexp x hx]
  · exact (Nat.card_congr (E.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans
      hcard

theorem HasElemAbelianEight.of_le {G : Type*} [Group G] {K E : Subgroup G} (hEK : E ≤ K)
    (hE : IsElemAbelian 2 E) (hcard : Nat.card E = 8) : HasElemAbelianEight K := by
  obtain ⟨hcomm, hexp⟩ := hE
  refine ⟨E.subgroupOf K, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have h := hcomm.is_comm.comm ⟨(x : K), (mem_subgroupOf.mp x.2)⟩
      ⟨(y : K), (mem_subgroupOf.mp y.2)⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : E => (z : G)) h
  · apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact hexp _ (mem_subgroupOf.mp hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hcard]

theorem rowData_of_hasElemAbelianEight {Y : Type*} [Group Y] [Finite Y] (hI : HypothesisOne Y)
    (h : HasElemAbelianEight Y) : Finkelstein77.RowData Y := by
  obtain ⟨E, hE, hcard⟩ := h
  exact Finkelstein77.RowData.of_elemAbelian_eight hI E hE hcard

theorem eq_one_or_eq_of_mem_zpowers_sq {G : Type*} [Group G] {y g : G} (hy : y ^ 2 = 1)
    (hg : g ∈ zpowers y) : g = 1 ∨ g = y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have hy' : y ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hy]
  have hk : y ^ k = y ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2]
    rw [zpow_add, zpow_mul, hy', one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem isElemAbelian_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {y : G}
    (hy : orderOf y = 2) : IsElemAbelian 2 (zpowers y) ∧ Nat.card (zpowers y) = 2 ^ 1 := by
  have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  refine ⟨⟨inferInstance, fun g hg => ?_⟩, by rw [Nat.card_zpowers, hy, pow_one]⟩
  rcases eq_one_or_eq_of_mem_zpowers_sq hy2 hg with h | h
  · rw [h, one_pow]
  · rw [h, hy2]

private theorem sq_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {y : G} (hy : orderOf y = 2) :
    y * y = 1 := by
  rw [← sq, ← hy]
  exact pow_orderOf_eq_one y

private theorem ne_one_of_orderOf_eq_two {G : Type*} [Group G] {y : G} (hy : orderOf y = 2) :
    y ≠ 1 := fun h => by
  rw [h, orderOf_one] at hy
  omega

theorem exists_elemAbelian_eight {G : Type*} [Group G] [Finite G] (a b c : G)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hab2 : orderOf (a * b) = 2) (hac2 : orderOf (a * c) = 2) (hbc2 : orderOf (b * c) = 2)
    (habc : orderOf (a * b * c) = 2) :
    ∃ E : Subgroup G, E ≤ zpowers a ⊔ zpowers b ⊔ zpowers c ∧ IsElemAbelian 2 E ∧
      Nat.card E = 8 := by
  classical
  have ha2 := sq_eq_one_of_orderOf_eq_two ha
  have hb2 := sq_eq_one_of_orderOf_eq_two hb
  have hc2 := sq_eq_one_of_orderOf_eq_two hc
  have ha1 := ne_one_of_orderOf_eq_two ha
  have hb1 := ne_one_of_orderOf_eq_two hb
  have hc1 := ne_one_of_orderOf_eq_two hc
  have hab1 := ne_one_of_orderOf_eq_two hab2
  have ha2' : a ^ 2 = 1 := by rw [sq]; exact ha2
  have hb2' : b ^ 2 = 1 := by rw [sq]; exact hb2
  have hc2' : c ^ 2 = 1 := by rw [sq]; exact hc2
  have hne_ab : a ≠ b := fun h => hab1 (by rw [← h]; exact ha2)
  obtain ⟨hAe, hAc⟩ := isElemAbelian_zpowers_of_orderOf_eq_two ha
  obtain ⟨hBe, hBc⟩ := isElemAbelian_zpowers_of_orderOf_eq_two hb
  obtain ⟨hCe, hCc⟩ := isElemAbelian_zpowers_of_orderOf_eq_two hc
  have hcomm_zp : ∀ {x y : G}, x * y = y * x → zpowers x ≤ centralizer (zpowers y : Set G) := by
    intro x y hxy g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hh
    exact ((Commute.zpow_zpow (Commute.symm hxy) l k).symm.eq).symm
  have hdisj : Disjoint (zpowers a) (zpowers b) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨hga, hgb⟩
    rcases eq_one_or_eq_of_mem_zpowers_sq ha2' hga with h | h
    · exact mem_bot.mpr h
    · rcases eq_one_or_eq_of_mem_zpowers_sq hb2' hgb with h' | h'
      · exact mem_bot.mpr h'
      · exact absurd (h.symm.trans h') hne_ab
  obtain ⟨V, hAV, hBV, hVe, hVc, hVle⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (zpowers a) (zpowers b) hAe hBe hAc hBc (hcomm_zp hab) hdisj
  have hVelts : ∀ g ∈ V, g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
    have haV : a ∈ V := hAV (mem_zpowers a)
    have hbV : b ∈ V := hBV (mem_zpowers b)
    have habV : a * b ∈ V := V.mul_mem haV hbV
    have hnd : [1, a, b, a * b].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨⟨ha1.symm, hb1.symm, hab1.symm⟩, ⟨hne_ab, fun h => hb1 ?_⟩, fun h => ha1 ?_,
        not_false, List.nodup_nil⟩
      · exact mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm)
      · exact mul_right_cancel (b := b) (by rw [one_mul]; exact h.symm)
    have hsub : ((([1, a, b, a * b] : List G).toFinset : Finset G) : Set G) ⊆ (V : Set G) := by
      intro g hg
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
        or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact V.one_mem
      · exact haV
      · exact hbV
      · exact habV
    have hcard : (V : Set G).ncard ≤
        ((([1, a, b, a * b] : List G).toFinset : Finset G) : Set G).ncard := by
      have h4 : (V : Set G).ncard = 4 := by
        rw [← Nat.card_coe_set_eq]
        exact hVc.trans (by norm_num)
      rw [h4, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
      simp
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard
    intro g hg
    have : g ∈ ((([1, a, b, a * b] : List G).toFinset : Finset G) : Set G) := by
      rw [heq]
      exact hg
    simpa using this
  have hVcomm : V ≤ centralizer (zpowers c : Set G) :=
    hVle.trans (sup_le (hcomm_zp hac) (hcomm_zp hbc))
  have hdisj2 : Disjoint V (zpowers c) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨hgV, hgc⟩
    rcases eq_one_or_eq_of_mem_zpowers_sq hc2' hgc with h | h
    · exact mem_bot.mpr h
    · exfalso
      rw [h] at hgV
      rcases hVelts c hgV with h1 | h1 | h1 | h1
      · exact hc1 h1
      · rw [h1, ha2, orderOf_one] at hac2
        omega
      · rw [h1, hb2, orderOf_one] at hbc2
        omega
      · have hsq : a * b * (a * b) = 1 := by
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hab]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
        rw [h1, hsq, orderOf_one] at habc
        omega
  obtain ⟨E, -, -, hE, hEc, hEle⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product V (zpowers c)
      hVe hCe hVc hCc hVcomm hdisj2
  exact ⟨E, hEle.trans (sup_le_sup_right hVle _), hE, by rw [hEc]; norm_num⟩

end CFSG.EvenSporadicStandard.HypOne
