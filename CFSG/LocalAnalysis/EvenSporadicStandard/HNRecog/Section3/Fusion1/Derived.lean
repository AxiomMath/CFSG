module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

private theorem natCard_elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  change Nat.card (Multiplicative (Fin n → ZMod 2)) = 2 ^ n
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem natCard_of_isShapeTwoTwoTimesA8 {X : Type} [Group X]
    (h : IsShapeTwoTwoTimesA8 X) : Nat.card X = 4 * 20160 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_elem2 2, nat_card_alternatingGroup,
    Nat.card_fin]
  norm_num

private theorem natCard_of_isShapeTwoTwoTimesTwoFourA5 {X : Type} [Group X]
    (h : IsShapeTwoTwoTimesTwoFourA5 X) : Nat.card X = 4 * (16 * 60) := by
  obtain ⟨Y, _, hshape, hiso⟩ := h
  obtain ⟨e⟩ := hiso
  have hY : Nat.card Y = 16 * 60 := by
    obtain ⟨N, hN, hNiso, hQiso⟩ := hshape
    haveI : N.Normal := hN
    obtain ⟨eN⟩ := hNiso
    obtain ⟨eQ⟩ := hQiso
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
      Nat.card_congr eN.toEquiv, natCard_elem2 4, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_elem2 2, hY]
  norm_num

private theorem natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  unfold A5WrTwo
  rw [RegularWreathProduct.card, nat_card_alternatingGroup, Nat.card_fin,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  norm_num

private theorem natCard_of_isExtraspecialPlusByA5WrTwo {C : Type} [Group C]
    (h : IsExtraspecialPlusByA5WrTwo C) : Nat.card C = 2 ^ 9 * 7200 := by
  obtain ⟨Q, hQ, hw⟩ := h
  haveI : Q.Normal := hQ
  obtain ⟨hplus, _hcent, hquot⟩ := hw
  obtain ⟨_hext, hcardQ, _E, _hEQ, _hEab, _hEcard⟩ := hplus
  obtain ⟨eQ⟩ := hquot
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q, Nat.card_congr eQ.toEquiv,
    natCard_A5WrTwo, hcardQ]
  norm_num

private theorem card_centralizer_eq_of_isConj' {G : Type} [Group G] {x y : G}
    (h : IsConj x y) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact Nat.card_congr
    (centralizerMulEquiv (MulAut.conj c) (by simpa [MulAut.conj_apply] using hc)).toEquiv

private theorem centralizer_mul_eq_of_mem_center {G : Type} [Group G] {a b : G}
    (ha : a ∈ center G) :
    Subgroup.centralizer ({a * b} : Set G) = Subgroup.centralizer ({b} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hga : g * a = a * g := Subgroup.mem_center_iff.mp ha g
  constructor
  · intro hg
    apply mul_left_cancel (a := a)
    calc a * (g * b) = (a * g) * b := by rw [mul_assoc]
      _ = (g * a) * b := by rw [hga]
      _ = g * (a * b) := by rw [mul_assoc]
      _ = (a * b) * g := hg
      _ = a * (b * g) := by rw [mul_assoc]
  · intro hg
    calc g * (a * b) = (g * a) * b := by rw [mul_assoc]
      _ = (a * g) * b := by rw [hga]
      _ = a * (g * b) := by rw [mul_assoc]
      _ = a * (b * g) := by rw [hg]
      _ = (a * b) * g := by rw [mul_assoc]

private theorem isConj_mul_center_aux {G : Type} [Group G] {a : G} (ha : a ∈ center G)
    {x y : G} (h : IsConj x y) : IsConj (a * x) (a * y) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨g, ?_⟩
  have hga : g * a = a * g := Subgroup.mem_center_iff.mp ha g
  have hfix : g * a * g⁻¹ = a := by rw [hga, mul_assoc, mul_inv_cancel, mul_one]
  calc g * (a * x) * g⁻¹ = (g * a * g⁻¹) * (g * x * g⁻¹) := by group
    _ = a * y := by rw [hfix, hg]

private theorem eq_of_mem_zpowers_of_orderOf_eq_two {G : Type} [Group G] [DecidableEq G] {x y : G}
    (hx : orderOf x = 2) (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : y = x := by
  have hxfin : IsOfFinOrder x := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [← hx]; exact pow_orderOf_eq_one x⟩
  rw [hxfin.mem_zpowers_iff_mem_range_orderOf, hx, Finset.mem_image] at hy
  obtain ⟨n, hn, hny⟩ := hy
  rw [Finset.mem_range] at hn
  interval_cases n
  · simp at hny
    exact absurd hny.symm hy1
  · simp at hny
    exact hny.symm

private theorem exists_labelled_facts' (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) : ∃ z' b' u' : ↥(Gx a), TwoHSFacts ↥(Gx a) (GxSelf a) z' b' u' := by
  classical
  obtain ⟨E, hE⟩ := h.cent_a
  obtain ⟨a', z', b', u', hf⟩ := hI.facts ↥(Gx a) E hE
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have ha_ne_one : a ≠ 1 := by
    intro h1
    have h2 := h.orderOf_a
    rw [h1, orderOf_one] at h2
    norm_num at h2
  have hself_ne_one : GxSelf a ≠ 1 := by
    intro h1
    exact ha_ne_one (by simpa [GxSelf] using congrArg Subtype.val h1)
  have hself_center : GxSelf a ∈ center ↥(Gx a) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.2
  have hself_zpow : GxSelf a ∈ Subgroup.zpowers a' := by
    rw [← hf.center_eq]
    exact hself_center
  have hself2 : orderOf (GxSelf a) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      simp [GxSelf, ha2]
    · exact hself_ne_one
  have heq : GxSelf a = a' :=
    eq_of_mem_zpowers_of_orderOf_eq_two hf.orderOf_a hself_zpow hself_ne_one
  rw [← heq] at hf
  exact ⟨z', b', u', hf⟩

private theorem not_isConj_of_isF5Type' (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) : ¬ IsConj a z := by
  intro hconj
  have hcard_a : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) =
      2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11 := by
    obtain ⟨E, hE⟩ := h.cent_a
    obtain ⟨a', z', b', u', hf⟩ := hI.facts ↥(Gx a) E hE
    exact hf.card_eq
  have hcard_z : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 2 ^ 9 * 7200 :=
    natCard_of_isExtraspecialPlusByA5WrTwo h.cent_z
  have hcard := card_centralizer_eq_of_isConj' hconj
  rw [hcard_a, hcard_z] at hcard
  norm_num at hcard

theorem TwoHSFacts.isConj_mul_of_not_mem_commutator {H : Type} [Group H] {a z b z₁ : H}
    (h : TwoHSFacts H a z b z₁) {t : H} (ht : t ^ 2 = 1) (htH : t ∉ commutator H) :
    IsConj t (a * t) := by
  have ha_center : a ∈ center H := by rw [h.center_eq]; exact Subgroup.mem_zpowers a
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← h.orderOf_b]; exact pow_orderOf_eq_one b
  have hz₁2 : z₁ ^ 2 = 1 := by rw [← h.orderOf_z₁]; exact pow_orderOf_eq_one z₁
  have ha_comm : ∀ g : H, g * a = a * g := fun g => Subgroup.mem_center_iff.mp ha_center g
  have hmem_of_conj : ∀ c x : H, c ∈ commutator H → IsConj c x → x ∈ commutator H := by
    intro c x hc hconj
    rw [isConj_iff] at hconj
    obtain ⟨g, hg⟩ := hconj
    have := (inferInstance : (commutator H).Normal).conj_mem c hc g
    rwa [hg] at this
  have ht_ne_one : t ≠ 1 := fun h1 => htH (by rw [h1]; exact Subgroup.one_mem _)
  have ht_order : orderOf t = 2 := orderOf_eq_prime ht ht_ne_one
  have hcard_b : Nat.card ↥(Subgroup.centralizer ({b} : Set H)) = 4 * 20160 :=
    natCard_of_isShapeTwoTwoTimesA8 h.cent_b
  have hcard_z₁ : Nat.card ↥(Subgroup.centralizer ({z₁} : Set H)) = 4 * (16 * 60) :=
    natCard_of_isShapeTwoTwoTimesTwoFourA5 h.cent_z₁
  have hab2 : (a * b) ^ 2 = 1 := by
    have hba : b * a = a * b := ha_comm b
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b) * b := by rw [hba]
      _ = a ^ 2 * b ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [ha2, hb2, one_mul]
  have habH : a * b ∉ commutator H := by
    intro hmem
    have : b ∈ commutator H := by
      have h1 := (commutator H).mul_mem ((commutator H).inv_mem h.mem_commutator.1) hmem
      simpa using h1
    exact h.not_mem_commutator.1 this
  have hab_order : orderOf (a * b) = 2 :=
    orderOf_eq_prime hab2 (fun h1 => habH (by rw [h1]; exact Subgroup.one_mem _))
  have hab_conj_b : IsConj (a * b) b := by
    obtain ⟨j, hj⟩ := h.involution_cover (a * b) hab_order
    fin_cases j
    · exact absurd (hmem_of_conj a (a * b) h.mem_commutator.1 hj) habH
    · exact absurd (hmem_of_conj z (a * b) h.mem_commutator.2.1 hj) habH
    · exact absurd (hmem_of_conj (a * z) (a * b) h.mem_commutator.2.2 hj) habH
    · exact hj.symm
    · exfalso
      have hcent : Subgroup.centralizer ({a * b} : Set H) = Subgroup.centralizer ({b} : Set H) :=
        centralizer_mul_eq_of_mem_center ha_center
      have hcard1 : Nat.card ↥(Subgroup.centralizer ({z₁} : Set H)) =
          Nat.card ↥(Subgroup.centralizer ({a * b} : Set H)) :=
        card_centralizer_eq_of_isConj' hj
      rw [hcent, hcard_b] at hcard1
      rw [hcard_z₁] at hcard1
      exact absurd hcard1 (by norm_num)
  have haz₁2 : (a * z₁) ^ 2 = 1 := by
    have hz₁a : z₁ * a = a * z₁ := ha_comm z₁
    calc (a * z₁) ^ 2 = a * (z₁ * a) * z₁ := by rw [pow_two]; group
      _ = a * (a * z₁) * z₁ := by rw [hz₁a]
      _ = a ^ 2 * z₁ ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [ha2, hz₁2, one_mul]
  have haz₁H : a * z₁ ∉ commutator H := by
    intro hmem
    have : z₁ ∈ commutator H := by
      have h1 := (commutator H).mul_mem ((commutator H).inv_mem h.mem_commutator.1) hmem
      simpa using h1
    exact h.not_mem_commutator.2 this
  have haz₁_order : orderOf (a * z₁) = 2 :=
    orderOf_eq_prime haz₁2 (fun h1 => haz₁H (by rw [h1]; exact Subgroup.one_mem _))
  have haz₁_conj : IsConj (a * z₁) z₁ := by
    obtain ⟨j, hj⟩ := h.involution_cover (a * z₁) haz₁_order
    fin_cases j
    · exact absurd (hmem_of_conj a (a * z₁) h.mem_commutator.1 hj) haz₁H
    · exact absurd (hmem_of_conj z (a * z₁) h.mem_commutator.2.1 hj) haz₁H
    · exact absurd (hmem_of_conj (a * z) (a * z₁) h.mem_commutator.2.2 hj) haz₁H
    · exfalso
      have hcent : Subgroup.centralizer ({a * z₁} : Set H) = Subgroup.centralizer ({z₁} : Set H) :=
        centralizer_mul_eq_of_mem_center ha_center
      have hcard1 : Nat.card ↥(Subgroup.centralizer ({b} : Set H)) =
          Nat.card ↥(Subgroup.centralizer ({a * z₁} : Set H)) :=
        card_centralizer_eq_of_isConj' hj
      rw [hcent, hcard_z₁] at hcard1
      rw [hcard_b] at hcard1
      exact absurd hcard1 (by norm_num)
    · exact hj.symm
  obtain ⟨i, hi⟩ := h.involution_cover t ht_order
  fin_cases i
  · exact absurd (hmem_of_conj a t h.mem_commutator.1 hi) htH
  · exact absurd (hmem_of_conj z t h.mem_commutator.2.1 hi) htH
  · exact absurd (hmem_of_conj (a * z) t h.mem_commutator.2.2 hi) htH
  · have h2 : IsConj (a * t) (a * b) := isConj_mul_center_aux ha_center hi.symm
    have h3 : IsConj (a * b) b := hab_conj_b
    exact (h2.trans (h3.trans hi)).symm
  · have h2 : IsConj (a * t) (a * z₁) := isConj_mul_center_aux ha_center hi.symm
    have h3 : IsConj (a * z₁) z₁ := haz₁_conj
    exact (h2.trans (h3.trans hi)).symm

theorem mem_derivedOf_of_isConj_z (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) {t : G} (ht : t ∈ Gx a) (ht2 : t ^ 2 = 1) (hz : IsConj z t)
    (hat : IsConj a (a * t)) : t ∈ derivedOf (Gx a) := by
  by_contra hnot
  have htH : (⟨t, ht⟩ : ↥(Gx a)) ∉ commutator ↥(Gx a) := by
    intro hc
    exact hnot (Subgroup.mem_map.mpr ⟨⟨t, ht⟩, hc, rfl⟩)
  obtain ⟨z', b', u', hfacts⟩ := exists_labelled_facts' hI h
  have ht2' : (⟨t, ht⟩ : ↥(Gx a)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using ht2
  have hconj' : IsConj (⟨t, ht⟩ : ↥(Gx a)) (GxSelf a * ⟨t, ht⟩) :=
    TwoHSFacts.isConj_mul_of_not_mem_commutator hfacts ht2' htH
  have hconjG : IsConj t (a * t) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj'
    refine isConj_iff.mpr ⟨(g : G), ?_⟩
    have := congrArg Subtype.val hg
    simpa [GxSelf] using this
  have haz : IsConj a z := (hat.trans hconjG.symm).trans hz.symm
  exact not_isConj_of_isF5Type' hI h haz

end CFSG.EvenSporadicStandard.HNRecog.Section3
