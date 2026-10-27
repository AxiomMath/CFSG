module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.FiveCStab
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableMaps

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

private theorem isConj_orderOf_eq {G : Type} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq (↑c) hc

private theorem orderOf_mul_center_two {G : Type} [Group G] {a z : G}
    (ha : a ∈ Subgroup.center G) (ha2 : orderOf a = 2) (hz2 : orderOf z = 2)
    (hne : a * z ≠ 1) : orderOf (a * z) = 2 := by
  have haa : a ^ 2 = 1 := by rw [← ha2]; exact pow_orderOf_eq_one a
  have hzz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hcomm : a * z = z * a := (Subgroup.mem_center_iff.mp ha z).symm
  apply orderOf_eq_prime
  · calc (a * z) ^ 2 = a * (z * a) * z := by rw [pow_two]; group
      _ = a * (a * z) * z := by rw [← hcomm]
      _ = a * a * (z * z) := by group
      _ = 1 := by rw [← pow_two, ← pow_two, haa, hzz, mul_one]
  · exact hne

private theorem mul_center_ne_one_of_not_conj {G : Type} [Group G] {a z : G}
    (hz2 : orderOf z = 2) (h : ¬ IsConj a z) : a * z ≠ 1 := by
  intro h1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  have hza : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have haz : a = z⁻¹ := by rw [← inv_inv a, inv_eq_of_mul_eq_one_right h1]
  exact h (by simpa [haz, hza] using IsConj.refl z)

private theorem orderOf_eq_two_of_HIsA {G : Type} [Group G] {a z b x : G}
    (ha : a ∈ Subgroup.center G) (ha2 : orderOf a = 2) (hz2 : orderOf z = 2)
    (hb2 : orderOf b = 2) (hne : a * z ≠ 1) (h : HIsA a z b x) : orderOf x = 2 := by
  have haz2 : orderOf (a * z) = 2 := orderOf_mul_center_two ha ha2 hz2 hne
  unfold HIsA at h
  rcases h with h | h | h
  · exact (isConj_orderOf_eq h).symm.trans ha2
  · exact (isConj_orderOf_eq h).symm.trans haz2
  · exact (isConj_orderOf_eq h).symm.trans hb2

private theorem orderOf_eq_two_of_HIsB {G : Type} [Group G] {z z₁ x : G}
    (hz2 : orderOf z = 2) (hz₁2 : orderOf z₁ = 2) (h : HIsB z z₁ x) : orderOf x = 2 := by
  unfold HIsB at h
  rcases h with h | h
  · exact (isConj_orderOf_eq h).symm.trans hz2
  · exact (isConj_orderOf_eq h).symm.trans hz₁2

private theorem not_HIsA_HIsB {G : Type} [Group G] {a z b z₁ x : G}
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (hA : HIsA a z b x) (hB : HIsB z z₁ x) : False := by
  unfold HIsA at hA
  unfold HIsB at hB
  rcases hA with h | h | h <;> rcases hB with h' | h'
  · exact (hnc 0 1 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 0 4 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 2 1 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 2 4 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 3 1 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 3 4 (by decide)) (by simpa using h.trans h'.symm)

private theorem not_shapeC_shapeB {X : Type*} [Group X]
    (hC : IsShapeCentralizerFiveC X) (hB : IsShapeCentralizerFiveB X) : False := by
  have h1 := hC.card_eq
  have h2 := hB.card_eq
  omega

private theorem tab6Set_mem_base {G : Type} [Group G] {a z b z₁ y c : G} {i : Fin 8}
    (hc : c ∈ tab6Set a z b z₁ y i) : c ∈ tab6Base a z y := by
  fin_cases i <;> exact hc.1

private theorem tab6Set_zero_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 0) : HIsA a z b (y * c) :=
  hc.2

private theorem tab6Set_one_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 1) : HIsB z z₁ (y * c) :=
  hc.2

private theorem tab6Set_two_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 2) : orderOf (y * c) = 3 :=
  hc.2

private theorem tab6Set_three_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 3) : orderOf (y * c) = 4 ∧ HIsB z z₁ ((y * c) ^ 2) :=
  hc.2

private theorem tab6Set_four_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 4) : orderOf (y * c) = 4 ∧ HIsA a z b ((y * c) ^ 2) :=
  hc.2

private theorem tab6Set_five_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 5) :
    orderOf (y * c) = 5 ∧ IsShapeCentralizerFiveC ↥(Gx (y * c)) :=
  hc.2

private theorem tab6Set_six_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 6) :
    orderOf (y * c) = 5 ∧ IsShapeCentralizerFiveB ↥(Gx (y * c)) :=
  hc.2

private theorem tab6Set_seven_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab6Set a z b z₁ y 7) : orderOf (y * c) = 6 ∧ HIsA a z b ((y * c) ^ 3) :=
  hc.2

private theorem orderOf_mul_eq_rowOrd {G : Type} [Group G] {a z b z₁ y c : G}
    (ha : a ∈ Subgroup.center G)
    (hord : orderOf a = 2 ∧ orderOf z = 2 ∧ orderOf b = 2 ∧ orderOf z₁ = 2)
    (hne : a * z ≠ 1) {i : Fin 8} (hc : c ∈ tab6Set a z b z₁ y i) :
    orderOf (y * c) = ![2, 2, 3, 4, 4, 5, 5, 6] i := by
  fin_cases i
  · simpa using
      orderOf_eq_two_of_HIsA ha hord.1 hord.2.1 hord.2.2.1 hne (tab6Set_zero_spec hc)
  · simpa using orderOf_eq_two_of_HIsB hord.2.1 hord.2.2.2 (tab6Set_one_spec hc)
  · simpa using tab6Set_two_spec hc
  · simpa using (tab6Set_three_spec hc).1
  · simpa using (tab6Set_four_spec hc).1
  · simpa using (tab6Set_five_spec hc).1
  · simpa using (tab6Set_six_spec hc).1
  · simpa using (tab6Set_seven_spec hc).1

private theorem nonempty_mulEquiv_of_mem_conjOrbit {G : Type} [Group G] {K : Subgroup G}
    {S : Set G} (hS : IsConjOrbit K S) {c₀ c' : G} (hc₀ : c₀ ∈ S) (hc' : c' ∈ S)
    {P : Type*} [Group P] (h : Nonempty (↥(K ⊓ Gx c₀) ≃* P)) :
    Nonempty (↥(K ⊓ Gx c') ≃* P) := by
  obtain ⟨k, hk, hkconj⟩ := hS.transitive c₀ hc₀ c' hc'
  obtain ⟨e⟩ := nonempty_mulEquiv_inf_Gx_of_conj (K := K) (k := k) (c := c₀) hk
  rw [hkconj] at e
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

theorem tab6Set_disjoint {G : Type} [Group G] {a z b z₁ y : G} (ha : a ∈ Subgroup.center G)
    (hord : orderOf a = 2 ∧ orderOf z = 2 ∧ orderOf b = 2 ∧ orderOf z₁ = 2)
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j)) :
    ∀ i j, i ≠ j → Disjoint (tab6Set a z b z₁ y i) (tab6Set a z b z₁ y j) := by
  have hne_az : a * z ≠ 1 :=
    mul_center_ne_one_of_not_conj hord.2.1
      (fun hconj => (hnc 0 1 (by decide)) (by simpa using hconj))
  intro i j hij
  rw [Set.disjoint_left]
  intro c hci hcj
  fin_cases i <;> fin_cases j <;>
    first
      | exact (hij rfl).elim
      | exact absurd
          ((orderOf_mul_eq_rowOrd ha hord hne_az hci).symm.trans
            (orderOf_mul_eq_rowOrd ha hord hne_az hcj)) (by decide)
      | exact not_HIsA_HIsB hnc (tab6Set_zero_spec hci) (tab6Set_one_spec hcj)
      | exact not_HIsA_HIsB hnc (tab6Set_zero_spec hcj) (tab6Set_one_spec hci)
      | exact not_HIsA_HIsB hnc (tab6Set_four_spec hci).2 (tab6Set_three_spec hcj).2
      | exact not_HIsA_HIsB hnc (tab6Set_four_spec hcj).2 (tab6Set_three_spec hci).2
      | exact not_shapeC_shapeB (tab6Set_five_spec hci).2 (tab6Set_six_spec hcj).2
      | exact not_shapeC_shapeB (tab6Set_five_spec hcj).2 (tab6Set_six_spec hci).2

theorem tableVI_of_reps {G : Type} [Group G] [Finite G] {a z b z₁ y : G}
    (ha : a ∈ Subgroup.center G)
    (hord : orderOf a = 2 ∧ orderOf z = 2 ∧ orderOf b = 2 ∧ orderOf z₁ = 2)
    (hy : IsConj (a * z) y)
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (hK : Nat.card ↥(Gx y) = 30720) (hB : (tab6Base a z y).ncard = 5774)
    (c : Fin 8 → G) (hc : ∀ i, c i ∈ tab6Set a z b z₁ y i)
    (hstab : ∀ i, Nat.card ↥(Gx y ⊓ Gx (c i)) = ![384, 1024, 48, 64, 32, 240, 20, 16] i)
    (h3A : IsShapeD8TimesS3 ↥(Gx y ⊓ Gx (c 2)))
    (h4B : IsShapeTwoTwoTimesD8 ↥(Gx y ⊓ Gx (c 4)))
    (h5E : IsShapeZ2TimesD10 ↥(Gx y ⊓ Gx (c 6)))
    (h6A : IsShapeZ2TimesD8 ↥(Gx y ⊓ Gx (c 7))) : TableVIData a z b z₁ y := by
  have hne_az : a * z ≠ 1 :=
    mul_center_ne_one_of_not_conj hord.2.1
      (fun hconj => (hnc 0 1 (by decide)) (by simpa using hconj))
  have haz2 : orderOf (a * z) = 2 := orderOf_mul_center_two ha hord.1 hord.2.1 hne_az
  have hsum : ∑ i : Fin 8,
      Nat.card ↥(Gx y) / (![384, 1024, 48, 64, 32, 240, 20, 16] : Fin 8 → ℕ) i
      = (tab6Base a z y).ncard := by
    rw [hK, hB]
    decide
  obtain ⟨hpart, hstab'⟩ := orbitPartition_of_rows (Gx y) (tab6Base a z y)
      (tab6Set a z b z₁ y) c ![384, 1024, 48, 64, 32, 240, 20, 16]
      (by intro i x hx; fin_cases i <;> exact hx.1)
      (fun i j hij => tab6Set_disjoint ha hord hnc i j hij)
      (by
        intro i k hk x hx
        have hky : k * y * k⁻¹ = y := by rw [← mem_Gx.mp hk]; group
        have := (mem_tab6Set_conj ha z b z₁ y x k i).mpr hx
        rwa [hky] at this)
      hc hstab hsum
  refine ⟨hpart, hstab', ?_, ?_, ?_, ?_, ?_⟩
  · intro c' hc'
    exact nonempty_mulEquiv_of_mem_conjOrbit (hS := hpart.orbit 2) (hc₀ := hc 2) hc' h3A
  · intro c' hc'
    exact nonempty_mulEquiv_of_mem_conjOrbit (hS := hpart.orbit 4) (hc₀ := hc 4) hc' h4B
  · intro c' hc'
    have hfive := tab6Set_five_spec hc'
    have hbase := tab6Set_mem_base hc'
    have hc'ord : orderOf c' = 2 := (isConj_orderOf_eq hbase.1).symm.trans haz2
    have hc'c' : c' * c' = 1 := by rw [← pow_two, ← hc'ord]; exact pow_orderOf_eq_one c'
    have hyord : orderOf y = 2 := (isConj_orderOf_eq hy.symm).trans haz2
    have hyy : y * y = 1 := by rw [← pow_two, ← hyord]; exact pow_orderOf_eq_one y
    have h240 : Nat.card ↥(Gx y ⊓ Gx c') = 240 := by
      have := hstab' 5 c' hc'
      simpa using this
    exact isNonsplitDoubleCoverOfS5_inf_Gx hyy hc'c' hfive.1 hfive.2 h240
  · intro c' hc'
    exact nonempty_mulEquiv_of_mem_conjOrbit (hS := hpart.orbit 6) (hc₀ := hc 6) hc' h5E
  · intro c' hc'
    exact nonempty_mulEquiv_of_mem_conjOrbit (hS := hpart.orbit 7) (hc₀ := hc 7) hc' h6A

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
