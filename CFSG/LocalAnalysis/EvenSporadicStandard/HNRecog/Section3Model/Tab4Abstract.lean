module

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
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [← pow_two a, ← pow_two z, haa, hzz, one_mul]
  · exact hne

private theorem mul_center_ne_one_of_not_conj {G : Type} [Group G] {a z : G}
    (hz2 : orderOf z = 2) (h : ¬ IsConj a z) : a * z ≠ 1 := by
  intro h1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  have hza : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have haz : a = z⁻¹ := by rw [← inv_inv a, inv_eq_of_mul_eq_one_right h1]
  exact h (by simpa [haz, hza] using (IsConj.refl a : IsConj a a))

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

private theorem conj_sq_sq_eq_one {G : Type} [Group G] {p x : G} (hp : p ^ 2 = 1)
    (h : IsConj p (x ^ 2)) : x ^ 4 = 1 := by
  have h' := h.pow 2
  rw [hp] at h'
  have h1 : (x ^ 2) ^ 2 = 1 := isConj_one_right.mp h'
  rwa [show (x ^ 2) ^ 2 = x ^ 4 from by rw [← pow_mul]] at h1

private theorem conj_ne_one {G : Type} [Group G] {p x : G} (hp : p ≠ 1) (h : IsConj p x) :
    x ≠ 1 := by
  intro hx
  rw [hx] at h
  exact hp (isConj_one_left.mp h)

private theorem orderOf_eq_four_of_pow_four_eq_one_of_sq_ne_one {G : Type} [Group G] {x : G}
    (h4 : x ^ 4 = 1) (h2 : x ^ 2 ≠ 1) : orderOf x = 4 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (n := 4) (by norm_num) h4 ?_
  intro p hp hpdiv
  have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hpdiv
  have hp_ge : 2 ≤ p := hp.two_le
  interval_cases p
  · rw [show 4 / 2 = 2 by norm_num]; exact h2
  · norm_num at hpdiv
  · norm_num at hp

private theorem orderOf_eq_six_of_cube_eq {G : Type} [Group G] {x a : G} (ha2 : a ^ 2 = 1)
    (ha_ne : a ≠ 1) (hx3 : x ^ 3 = a) (hx2ne : x ^ 2 ≠ 1) : orderOf x = 6 := by
  have hx6 : x ^ 6 = 1 := by
    rw [show x ^ 6 = (x ^ 3) ^ 2 from by rw [← pow_mul], hx3, ha2]
  refine orderOf_eq_of_pow_and_pow_div_prime (n := 6) (by norm_num) hx6 ?_
  intro p hp hpdiv
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpdiv
  have hp_ge : 2 ≤ p := hp.two_le
  interval_cases p
  · rw [show 6 / 2 = 3 by norm_num, hx3]; exact ha_ne
  · rw [show 6 / 3 = 2 by norm_num]; exact hx2ne
  · norm_num at hpdiv
  · norm_num at hpdiv
  · norm_num at hp

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

private theorem not_sq_eq_center_of_HIsB {G : Type} [Group G] {a z b z₁ y c : G}
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (h2 : (y * c) ^ 2 = a) (hB : HIsB z z₁ ((y * c) ^ 2)) : False := by
  unfold HIsB at hB
  rcases hB with h | h
  · rw [h2] at h
    exact (hnc 0 1 (by decide)) (by simpa using h.symm)
  · rw [h2] at h
    exact (hnc 0 4 (by decide)) (by simpa using h.symm)

private theorem tab4Set_mem_base {G : Type} [Group G] {a z b z₁ y c : G} {i : Fin 6}
    (hc : c ∈ tab4Set a z b z₁ y i) : c ∈ tab4Base a b y := by
  fin_cases i <;> (simp [tab4Set] at hc; exact hc.1)

private theorem tab4Set_zero_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab4Set a z b z₁ y 0) : HIsA a z b (y * c) := by
  have h := hc; simp [tab4Set] at h; exact h.2

private theorem tab4Set_one_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab4Set a z b z₁ y 1) : HIsB z z₁ (y * c) := by
  have h := hc; simp [tab4Set] at h; exact h.2

private theorem tab4Set_two_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab4Set a z b z₁ y 2) : (y * c) ^ 2 = a := by
  have h := hc; simp [tab4Set] at h; exact h.2

private theorem tab4Set_three_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab4Set a z b z₁ y 3) : HIsB z z₁ ((y * c) ^ 2) := by
  have h := hc; simp [tab4Set] at h; exact h.2

private theorem tab4Set_four_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab4Set a z b z₁ y 4) : orderOf (y * c) = 3 := by
  have h := hc; simp [tab4Set] at h; exact h.2

private theorem tab4Set_five_spec {G : Type} [Group G] {a z b z₁ y c : G}
    (hc : c ∈ tab4Set a z b z₁ y 5) : (y * c) ^ 3 = a := by
  have h := hc; simp [tab4Set] at h; exact h.2

private theorem orderOf_mul_eq_rowOrd {G : Type} [Group G] {a z b z₁ y c : G}
    (ha : a ∈ Subgroup.center G)
    (hord : orderOf a = 2 ∧ orderOf z = 2 ∧ orderOf b = 2 ∧ orderOf z₁ = 2)
    (hy : IsConj b y) (hne_az : a * z ≠ 1) {i : Fin 6}
    (hc : c ∈ tab4Set a z b z₁ y i) :
    orderOf (y * c) = ![2, 2, 4, 4, 3, 6] i := by
  have ha2 : a ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hord.1]
  have ha_ne : a ≠ 1 := by
    rintro rfl
    have h1 : orderOf (1 : G) = 2 := hord.1
    rw [orderOf_one] at h1
    omega
  fin_cases i
  · simpa using
      orderOf_eq_two_of_HIsA ha hord.1 hord.2.1 hord.2.2.1 hne_az (tab4Set_zero_spec hc)
  · simpa using orderOf_eq_two_of_HIsB hord.2.1 hord.2.2.2 (tab4Set_one_spec hc)
  · have hx2a : (y * c) ^ 2 = a := tab4Set_two_spec hc
    have hx4 : (y * c) ^ 4 = 1 := by
      rw [show (y * c) ^ 4 = ((y * c) ^ 2) ^ 2 from by rw [← pow_mul], hx2a, ha2]
    have hx2ne : (y * c) ^ 2 ≠ 1 := by rw [hx2a]; exact ha_ne
    simpa using orderOf_eq_four_of_pow_four_eq_one_of_sq_ne_one hx4 hx2ne
  · have hB := tab4Set_three_spec hc
    have hz2 : z ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hord.2.1]
    have hz12 : z₁ ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hord.2.2.2]
    have hz_ne : z ≠ 1 := by
      rintro rfl
      have h1 : orderOf (1 : G) = 2 := hord.2.1
      rw [orderOf_one] at h1
      omega
    have hz1_ne : z₁ ≠ 1 := by
      rintro rfl
      have h1 : orderOf (1 : G) = 2 := hord.2.2.2
      rw [orderOf_one] at h1
      omega
    have hx4 : (y * c) ^ 4 = 1 := by
      unfold HIsB at hB
      rcases hB with h | h
      · exact conj_sq_sq_eq_one hz2 h
      · exact conj_sq_sq_eq_one hz12 h
    have hx2ne : (y * c) ^ 2 ≠ 1 := by
      unfold HIsB at hB
      rcases hB with h | h
      · exact conj_ne_one hz_ne h
      · exact conj_ne_one hz1_ne h
    simpa using orderOf_eq_four_of_pow_four_eq_one_of_sq_ne_one hx4 hx2ne
  · simpa using tab4Set_four_spec hc
  · have hx3 : (y * c) ^ 3 = a := tab4Set_five_spec hc
    have hcay : c ≠ a * y := by
      have h := tab4Set_mem_base hc
      simp [tab4Base] at h
      exact h.2.2
    have hy_inv : y⁻¹ = y := by
      have hy_ord : orderOf y = 2 := (isConj_orderOf_eq hy).symm.trans hord.2.2.1
      have hyy : y * y = 1 := by
        have := pow_orderOf_eq_one y
        rw [hy_ord] at this
        simpa [pow_two] using this
      exact inv_eq_of_mul_eq_one_right hyy
    have hx2ne : (y * c) ^ 2 ≠ 1 := by
      intro hx2
      apply hcay
      have hx : y * c = a := by
        calc y * c = (y * c) * ((y * c) ^ 2) := by rw [hx2, mul_one]
          _ = (y * c) ^ 3 := by rw [← pow_succ']
          _ = a := hx3
      calc c = y⁻¹ * (y * c) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = y⁻¹ * a := by rw [hx]
        _ = a * y := by rw [hy_inv, Subgroup.mem_center_iff.mp ha y]
    simpa using orderOf_eq_six_of_cube_eq ha2 ha_ne hx3 hx2ne

private theorem nonempty_mulEquiv_of_mem_conjOrbit {G : Type} [Group G] {K : Subgroup G}
    {S : Set G} (hS : IsConjOrbit K S) {c₀ c' : G} (hc₀ : c₀ ∈ S) (hc' : c' ∈ S)
    {P : Type*} [Group P] (h : Nonempty (↥(K ⊓ Gx c₀) ≃* P)) :
    Nonempty (↥(K ⊓ Gx c') ≃* P) := by
  obtain ⟨k, hk, hkconj⟩ := hS.transitive c₀ hc₀ c' hc'
  obtain ⟨e⟩ := nonempty_mulEquiv_inf_Gx_of_conj (K := K) (k := k) (c := c₀) hk
  rw [hkconj] at e
  obtain ⟨f⟩ := h
  exact ⟨e.trans f⟩

theorem tab4Set_disjoint {G : Type} [Group G] {a z b z₁ y : G} (ha : a ∈ Subgroup.center G)
    (hord : orderOf a = 2 ∧ orderOf z = 2 ∧ orderOf b = 2 ∧ orderOf z₁ = 2)
    (hy : IsConj b y)
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j)) :
    ∀ i j, i ≠ j → Disjoint (tab4Set a z b z₁ y i) (tab4Set a z b z₁ y j) := by
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
          ((orderOf_mul_eq_rowOrd ha hord hy hne_az hci).symm.trans
            (orderOf_mul_eq_rowOrd ha hord hy hne_az hcj)) (by decide)
      | exact not_HIsA_HIsB hnc (tab4Set_zero_spec hci) (tab4Set_one_spec hcj)
      | exact not_HIsA_HIsB hnc (tab4Set_zero_spec hcj) (tab4Set_one_spec hci)
      | exact not_sq_eq_center_of_HIsB hnc (tab4Set_two_spec hci) (tab4Set_three_spec hcj)
      | exact not_sq_eq_center_of_HIsB hnc (tab4Set_two_spec hcj) (tab4Set_three_spec hci)

theorem tableIV_of_reps {G : Type} [Group G] [Finite G] {a z b z₁ y : G}
    (ha : a ∈ Subgroup.center G)
    (hord : orderOf a = 2 ∧ orderOf z = 2 ∧ orderOf b = 2 ∧ orderOf z₁ = 2)
    (hy : IsConj b y)
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (hK : Nat.card ↥(Gx y) = 80640) (hB : (tab4Base a b y).ncard = 2198)
    (c : Fin 6 → G) (hc : ∀ i, c i ∈ tab4Set a z b z₁ y i)
    (hstab : ∀ i, Nat.card ↥(Gx y ⊓ Gx (c i)) = ![768, 768, 1440, 64, 240, 240] i)
    (h4B : IsShapeZ2TimesSym 6 ↥(Gx y ⊓ Gx (c 2)))
    (h3A : IsShapeZ2TimesSym 5 ↥(Gx y ⊓ Gx (c 4)))
    (h6A : IsShapeZ2TimesSym 5 ↥(Gx y ⊓ Gx (c 5))) : TableIVData a z b z₁ y := by
  have hsum : ∑ i : Fin 6,
      Nat.card ↥(Gx y) / (![768, 768, 1440, 64, 240, 240] : Fin 6 → ℕ) i
      = (tab4Base a b y).ncard := by
    rw [hK, hB]
    decide
  obtain ⟨hpart, hstab'⟩ := orbitPartition_of_rows (Gx y) (tab4Base a b y)
      (tab4Set a z b z₁ y) c ![768, 768, 1440, 64, 240, 240]
      (by intro i x hx; fin_cases i <;> (simp [tab4Set] at hx; exact hx.1))
      (fun i j hij => tab4Set_disjoint ha hord hy hnc i j hij)
      (by
        intro i k hk x hx
        have hky : k * y * k⁻¹ = y := by rw [← mem_Gx.mp hk]; group
        have := (mem_tab4Set_conj ha z b z₁ y x k i).mpr hx
        rwa [hky] at this)
      hc hstab hsum
  refine ⟨hpart, hstab', ?_, ?_, ?_⟩
  · intro c' hc'
    exact nonempty_mulEquiv_of_mem_conjOrbit (hS := hpart.orbit 2) (hc₀ := hc 2) hc' h4B
  · intro c' hc'
    exact nonempty_mulEquiv_of_mem_conjOrbit (hS := hpart.orbit 4) (hc₀ := hc 4) hc' h3A
  · intro c' hc'
    exact nonempty_mulEquiv_of_mem_conjOrbit (hS := hpart.orbit 5) (hc₀ := hc 5) hc' h6A

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
