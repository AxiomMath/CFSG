module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {B : Type*} [Group B]

private lemma comm_of_sq_eq_one {x y : B} (hx : x * x = 1) (hy : y * y = 1)
    (h : (x * y) * (x * y) = 1) : x * y = y * x := by
  have h1 : (x * y)⁻¹ = x * y := mul_eq_one_iff_inv_eq.mp h
  rw [mul_inv_rev] at h1
  have hx' : x⁻¹ = x := mul_eq_one_iff_inv_eq.mp hx
  have hy' : y⁻¹ = y := mul_eq_one_iff_inv_eq.mp hy
  rw [hx', hy'] at h1
  exact h1.symm

private lemma sq_eq_of_not_commute {a₁ l₁ : B} (hexp : ∀ x : B, x ^ 4 = 1)
    (ha₁ : a₁ * a₁ = 1) (hl₁ : l₁ * l₁ = 1) (hcomm : a₁ * l₁ = l₁ * a₁)
    (hC : ∀ x : B, x * a₁ = a₁ * x → x = 1 ∨ x = a₁ ∨ x = l₁ ∨ x = a₁ * l₁)
    (hnc : ∀ x : B, x * a₁ * x⁻¹ ≠ l₁) {a₂ : B} (ha₂ : a₂ * a₂ = 1)
    (hna : a₂ * a₁ ≠ a₁ * a₂) : (a₁ * a₂) * (a₁ * a₂) = l₁ := by
  have hainv : a₁⁻¹ = a₁ := mul_eq_one_iff_inv_eq.mp ha₁
  have h2inv : a₂⁻¹ = a₂ := mul_eq_one_iff_inv_eq.mp ha₂
  have hu2 : (a₁ * a₂) * (a₁ * a₂) ≠ 1 := fun h =>
    hna (comm_of_sq_eq_one (x := a₁) (y := a₂) ha₁ ha₂ h).symm
  have hz2 : ((a₁ * a₂) * (a₁ * a₂)) * ((a₁ * a₂) * (a₁ * a₂)) = 1 := by
    rw [← pow_two (a₁ * a₂), ← pow_two ((a₁ * a₂) ^ 2), ← pow_mul]
    exact hexp (a₁ * a₂)
  have hza : a₁ * ((a₁ * a₂) * (a₁ * a₂)) = ((a₁ * a₂) * (a₁ * a₂)) * a₁ := by
    have hau : MulAut.conj a₁ (a₁ * a₂) = (a₁ * a₂)⁻¹ := by
      rw [MulAut.conj_apply, mul_inv_rev, hainv, h2inv]
      rw [← mul_assoc a₁ a₁ a₂, ha₁, one_mul]
    have hconj : MulAut.conj a₁ ((a₁ * a₂) * (a₁ * a₂)) =
        ((a₁ * a₂) * (a₁ * a₂))⁻¹ := by
      rw [map_mul, hau]
      group
    have hz2inv : ((a₁ * a₂) * (a₁ * a₂))⁻¹ = (a₁ * a₂) * (a₁ * a₂) :=
      mul_eq_one_iff_inv_eq.mp hz2
    have hconj' : a₁ * ((a₁ * a₂) * (a₁ * a₂)) * a₁ = (a₁ * a₂) * (a₁ * a₂) := by
      rwa [MulAut.conj_apply, hainv, hz2inv] at hconj
    calc a₁ * ((a₁ * a₂) * (a₁ * a₂))
        = a₁ * ((a₁ * a₂) * (a₁ * a₂)) * a₁ * a₁ := by
          rw [mul_assoc (a₁ * ((a₁ * a₂) * (a₁ * a₂))) a₁ a₁, ha₁, mul_one]
      _ = ((a₁ * a₂) * (a₁ * a₂)) * a₁ := by rw [hconj']
  rcases hC ((a₁ * a₂) * (a₁ * a₂)) hza.symm with h | h | h | h
  · exact absurd h hu2
  · exfalso
    apply hna
    grind
  · exact h
  · exfalso
    exact hnc a₂ (by grind)

private lemma commute_l {a l : B} (hexp : ∀ x : B, x ^ 4 = 1)
    (ha : a * a = 1) (hl : l * l = 1) (ha1 : a ≠ 1) (hl1 : l ≠ 1) (hal : a ≠ l)
    (hcomm : a * l = l * a)
    (hC : ∀ x : B, x * a = a * x → x = 1 ∨ x = a ∨ x = l ∨ x = a * l)
    (hnc : ∀ x : B, x * a * x⁻¹ ≠ l) : ∀ x : B, x * l = l * x := by
  intro x
  have ha'2 : (x*a*x⁻¹)*(x*a*x⁻¹) = 1 := by
    calc (x*a*x⁻¹)*(x*a*x⁻¹) = x*(a*a)*x⁻¹ := by group
      _ = 1 := by rw [ha]; group
  have hl'2 : (x*l*x⁻¹)*(x*l*x⁻¹) = 1 := by
    calc (x*l*x⁻¹)*(x*l*x⁻¹) = x*(l*l)*x⁻¹ := by group
      _ = 1 := by rw [hl]; group
  have hcomm' : (x*a*x⁻¹)*(x*l*x⁻¹) = (x*l*x⁻¹)*(x*a*x⁻¹) := by
    calc (x*a*x⁻¹)*(x*l*x⁻¹) = x*(a*l)*x⁻¹ := by group
      _ = x*(l*a)*x⁻¹ := by rw [hcomm]
      _ = (x*l*x⁻¹)*(x*a*x⁻¹) := by group
  have hC' : ∀ y : B, y*(x*a*x⁻¹) = (x*a*x⁻¹)*y →
      y = 1 ∨ y = x*a*x⁻¹ ∨ y = x*l*x⁻¹ ∨ y = (x*a*x⁻¹)*(x*l*x⁻¹) := by
    intro y hy
    have h1 : (x⁻¹*y*x)*a = a*(x⁻¹*y*x) := by
      calc (x⁻¹*y*x)*a = x⁻¹*(y*(x*a*x⁻¹))*x := by group
        _ = x⁻¹*((x*a*x⁻¹)*y)*x := by rw [hy]
        _ = a*(x⁻¹*y*x) := by group
    rcases hC (x⁻¹*y*x) h1 with h | h | h | h
    · left
      calc y = x*(x⁻¹*y*x)*x⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right; left
      calc y = x*(x⁻¹*y*x)*x⁻¹ := by group
        _ = x*a*x⁻¹ := by rw [h]
    · right; right; left
      calc y = x*(x⁻¹*y*x)*x⁻¹ := by group
        _ = x*l*x⁻¹ := by rw [h]
    · right; right; right
      calc y = x*(x⁻¹*y*x)*x⁻¹ := by group
        _ = (x*a*x⁻¹)*(x*l*x⁻¹) := by rw [h]; group
  have hnc' : ∀ y : B, y*(x*a*x⁻¹)*y⁻¹ ≠ x*l*x⁻¹ := by
    intro y hy
    apply hnc (x⁻¹*y*x)
    calc (x⁻¹*y*x)*a*(x⁻¹*y*x)⁻¹ = x⁻¹*(y*(x*a*x⁻¹)*y⁻¹)*x := by group
      _ = x⁻¹*(x*l*x⁻¹)*x := by rw [hy]
      _ = l := by group
  by_cases hxa : (x*a*x⁻¹)*a = a*(x*a*x⁻¹)
  · rcases hC (x*a*x⁻¹) hxa with h | h | h | h
    · exfalso
      have : a = 1 := by
        calc a = x⁻¹*(x*a*x⁻¹)*x := by group
          _ = 1 := by rw [h]; group
      exact ha1 this
    · have hxE : x*a = a*x := by
        calc x*a = (x*a*x⁻¹)*x := by group
          _ = a*x := by rw [h]
      rcases hC x hxE with hx1 | hx1 | hx1 | hx1
      · rw [hx1]; group
      · rw [hx1]; exact hcomm
      · rw [hx1]
      · rw [hx1]
        calc (a*l)*l = a := by rw [mul_assoc, hl, mul_one]
          _ = l*(a*l) := by rw [hcomm, ← mul_assoc, hl, one_mul]
    · exfalso
      exact hnc x h
    · by_cases hla : a*(x*l*x⁻¹) = (x*l*x⁻¹)*a
      · rcases hC (x*l*x⁻¹) hla.symm with h' | h' | h' | h'
        · exfalso
          have : l = 1 := by
            calc l = x⁻¹*(x*l*x⁻¹)*x := by group
              _ = 1 := by rw [h']; group
          exact hl1 this
        · exfalso
          have : x⁻¹*a*x = l := by
            calc x⁻¹*a*x = x⁻¹*(x*l*x⁻¹)*x := by rw [h']
              _ = l := by group
          exact hnc (x⁻¹) (by simpa using this)
        · calc x*l = x*l*x⁻¹*x := by group
            _ = l*x := by rw [h']
        · exfalso
          have : a = l := by
            calc a = x⁻¹*(x*a*x⁻¹)*x := by group
              _ = x⁻¹*(x*l*x⁻¹)*x := by rw [h, h']
              _ = l := by group
          exact hal this
      · exfalso
        have h1 : (a*(x*l*x⁻¹))*(a*(x*l*x⁻¹)) = l :=
          sq_eq_of_not_commute hexp ha hl hcomm hC hnc hl'2 (fun hh => hla hh.symm)
        have h2' : (a*l)*(x*l*x⁻¹) = (x*l*x⁻¹)*(a*l) := by
          rw [← h]
          exact hcomm'
        have e1 : (x*l*x⁻¹)*a = a*l*(x*l*x⁻¹) := by
          have e : (x*l*x⁻¹)*a*(x*l*x⁻¹) = a*l := by
            calc (x*l*x⁻¹)*a*(x*l*x⁻¹)
                = (a*a)*((x*l*x⁻¹)*a*(x*l*x⁻¹)) := by rw [ha, one_mul]
              _ = a*((a*(x*l*x⁻¹))*(a*(x*l*x⁻¹))) := by group
              _ = a*l := by rw [h1]
          calc (x*l*x⁻¹)*a = (x*l*x⁻¹)*a*(x*l*x⁻¹)*(x*l*x⁻¹) := by
                rw [show (x*l*x⁻¹)*a*(x*l*x⁻¹)*(x*l*x⁻¹)
                    = (x*l*x⁻¹)*a*((x*l*x⁻¹)*(x*l*x⁻¹)) by group, hl'2, mul_one]
            _ = (a*l)*(x*l*x⁻¹) := by rw [e]
        have e2 : a*l*(x*l*x⁻¹) = (x*l*x⁻¹)*a*l := by
          calc a*l*(x*l*x⁻¹) = (a*l)*(x*l*x⁻¹) := by group
            _ = (x*l*x⁻¹)*(a*l) := h2'
            _ = (x*l*x⁻¹)*a*l := by group
        have hae : a = a*l := by
          have hcancel : (x*l*x⁻¹)*a = (x*l*x⁻¹)*(a*l) := by
            rw [e1, e2, mul_assoc]
          exact mul_left_cancel hcancel
        have hl1' : l = 1 := by
          calc l = a*(a*l) := by rw [← mul_assoc, ha, one_mul]
            _ = a*a := by rw [← hae]
            _ = 1 := ha
        exact hl1 hl1'
  · have h1 : (a*(x*a*x⁻¹))*(a*(x*a*x⁻¹)) = l :=
      sq_eq_of_not_commute hexp ha hl hcomm hC hnc ha'2 hxa
    have h2 : ((x*a*x⁻¹)*a)*((x*a*x⁻¹)*a) = x*l*x⁻¹ :=
      sq_eq_of_not_commute hexp ha'2 hl'2 hcomm' hC' hnc' ha (fun hh => hxa hh.symm)
    have hlinv : l⁻¹ = l := mul_eq_one_iff_inv_eq.mp hl
    calc x*l = x*l*x⁻¹*x := by group
      _ = l*x := by
        have : x*l*x⁻¹ = l := by
          rw [← h2]
          have hvinv : (x*a*x⁻¹)⁻¹ = x*a*x⁻¹ := mul_eq_one_iff_inv_eq.mp ha'2
          have hainv' : a⁻¹ = a := mul_eq_one_iff_inv_eq.mp ha
          calc ((x*a*x⁻¹)*a)*((x*a*x⁻¹)*a)
              = ((a*(x*a*x⁻¹))*(a*(x*a*x⁻¹)))⁻¹ := by
                rw [mul_inv_rev, mul_inv_rev, hainv', hvinv]
            _ = l⁻¹ := by rw [h1]
            _ = l := hlinv
        rw [this]

private lemma mem_closure_pair_iff' {a l x : B} (ha : a * a = 1) (hl : l * l = 1)
    (hcomm : a * l = l * a) :
    x ∈ Subgroup.closure ({a, l} : Set B) ↔ x = 1 ∨ x = a ∨ x = l ∨ x = a * l := by
  have ha' : ∀ y, a * (a * y) = y := fun y => by rw [← mul_assoc, ha, one_mul]
  have hla : ∀ y, l * (a * y) = a * (l * y) := fun y => by rw [← mul_assoc, ← hcomm, mul_assoc]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hli : l⁻¹ = l := inv_eq_of_mul_eq_one_right hl
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, ha, hl, ha', hla, hcomm.symm, mul_one, one_mul, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hai, hli, mul_inv_rev, hcomm.symm, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

private lemma mem_zpowers_of_sq_eq_one {g x : B} (hg : g * g = 1) :
    x ∈ Subgroup.zpowers g → x = 1 ∨ x = g := by
  rw [Subgroup.zpowers_eq_closure]
  refine Subgroup.closure_induction (p := fun x _ => x = 1 ∨ x = g) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact Or.inr hy
  · exact Or.inl rfl
  · intro x y _ _ hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left; rw [hx, hy, one_mul]
    · right; rw [hx, hy, one_mul]
    · right; rw [hx, hy, mul_one]
    · left; rw [hx, hy, hg]
  · intro x _ hx
    rcases hx with hx | hx
    · left; rw [hx, inv_one]
    · right; rw [hx, mul_eq_one_iff_inv_eq.mp hg]

private lemma zpowers_order_four_inv [Finite B] {c l : B} (hc2 : c * c = l) (hl : l * l = 1)
    (hl1 : l ≠ 1) (hc4 : (c*c)*(c*c) = 1) :
    ∀ x, x ∈ Subgroup.zpowers c → x*x = 1 → x = 1 ∨ x = l := by
  classical
  have hc4' : c^4 = 1 := by
    rw [show c^4 = (c*c)*(c*c) by rw [← pow_two c, ← pow_two (c^2), ← pow_mul]]
    exact hc4
  have hc1 : c ≠ 1 := by
    intro h; rw [h] at hc2; exact hl1 (by simpa using hc2.symm)
  have hc5 : c^2 ≠ 1 := by
    intro h; rw [pow_two, hc2] at h; exact hl1 h
  have hc3 : c^3 ≠ 1 := by
    intro h
    have : c = 1 := by
      calc c = c^4 * (c^3)⁻¹ := by group
        _ = 1 := by rw [hc4', h, inv_one, mul_one]
    exact hc1 this
  have hord : orderOf c = 4 := (orderOf_eq_iff (n := 4) (by norm_num)).mpr ⟨hc4', by
    intro m hm hm0
    interval_cases m
    · simpa using hc1
    · exact hc5
    · exact hc3⟩
  intro x hx hx2
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range] at hi
  interval_cases i
  · left; exact pow_zero c
  · exfalso
    have hcc : c * c = 1 := by simpa using hx2
    exact hc5 (by rw [pow_two]; exact hcc)
  · right; simpa [pow_two] using hc2
  · exfalso
    have h33 : c^3 * c^3 = 1 := hx2
    have h6 : c^6 = 1 := by rw [← pow_add] at h33; exact h33
    have h66 : c^6 = c^4 * c^2 := by rw [← pow_add]
    rw [h66, hc4', one_mul] at h6
    exact hc5 h6


private lemma mul_a_eq_of_conj {a c l : B} (hc : c*a*c⁻¹ = a*l) : c*a = a*l*c := by
  calc c*a = (c*a*c⁻¹)*c := by group
    _ = (a*l)*c := by rw [hc]

private lemma a_mul_conj_inv {a c l : B} (ha : a*a = 1) (hl : l*l = 1)
    (hc2 : c*c = l) (hc : c*a*c⁻¹ = a*l) : a*c*a = c⁻¹ := by
  have hca : c*a = a*l*c := mul_a_eq_of_conj hc
  have hcinv : c⁻¹ = l*c := by
    have h1 : c⁻¹*c = 1 := inv_mul_cancel c
    have h2 : (l*c)*c = 1 := by rw [mul_assoc, hc2, hl]
    exact mul_right_cancel (h1.trans h2.symm)
  calc a*c*a = a*(c*a) := by rw [mul_assoc]
    _ = a*(a*l*c) := by rw [hca]
    _ = (a*a)*(l*c) := by group
    _ = l*c := by rw [ha, one_mul]
    _ = c⁻¹ := hcinv.symm


private lemma conj_zpow_of_conj {a c : B} (ha : a * a = 1) (hac : a * c * a = c⁻¹) (k : ℤ) :
    a * c^k * a = c^(-k) := by
  have hai : a⁻¹ = a := mul_eq_one_iff_inv_eq.mp ha
  have h1 : (a * c * a⁻¹)^k = a * c^k * a⁻¹ := conj_zpow
  rw [hai, hac, inv_zpow] at h1
  exact h1.symm.trans (zpow_neg c k).symm

private lemma mem_dih_iff {a c x : B} (ha : a * a = 1) (hac : a * c * a = c⁻¹) :
    x ∈ Subgroup.closure ({a, c} : Set B) ↔ (∃ k : ℤ, x = c^k) ∨ (∃ k : ℤ, x = a*c^k) := by
  have hconj := conj_zpow_of_conj ha hac
  have hca : ∀ i : ℤ, c^i * a = a * c^(-i) := by
    intro i
    have h : a * (c^i * a) = a * (a * c^(-i)) := by
      calc a * (c^i * a) = (a * c^i) * a := by group
        _ = c^(-i) := hconj i
        _ = a * (a * c^(-i)) := by rw [← mul_assoc, ha, one_mul]
    exact mul_left_cancel h
  have haD : a ∈ Subgroup.closure ({a, c} : Set B) := Subgroup.subset_closure (by simp)
  have hcD : c ∈ Subgroup.closure ({a, c} : Set B) := Subgroup.subset_closure (by simp)
  have hle : Subgroup.zpowers c ≤ Subgroup.closure ({a, c} : Set B) :=
    Subgroup.zpowers_le.mpr hcD
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · right; exact ⟨0, by rw [zpow_zero, mul_one]⟩
      · left; exact ⟨1, by rw [zpow_one]⟩
    | one => left; exact ⟨0, by rw [zpow_zero]⟩
    | mul x y _ _ hx hy =>
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left; refine ⟨i+j, ?_⟩; rw [zpow_add]
      · right; refine ⟨j-i, ?_⟩
        rw [← mul_assoc (c^i) a (c^j), hca i, mul_assoc, ← zpow_add,
            show -i + j = j - i by ring]
      · right; refine ⟨i+j, ?_⟩; rw [mul_assoc, zpow_add]
      · left; refine ⟨j-i, ?_⟩
        rw [mul_assoc a (c^i) (a*c^j), ← mul_assoc (c^i) a (c^j), hca i,
            mul_assoc a (c^(-i)) (c^j), ← mul_assoc a a (c^(-i)*c^j), ha, one_mul,
            ← zpow_add, show -i + j = j - i by ring]
    | inv x _ hx =>
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · left; refine ⟨-i, ?_⟩; exact (zpow_neg c i).symm
      · right; refine ⟨i, ?_⟩
        rw [mul_inv_rev, mul_eq_one_iff_inv_eq.mp ha, ← zpow_neg, hca (-i)]
        simp
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact hle (Subgroup.zpow_mem_zpowers c k)
    · exact mul_mem haD (hle (Subgroup.zpow_mem_zpowers c k))

private lemma zpow_even_mem {c l : B} (hc2 : c * c = l) (hl : l * l = 1) {k : ℤ}
    (hk : Even k) : c^k = 1 ∨ c^k = l := by
  obtain ⟨m, hm⟩ := hk
  have hc2z : c ^ (2:ℤ) = l := by rw [zpow_ofNat, pow_two]; exact hc2
  rw [hm, show m + m = 2 * m by ring, zpow_mul, hc2z]
  exact mem_zpowers_of_sq_eq_one hl (Subgroup.zpow_mem_zpowers l m)

private lemma zpow_odd_sq {c l : B} (hc4 : c^4 = 1) (hc2 : c * c = l) (hl : l * l = 1)
    {k : ℤ} (hk : Odd k) : (c^k)*(c^k) = l := by
  rw [← zpow_add, show k + k = 2 * k by ring]
  obtain ⟨m, hm⟩ := hk
  have hc4z : c ^ (4:ℤ) = 1 := by rw [zpow_ofNat]; exact hc4
  have hc2z : c ^ (2:ℤ) = l := by rw [zpow_ofNat, pow_two]; exact hc2
  rw [hm, show 2*(2*m+1) = 4*m + 2 by ring, zpow_add, zpow_mul,
      hc4z, one_zpow, one_mul, hc2z]

private lemma zpow_odd_ne_one {c l : B} (hc4 : c^4 = 1) (hc2 : c * c = l) (hl : l * l = 1)
    (hl1 : l ≠ 1) {k : ℤ} (hk : Odd k) : c^k ≠ 1 := by
  intro h
  have := zpow_odd_sq hc4 hc2 hl hk
  rw [h, one_mul] at this
  exact hl1 this.symm

theorem exists_index_two_of_four_centralizer {B : Type*} [Group B] [Finite B]
    (hB : IsPGroup 2 B) (hexp : ∀ x : B, x ^ 4 = 1) {a l : B} (ha : a ^ 2 = 1) (hl : l ^ 2 = 1)
    (ha1 : a ≠ 1) (hl1 : l ≠ 1) (hal : a ≠ l) (hcomm : a * l = l * a)
    (hC : ∀ x : B, x * a = a * x → x = 1 ∨ x = a ∨ x = l ∨ x = a * l)
    (hnc : ∀ x : B, x * a * x⁻¹ ≠ l) :
    ∃ N : Subgroup B, N.index = 2 ∧ a ∉ N ∧ ∀ x ∈ N, x ^ 2 = 1 → x = 1 ∨ x = l := by
  classical
  have ha' : a * a = 1 := by simpa [pow_two] using ha
  have hl' : l * l = 1 := by simpa [pow_two] using hl
  have hlc : ∀ x : B, x * l = l * x := commute_l hexp ha' hl' ha1 hl1 hal hcomm hC hnc
  let E : Subgroup B := Subgroup.closure ({a, l} : Set B)
  have hEmem : ∀ x : B, x ∈ E ↔ x = 1 ∨ x = a ∨ x = l ∨ x = a * l :=
    fun x => mem_closure_pair_iff' ha' hl' hcomm (x := x)
  by_cases hEt : E = ⊤
  · refine ⟨Subgroup.zpowers l, ?_, ?_, ?_⟩
    · rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      refine ⟨a, ?_, ?_⟩
      · intro hmem
        rcases mem_zpowers_of_sq_eq_one hl' hmem with h | h
        · exact ha1 h
        · exact hal h
      · intro b
        have hbE : b ∈ E := by rw [hEt]; trivial
        rcases (hEmem b).mp hbE with h | h | h | h
        · right; rw [h]; exact Subgroup.one_mem _
        · left; rw [h, ha']; exact Subgroup.one_mem _
        · right; rw [h]; exact Subgroup.mem_zpowers l
        · left
          have : (a*l)*a = l := by rw [hcomm, mul_assoc, ha', mul_one]
          rw [h, this]
          exact Subgroup.mem_zpowers l
    · intro hmem
      rcases mem_zpowers_of_sq_eq_one hl' hmem with h | h
      · exact ha1 h
      · exact hal h
    · intro x hx hx2
      exact mem_zpowers_of_sq_eq_one (g := l) hl' hx
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent B := IsPGroup.isNilpotent (p := 2) hB
    have hncB : NormalizerCondition B := Group.normalizerCondition_of_isNilpotent
    have hEne : E ≠ Subgroup.normalizer E := by
      intro h
      exact hEt ((normalizerCondition_iff_only_full_group_self_normalizing.mp hncB E) h.symm)
    obtain ⟨c, hcN, hcE⟩ := SetLike.exists_of_lt (lt_of_le_of_ne le_normalizer hEne)
    have haE : a ∈ E := subset_closure (by simp)
    have hca_mem : c*a*c⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hcN a).mp haE
    have hca' : c*a*c⁻¹ = a*l := by
      rcases (hEmem (c*a*c⁻¹)).mp hca_mem with h | h | h | h
      · exfalso
        have : a = 1 := by
          calc a = c⁻¹*(c*a*c⁻¹)*c := by group
            _ = 1 := by rw [h]; group
        exact ha1 this
      · exfalso
        apply hcE
        have hcomm_ca : c*a = a*c := by
          calc c*a = (c*a*c⁻¹)*c := by group
            _ = a*c := by rw [h]
        exact (hEmem c).mpr (hC c hcomm_ca)
      · exfalso
        exact hnc c h
      · exact h
    have hcl' : c*l*c⁻¹ = l := by
      rw [hlc c]; group
    have hc2E : c*c ∈ E := by
      have hca2a : c*c*a*(c*c)⁻¹ = a := by
        calc c*c*a*(c*c)⁻¹ = c*(c*a*c⁻¹)*c⁻¹ := by group
          _ = c*(a*l)*c⁻¹ := by rw [hca']
          _ = (c*a*c⁻¹)*(c*l*c⁻¹) := by group
          _ = (a*l)*l := by rw [hca', hcl']
          _ = a := by rw [mul_assoc, hl', mul_one]
      have hcomm2 : (c*c)*a = a*(c*c) := by
        calc (c*c)*a = (c*c*a*(c*c)⁻¹)*(c*c) := by group
          _ = a*(c*c) := by rw [hca2a]
      exact (hEmem (c*c)).mpr (hC (c*c) hcomm2)
    have hc2 : c*c = 1 ∨ c*c = l := by
      rcases (hEmem (c*c)).mp hc2E with h | h | h | h
      · exact Or.inl h
      · exfalso
        have hcomm_ca : c*a = a*c := by
          rw [← h]; group
        exact hcE ((hEmem c).mpr (hC c hcomm_ca))
      · exact Or.inr h
      · exfalso
        have hae : a = a*l := by
          calc a = c⁻¹*(c*a*c⁻¹)*c := by group
            _ = c⁻¹*(a*l)*c := by rw [hca']
            _ = c⁻¹*(c*c)*c := by rw [← h]
            _ = c*c := by group
            _ = a*l := h
        have hl1' : l = 1 := by
          calc l = a*(a*l) := by rw [← mul_assoc, ha', one_mul]
            _ = a*a := by rw [← hae]
            _ = 1 := ha'
        exact hl1 hl1'
    set c' : B := if c*c = l then c else c*a with hc'def
    have hc'2 : c'*c' = l := by
      rw [hc'def]
      by_cases hcc : c*c = l
      · simp only [if_pos hcc]; exact hcc
      · have hc1 : c*c = 1 := by rcases hc2 with h | h; exact h; exact absurd h hcc
        simp only [if_neg hcc]
        calc (c*a)*(c*a) = (c*a*c⁻¹)*(c*c)*a := by group
          _ = (a*l)*(c*c)*a := by rw [hca']
          _ = (a*l)*1*a := by rw [hc1]
          _ = l := by rw [mul_one, hcomm, mul_assoc, ha', mul_one]
    have hc'a_conj : c'*a*c'⁻¹ = a*l := by
      rw [hc'def]
      by_cases hcc : c*c = l
      · simp only [if_pos hcc]; exact hca'
      · simp only [if_neg hcc]
        calc (c*a)*a*(c*a)⁻¹ = c*a*c⁻¹ := by group
          _ = a*l := hca'
    have hc'a_inv : a*c'*a = c'⁻¹ := a_mul_conj_inv ha' hl' hc'2 hc'a_conj
    let D : Subgroup B := Subgroup.closure ({a, c'} : Set B)
    have hc4 : c'^4 = 1 := by
      rw [show c'^4 = (c'*c')*(c'*c') by rw [← pow_two c', ← pow_two (c'^2), ← pow_mul],
          hc'2, hl']
    have hconjz : ∀ i : ℤ, a * c'^i * a = c'^(-i) := conj_zpow_of_conj ha' hc'a_inv
    have hca_z : ∀ i : ℤ, c'^i * a = a * c'^(-i) := by
      intro i
      calc c'^i * a = a * (a * c'^i * a) := by
            rw [show a * (a*c'^i*a) = c'^i*a by
                  rw [mul_assoc a (c'^i) a, ← mul_assoc a a (c'^i*a), ha', one_mul]]
        _ = a * c'^(-i) := by rw [hconjz i]
    have hac'_ne : a*c' ≠ c'*a := by
      intro hh
      have hca := mul_a_eq_of_conj hc'a_conj
      rw [hca] at hh
      have h2 : c' = l*c' := by
        have := congrArg (fun z => a⁻¹ * z) hh
        simpa [mul_assoc] using this
      have h3 : 1 = l := by
        have := congrArg (fun z => z * c'⁻¹) h2
        simpa [mul_assoc] using this
      exact hl1 h3.symm
    have hc'D : c' ∈ D := Subgroup.subset_closure (by simp)
    have hlD : l ∈ D := by rw [← hc'2]; exact mul_mem hc'D hc'D
    have hED : E ≤ D := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact hlD
    have hDmem : ∀ x : B, x ∈ D ↔ (∃ k : ℤ, x = c'^k) ∨ (∃ k : ℤ, x = a*c'^k) :=
      fun x => mem_dih_iff ha' hc'a_inv (x := x)
    have hDtop : D = ⊤ := by
      by_contra hDne
      have hDne' : D ≠ Subgroup.normalizer D := by
        intro h
        exact hDne ((normalizerCondition_iff_only_full_group_self_normalizing.mp hncB D) h.symm)
      obtain ⟨e, heN, heD⟩ := SetLike.exists_of_lt (lt_of_le_of_ne le_normalizer hDne')
      have haD : a ∈ D := Subgroup.subset_closure (by simp)
      have hpaD : e*a*e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp heN a).mp haD
      have hpcD : e*c'*e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp heN c').mp hc'D
      have hpa_sq : (e*a*e⁻¹)*(e*a*e⁻¹) = 1 := by
        calc (e*a*e⁻¹)*(e*a*e⁻¹) = e*(a*a)*e⁻¹ := by group
          _ = 1 := by rw [ha']; group
      rcases (hDmem (e*a*e⁻¹)).mp hpaD with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hkk : c'^k * c'^k = 1 := by rw [← hk]; exact hpa_sq
        have hck : c'^(-k) = c'^k := by
          rw [zpow_neg]
          exact mul_eq_one_iff_inv_eq.mp hkk
        have hcomm : (e*a*e⁻¹)*(e*c'*e⁻¹) = (e*c'*e⁻¹)*(e*a*e⁻¹) := by
          rcases (hDmem (e*c'*e⁻¹)).mp hpcD with ⟨j, hj⟩ | ⟨j, hj⟩
          · rw [hk, hj, ← zpow_add, ← zpow_add, add_comm]
          · rw [hk, hj]
            calc c'^k*(a*c'^j) = (c'^k*a)*c'^j := by group
              _ = (a*c'^(-k))*c'^j := by rw [hca_z k]
              _ = a*(c'^(-k)*c'^j) := by group
              _ = a*(c'^k*c'^j) := by rw [hck]
              _ = a*c'^(k+j) := by rw [zpow_add]
              _ = a*(c'^j*c'^k) := by rw [add_comm, zpow_add]
              _ = (a*c'^j)*c'^k := by group
        have hcomm_ac' : a*c' = c'*a := by
          have h1 : e*(a*c')*e⁻¹ = e*(c'*a)*e⁻¹ := by
            calc e*(a*c')*e⁻¹ = (e*a*e⁻¹)*(e*c'*e⁻¹) := by group
              _ = (e*c'*e⁻¹)*(e*a*e⁻¹) := hcomm
              _ = e*(c'*a)*e⁻¹ := by group
          have := congrArg (fun z => e⁻¹*z*e) h1
          simpa [mul_assoc] using this
        exact hac'_ne hcomm_ac'
      · have hkcase : Odd k := by
          rcases Int.even_or_odd k with hke | hko
          · exfalso
            obtain ⟨m, hm⟩ := hke
            have hcm : c'^(m+m) = l^m := by
              have hc'2z : c' ^ (2:ℤ) = l := by rw [zpow_ofNat, pow_two]; exact hc'2
              rw [show m+m = 2*m by ring, zpow_mul, hc'2z]
            have hlm : l^m = 1 ∨ l^m = l :=
              mem_zpowers_of_sq_eq_one hl' (Subgroup.zpow_mem_zpowers l m)
            rw [hm] at hk
            rcases hlm with hlm | hlm
            · have hpa_a : e*a*e⁻¹ = a := by rw [hk, hcm, hlm, mul_one]
              have hcomm_ea : e*a = a*e := by
                calc e*a = (e*a*e⁻¹)*e := by group
                  _ = a*e := by rw [hpa_a]
              exact heD (hED ((hEmem e).mpr (hC e hcomm_ea)))
            · have hpa_al : e*a*e⁻¹ = a*l := by rw [hk, hcm, hlm]
              have hceE : c'⁻¹*e ∈ E := by
                apply (hEmem (c'⁻¹*e)).mpr
                apply hC
                calc (c'⁻¹*e)*a = c'⁻¹*(e*a*e⁻¹)*e := by group
                  _ = c'⁻¹*(c'*a*c'⁻¹)*e := by rw [hpa_al, ← hc'a_conj]
                  _ = a*(c'⁻¹*e) := by group
              have heq : e = c'*(c'⁻¹*e) := by group
              exact heD (by rw [heq]; exact mul_mem hc'D (hED hceE))
          · exact hko
        have hkk_l : c'^k * c'^k = l := zpow_odd_sq hc4 hc'2 hl' hkcase
        rcases (hDmem (e*c'*e⁻¹)).mp hpcD with ⟨j, hj⟩ | ⟨j, hj⟩
        · have hpc_sq : (e*c'*e⁻¹)*(e*c'*e⁻¹) = l := by
            calc (e*c'*e⁻¹)*(e*c'*e⁻¹) = e*(c'*c')*e⁻¹ := by group
              _ = e*l*e⁻¹ := by rw [hc'2]
              _ = l := by rw [hlc e]; group
          have hjodd : Odd j := by
            rcases Int.even_or_odd j with hje | hjo
            · exfalso
              obtain ⟨m, hm⟩ := hje
              have hc4z : c'^(4:ℤ) = 1 := by rw [zpow_ofNat]; exact hc4
              have h2j : c'^(2*j) = 1 := by
                rw [hm, show 2*(m+m) = 4*m by ring, zpow_mul, hc4z, one_zpow]
              have h2jl : c'^(2*j) = l := by
                have h := hpc_sq
                rw [hj] at h
                rw [show c'^j * c'^j = c'^(2*j) by
                      rw [show 2*j = j+j by ring, zpow_add]] at h
                exact h
              rw [h2j] at h2jl
              exact hl1 h2jl.symm
            · exact hjo
          have he2D : e^2 ∈ D := by
            have hphi2a : e^2*a*(e^2)⁻¹ = a*c'^(k*(1+j)) := by
              calc e^2*a*(e^2)⁻¹ = e*(e*a*e⁻¹)*e⁻¹ := by rw [pow_two]; group
                _ = e*(a*c'^k)*e⁻¹ := by rw [hk]
                _ = (e*a*e⁻¹)*(e*c'^k*e⁻¹) := by group
                _ = (a*c'^k)*((e*c'*e⁻¹)^k) := by rw [hk, ← conj_zpow]
                _ = (a*c'^k)*(c'^j)^k := by rw [hj]
                _ = a*c'^(k*(1+j)) := by
                  rw [← zpow_mul, mul_assoc, ← zpow_add]
                  congr 1
                  ring
            have hkeven2 : Even (k*(1+j)) := by
              obtain ⟨t, ht⟩ := hjodd
              exact ⟨k*(t+1), by rw [ht]; ring⟩
            rcases zpow_even_mem hc'2 hl' hkeven2 with hm1 | hm1
            · have hcomm : e^2*a = a*e^2 := by
                calc e^2*a = (e^2*a*(e^2)⁻¹)*e^2 := by rw [pow_two]; group
                  _ = (a*c'^(k*(1+j)))*e^2 := by rw [hphi2a]
                  _ = a*e^2 := by rw [hm1, mul_one]
              exact hED ((hEmem (e^2)).mpr (hC (e^2) hcomm))
            · have hce : c'⁻¹*e^2 ∈ E := by
                apply (hEmem (c'⁻¹*e^2)).mpr
                apply hC
                calc (c'⁻¹*e^2)*a = c'⁻¹*(e^2*a*(e^2)⁻¹)*e^2 := by rw [pow_two]; group
                  _ = c'⁻¹*(a*c'^(k*(1+j)))*e^2 := by rw [hphi2a]
                  _ = c'⁻¹*(a*l)*e^2 := by rw [hm1]
                  _ = a*(c'⁻¹*e^2) := by
                    have hcl : c'⁻¹*(a*l) = a*c'⁻¹ := by
                      calc c'⁻¹*(a*l) = c'⁻¹*(c'*a*c'⁻¹) := by rw [← hc'a_conj]
                        _ = a*c'⁻¹ := by group
                    rw [hcl]; group
              have heq : e^2 = c'*(c'⁻¹*e^2) := by group
              rw [heq]
              exact mul_mem hc'D (hED hce)
          have he2sq : (e^2)*(e^2) = 1 := by
            rw [← pow_two (e^2), ← pow_mul]
            exact hexp e
          rcases (hDmem (e^2)).mp he2D with ⟨m, hm⟩ | ⟨m, hm⟩
          · have hmeven : Even m := by
              rcases Int.even_or_odd m with hme | hmo
              · exact hme
              · exfalso
                have h2m1 : c'^(2*m) = 1 := by
                  have h := he2sq
                  rw [hm] at h
                  rw [show c'^m * c'^m = c'^(2*m) by
                        rw [show 2*m = m+m by ring, zpow_add]] at h
                  exact h
                have h2ml : c'^(2*m) = l := by
                  rw [show 2*m = m+m by ring, zpow_add]
                  exact zpow_odd_sq hc4 hc'2 hl' hmo
                rw [h2ml] at h2m1
                exact hl1 h2m1
            have he2val : e^2 = 1 ∨ e^2 = l := by
              rw [hm]
              exact zpow_even_mem hc'2 hl' hmeven
            have hfa : (e*a)*(e*a) = (e*a*e⁻¹)*e^2*a := by rw [pow_two]; group
            have hf2 : (e*a)*(e*a) = c'^(-k) ∨ (e*a)*(e*a) = c'^(-k)*l := by
              rw [hk] at hfa
              rcases he2val with hv | hv
              · left
                rw [hv, mul_one] at hfa
                rw [hfa, hconjz k]
              · right
                rw [hv] at hfa
                rw [hfa]
                calc (a*c'^k)*l*a = a*c'^k*(l*a) := by group
                  _ = a*c'^k*(a*l) := by rw [← hlc a]
                  _ = (a*c'^k*a)*l := by group
                  _ = c'^(-k)*l := by rw [hconjz k]
            have hf4 : ((e*a)*(e*a))*((e*a)*(e*a)) = l := by
              rcases hf2 with hf2 | hf2
              · rw [hf2]
                calc (c'^(-k))*(c'^(-k)) = ((c'^k)*(c'^k))⁻¹ := by
                      rw [show c'^(-k) = (c'^k)⁻¹ by rw [zpow_neg]]; group
                  _ = l := by rw [hkk_l, mul_eq_one_iff_inv_eq.mp hl']
              · rw [hf2]
                calc (c'^(-k)*l)*(c'^(-k)*l) = ((c'^k)*(c'^k))⁻¹*(l*l) := by
                      rw [show c'^(-k) = (c'^k)⁻¹ by rw [zpow_neg]]
                      calc ((c'^k)⁻¹*l)*((c'^k)⁻¹*l)
                            = (c'^k)⁻¹*(l*(c'^k)⁻¹)*l := by group
                        _ = (c'^k)⁻¹*((c'^k)⁻¹*l)*l := by rw [← hlc (c'^k)⁻¹]
                        _ = ((c'^k)*(c'^k))⁻¹*(l*l) := by
                              rw [show ((c'^k)*(c'^k))⁻¹ = (c'^k)⁻¹*(c'^k)⁻¹ by group]
                              group
                  _ = l := by
                    rw [hkk_l]
                    rw [mul_eq_one_iff_inv_eq.mp hl', hl', mul_one]
            have hf4' : ((e*a)*(e*a))*((e*a)*(e*a)) = 1 := by
              rw [← pow_two (e*a), ← pow_two ((e*a)^2), ← pow_mul]
              exact hexp (e*a)
            rw [hf4] at hf4'
            exact hl1 hf4'
          · have he2comm : e*e^2*e⁻¹ = e^2 := by rw [pow_two]; group
            rw [hm] at he2comm
            have hphi_e2 : e*(a*c'^m)*e⁻¹ = a*c'^(k+j*m) := by
              calc e*(a*c'^m)*e⁻¹ = (e*a*e⁻¹)*(e*c'^m*e⁻¹) := by group
                _ = (a*c'^k)*((e*c'*e⁻¹)^m) := by rw [hk, ← conj_zpow]
                _ = (a*c'^k)*(c'^j)^m := by rw [hj]
                _ = a*c'^(k+j*m) := by
                  rw [← zpow_mul, mul_assoc, ← zpow_add]
            have hc_eq : c'^(k+j*m) = c'^m := by
              apply mul_left_cancel (a := a)
              rw [← hphi_e2, he2comm]
            have hzero : c'^(k+j*m-m) = 1 := by
              have h := congrArg (fun z => z * c'^(-m)) hc_eq
              rw [show c'^m * c'^(-m) = 1 by
                    rw [← zpow_add, add_neg_cancel, zpow_zero]] at h
              rw [show k+j*m-m = k+j*m + -m by ring, zpow_add]
              exact h
            have hodd2 : Odd (k+j*m-m) := by
              obtain ⟨t, ht⟩ := hkcase
              obtain ⟨s, hs⟩ := hjodd
              exact ⟨t+s*m, by rw [ht, hs]; ring⟩
            exact zpow_odd_ne_one hc4 hc'2 hl' hl1 hodd2 hzero
        · exfalso
          have hpc_sq : (e*c'*e⁻¹)*(e*c'*e⁻¹) = l := by
            calc (e*c'*e⁻¹)*(e*c'*e⁻¹) = e*(c'*c')*e⁻¹ := by group
              _ = e*l*e⁻¹ := by rw [hc'2]
              _ = l := by rw [hlc e]; group
          have hjasq : (a*c'^j)*(a*c'^j) = 1 := by
            calc (a*c'^j)*(a*c'^j) = (a*c'^j*a)*c'^j := by group
              _ = c'^(-j)*c'^j := by rw [hconjz j]
              _ = 1 := by rw [← zpow_add, neg_add_cancel, zpow_zero]
          rw [hj, hjasq] at hpc_sq
          exact hl1 hpc_sq.symm
    refine ⟨Subgroup.zpowers c', ?_, ?_, ?_⟩
    · rw [Subgroup.index_eq_two_iff_exists_notMem_and]
      refine ⟨a, ?_, ?_⟩
      · intro hmem
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        have hcomm_ac' : a * c' = c' * a := by
          rw [← hk]
          calc c'^k * c' = c'^(k+1) := by rw [zpow_add_one]
            _ = c'^(1+k) := by rw [add_comm]
            _ = c' * c'^k := by rw [zpow_one_add]
        have hac' : a*c' = c'⁻¹*a := by
          calc a*c' = (a*c'*a)*a := by rw [mul_assoc (a*c') a a, ha', mul_one]
            _ = c'⁻¹*a := by rw [hc'a_inv]
        have hcinv : c' = c'⁻¹ := mul_right_cancel (by rw [← hcomm_ac', hac'])
        have : c'*c' = 1 := mul_eq_one_iff_inv_eq.mpr hcinv.symm
        rw [hc'2] at this
        exact hl1 this
      · intro b
        have hbD : b ∈ D := by rw [hDtop]; trivial
        rcases (hDmem b).mp hbD with ⟨k, hk⟩ | ⟨k, hk⟩
        · right; rw [hk]; exact Subgroup.zpow_mem_zpowers c' k
        · left
          have hba : (a*c'^k)*a = c'^(-k) := by
            calc (a*c'^k)*a = a*c'^k*a := by rw [mul_assoc]
              _ = c'^(-k) := hconjz k
          rw [hk, hba, show c'^(-k) = (c'^k)⁻¹ by rw [zpow_neg]]
          exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers c' k)
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hcomm_ac' : a * c' = c' * a := by
        rw [← hk]
        calc c'^k * c' = c'^(k+1) := by rw [zpow_add_one]
          _ = c'^(1+k) := by rw [add_comm]
          _ = c' * c'^k := by rw [zpow_one_add]
      have hac' : a*c' = c'⁻¹*a := by
        calc a*c' = (a*c'*a)*a := by rw [mul_assoc (a*c') a a, ha', mul_one]
          _ = c'⁻¹*a := by rw [hc'a_inv]
      have hcinv : c' = c'⁻¹ := mul_right_cancel (by rw [← hcomm_ac', hac'])
      have : c'*c' = 1 := mul_eq_one_iff_inv_eq.mpr hcinv.symm
      rw [hc'2] at this
      exact hl1 this
    · intro x hx hx2
      exact zpowers_order_four_inv hc'2 hl' hl1 (by rw [hc'2, hl']) x hx
        (by simpa [pow_two] using hx2)


end CFSG.OddStandard.SmallF3.HarrisU33.S4B

end
