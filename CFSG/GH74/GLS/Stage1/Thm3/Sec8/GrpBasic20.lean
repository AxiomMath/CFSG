module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

theorem not_normalize_cyclic {G : Type*} [Group G] {A V : Subgroup G} {δ : G}
    (hVA : V ≤ A) (hV4 : Nat.card ↥V = 4) (hVc : IsCyclic ↥V)
    (hP1 : ∀ a ∈ A, δ * a * δ⁻¹ = a → a * a = 1)
    (hP2 : ∀ a ∈ A, a * (δ * a * δ⁻¹) = 1 → a * a = 1)
    (hnorm : ∀ x ∈ V, δ * x * δ⁻¹ ∈ V) : False := by
  obtain ⟨v, hv⟩ := hVc.exists_generator
  have hord : orderOf (v : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hv, hV4]
  have hvV : (v : G) ∈ V := v.2
  have hvA : (v : G) ∈ A := hVA hvV
  have h4 : (v : G) ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have h2 : (v : G) ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hord]; norm_num)
  have h1 : (v : G) ≠ 1 := fun h => h2 (by rw [h]; exact one_pow _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hv ⟨δ * v * δ⁻¹, hnorm _ hvV⟩)
  have hk' : (v : G) ^ k = δ * v * δ⁻¹ := congrArg Subtype.val hk
  have hmod : (v : G) ^ (k % 4) = (v : G) ^ k := by
    have := zpow_mod_orderOf (v : G) k
    rw [hord] at this
    exact_mod_cast this
  have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  ·
    rw [h, zpow_zero] at hmod
    have hx : δ * (v : G) * δ⁻¹ = 1 := by rw [← hk', ← hmod]
    apply h1
    have : (v : G) = δ⁻¹ * (δ * v * δ⁻¹) * δ := by group
    rw [this, hx]; group
  ·
    rw [h, zpow_one] at hmod
    have hx : δ * (v : G) * δ⁻¹ = v := by rw [← hk', ← hmod]
    exact h2 (by rw [pow_two]; exact hP1 _ hvA hx)
  ·
    rw [h] at hmod
    have hx : δ * (v : G) * δ⁻¹ = (v : G) ^ 2 := by rw [← hk', ← hmod]; norm_cast
    have : δ * ((v : G) ^ 2) * δ⁻¹ = 1 := by
      have e : δ * ((v : G) ^ 2) * δ⁻¹ = (δ * (v : G) * δ⁻¹) * (δ * (v : G) * δ⁻¹) := by
        simp only [pow_two, mul_assoc, inv_mul_cancel_left]
      rw [e, hx, ← pow_add]
      exact h4
    apply h2
    have e2 : (v : G) ^ 2 = δ⁻¹ * (δ * ((v : G) ^ 2) * δ⁻¹) * δ := by group
    rw [e2, this]; group
  ·
    rw [h] at hmod
    have hx : δ * (v : G) * δ⁻¹ = (v : G) ^ 3 := by rw [← hk', ← hmod]; norm_cast
    have hprod : (v : G) * (δ * (v : G) * δ⁻¹) = 1 := by
      rw [hx, ← pow_succ']
      exact h4
    exact h2 (by rw [pow_two]; exact hP2 _ hvA hprod)

private theorem inv_conj_eq_self_of_conj_eq_self {G : Type*} [Group G] {h x : G}
    (hfix : h * x * h⁻¹ = x) : h⁻¹ * x * h = x := by
  calc h⁻¹ * x * h = h⁻¹ * (h * x * h⁻¹) * h := by rw [hfix]
    _ = x := by group

theorem U_orbit {G : Type*} [Group G] {U : Subgroup G} {z h : G}
    (hU4 : Nat.card ↥U = 4) (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hUh : ∀ x ∈ U, h * x * h⁻¹ ∈ U) (hUh' : ∀ x ∈ U, h⁻¹ * x * h ∈ U)
    (hcube : ∀ x ∈ U, h ^ 3 * x = x * h ^ 3) (hmove : h⁻¹ * z * h ≠ z) :
    (∀ x ∈ U, h * x * h⁻¹ = x → x = 1) ∧
    (∀ x ∈ U, x ≠ 1 → x ≠ z → z = h * x * h⁻¹ ∨ z = h * (h * x * h⁻¹) * h⁻¹) := by
  have _ := hUh
  obtain ⟨a, ha⟩ : ∃ a : G, a = h⁻¹ * z * h := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : G, b = h⁻¹ * a * h := ⟨_, rfl⟩
  have haz : a ≠ z := by rw [ha]; exact hmove
  have haU : a ∈ U := by rw [ha]; exact hUh' z hzU
  have hbU : b ∈ U := by rw [hb]; exact hUh' a haU
  have hha : h * a * h⁻¹ = z := by rw [ha]; group
  have hhb : h * b * h⁻¹ = a := by rw [hb]; group
  have ha1 : a ≠ 1 := by
    intro h1
    apply hz1
    rw [← hha, h1]
    group
  have hb1 : b ≠ 1 := by
    intro h1
    apply ha1
    rw [← hhb, h1]
    group
  have hba : b ≠ a := by
    intro hba
    apply haz
    calc a = h * b * h⁻¹ := hhb.symm
      _ = h * a * h⁻¹ := by rw [hba]
      _ = z := hha
  have hbz : b ≠ z := by
    intro hbz
    apply haz
    have hc3 : h * h * h * z = z * (h * h * h) := by
      have := hcube z hzU
      rwa [pow_three'] at this
    have e1 : a = h⁻¹ * b * h := by rw [hbz, ha]
    have e2 : h⁻¹ * b * h = (h⁻¹ * h⁻¹ * h⁻¹) * z * (h * h * h) := by rw [hb, ha]; group
    have e3 : (h⁻¹ * h⁻¹ * h⁻¹) * z * (h * h * h) = z := by
      calc (h⁻¹ * h⁻¹ * h⁻¹) * z * (h * h * h)
          = (h⁻¹ * h⁻¹ * h⁻¹) * (z * (h * h * h)) := mul_assoc _ _ _
        _ = (h⁻¹ * h⁻¹ * h⁻¹) * (h * h * h * z) := by rw [hc3]
        _ = z := by group
    rw [e1, e2, e3]
  have hall : ∀ x ∈ U, x = 1 ∨ x = z ∨ x = a ∨ x = b := by
    have : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU4]; norm_num)
    let f : Fin 4 → ↥U := ![1, ⟨z, hzU⟩, ⟨a, haU⟩, ⟨b, hbU⟩]
    have hinj : Function.Injective f := by
      intro i j hij
      have hij' : (f i : G) = f j := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hz1, hz1.symm, ha1, ha1.symm, hb1, hb1.symm, haz, haz.symm, hbz, hbz.symm, hba,
          hba.symm] at hij' ⊢
    have hbij : Function.Bijective f :=
      hinj.bijective_of_nat_card_le (by rw [hU4, Nat.card_eq_fintype_card, Fintype.card_fin])
    intro x hx
    obtain ⟨i, hi⟩ := hbij.2 ⟨x, hx⟩
    have hi' : (f i : G) = x := congrArg Subtype.val hi
    fin_cases i <;> simp [f] at hi' <;>
      first
        | exact Or.inl hi'.symm
        | exact Or.inr (Or.inl hi'.symm)
        | exact Or.inr (Or.inr (Or.inl hi'.symm))
        | exact Or.inr (Or.inr (Or.inr hi'.symm))
  refine ⟨fun x hx hfix => ?_, fun x hx hx1 hxz => ?_⟩
  · rcases hall x hx with h1 | h1 | h1 | h1
    · exact h1
    · rw [h1] at hfix
      exact absurd (inv_conj_eq_self_of_conj_eq_self hfix) hmove
    · rw [h1] at hfix
      exact absurd (hfix.symm.trans hha) haz
    · rw [h1] at hfix
      exact absurd (hfix.symm.trans hhb) hba
  · rcases hall x hx with h1 | h1 | h1 | h1
    · exact absurd h1 hx1
    · exact absurd h1 hxz
    · left
      rw [h1, hha]
    · right
      rw [h1, hhb, hha]

theorem centralizer_trivial {G : Type*} [Group G] {A U : Subgroup G} {h : G}
    (hZ : Nonempty (↥A ≃* Bg.TwoGroups.Z4Z4)) (hU : ∀ x, x ∈ U ↔ x ∈ A ∧ x * x = 1)
    (hfree : ∀ x ∈ U, h * x * h⁻¹ = x → x = 1) :
    ∀ a ∈ A, h * a * h⁻¹ = a → a = 1 := by
  obtain ⟨e⟩ := hZ
  intro a ha hfix
  have hq4 : ∀ q : Bg.TwoGroups.Z4Z4, q ^ 4 = 1 := by decide
  have ha4 : a ^ 4 = 1 := by
    have h1 : (⟨a, ha⟩ : ↥A) ^ 4 = 1 := e.injective (by rw [map_pow, map_one]; exact hq4 _)
    have := congrArg Subtype.val h1
    simpa using this
  have hmul : a * a ∈ A := A.mul_mem ha ha
  have hsq : (a * a) * (a * a) = 1 := by
    rw [← ha4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hxU : a * a ∈ U := (hU _).2 ⟨hmul, hsq⟩
  have hfix2 : h * (a * a) * h⁻¹ = a * a := by
    calc h * (a * a) * h⁻¹ = (h * a * h⁻¹) * (h * a * h⁻¹) := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = a * a := by rw [hfix]
  have haa : a * a = 1 := hfree _ hxU hfix2
  exact hfree a ((hU a).2 ⟨ha, haa⟩) hfix

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
