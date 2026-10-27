module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Solvable

import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

variable {Y : Type*} [Group Y]

theorem isMulCommutative_derivedSeries_one (h : derivedSeries Y 2 = ⊥) :
    IsMulCommutative (derivedSeries Y 1) := by
  have hNN : ⁅derivedSeries Y 1, derivedSeries Y 1⁆ = ⊥ := by
    rw [← derivedSeries_succ Y 1]
    exact h
  exact Subgroup.commutator_self_eq_bot_iff.mp hNN

theorem isMulCommutative_of_closure_pairwise {S : Set Y} (h : S.Pairwise Commute)
    (hgen : Subgroup.closure S = ⊤) : IsMulCommutative Y := by
  have hS : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure h
  rw [hgen] at hS
  exact Function.Surjective.isMulCommutative
    (f := Subgroup.subtype (⊤ : Subgroup Y))
    (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩) hS

theorem mul_mem_commutator_of_isConj {t e : Y} (h : IsConj t e) (ht : t * t = 1) :
    t * e ∈ commutator Y := by
  have hπ : Abelianization.of e = Abelianization.of t := by
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    rw [← hg, map_mul, map_mul, map_inv, mul_comm (Abelianization.of g) (Abelianization.of t),
      mul_assoc, mul_inv_cancel, mul_one]
  have h1 : Abelianization.of (t * e) = 1 := by
    rw [map_mul, hπ, ← map_mul, ht, map_one]
  have hmem : t * e ∈ (Abelianization.of : Y →* Abelianization Y).ker := h1
  rwa [Abelianization.ker_of] at hmem

theorem odd_orderOf_mul_of_commute {M : Type*} [Monoid M] {a b : M} (h : Commute a b)
    (ha : Odd (orderOf a)) (hb : Odd (orderOf b)) : Odd (orderOf (a * b)) :=
  (ha.mul hb).of_dvd_nat h.orderOf_mul_dvd_mul_orderOf

theorem orderOf_dvd_two_of_orderOf_eq_two {T : Set Y} {t : Y} (ht : t ∈ T)
    (hconj : ∀ e ∈ T, IsConj t e) (hsq : ∀ e ∈ T, e * e = 1)
    (hder : derivedSeries Y 2 = ⊥)
    (hprod : ∀ e ∈ T, ∀ e' ∈ T, orderOf (e * e') ∣ 2 ∨ Odd (orderOf (e * e')))
    {e : Y} (he : e ∈ T) (hc2 : orderOf (t * e) = 2) :
    ∀ e' ∈ T, orderOf (t * e') ∣ 2 := by
  have hNcomm : IsMulCommutative (derivedSeries Y 1) := isMulCommutative_derivedSeries_one hder
  have habel : ∀ a ∈ derivedSeries Y 1, ∀ b ∈ derivedSeries Y 1, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hNcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcN : t * e ∈ derivedSeries Y 1 := by
    rw [derivedSeries_one]
    exact mul_mem_commutator_of_isConj (hconj e he) (hsq t ht)
  have hcsq : (t * e) * (t * e) = 1 := by
    rw [← pow_two, ← hc2]
    exact pow_orderOf_eq_one (t * e)
  intro e' he'
  have hc'N : t * e' ∈ derivedSeries Y 1 := by
    rw [derivedSeries_one]
    exact mul_mem_commutator_of_isConj (hconj e' he') (hsq t ht)
  set Z : Y := (t * e)⁻¹ * (t * e') with hZdef
  have hkey : e * e' = Z := by
    rw [hZdef, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t ht),
      inv_eq_of_mul_eq_one_right (hsq e he)]
    rw [mul_assoc, ← mul_assoc t t e', hsq t ht, one_mul]
  have hZ : orderOf Z ∣ 2 ∨ Odd (orderOf Z) := by
    rw [← hkey]
    exact hprod e he e' he'
  have hZN : Z ∈ derivedSeries Y 1 :=
    (derivedSeries Y 1).mul_mem ((derivedSeries Y 1).inv_mem hcN) hc'N
  have hc'eq : t * e' = (t * e) * Z := by
    rw [hZdef]
    group
  rcases hZ with hZ2 | hZodd
  · have hZsq : Z * Z = 1 := by
      rw [← pow_two, (orderOf_dvd_iff_pow_eq_one).mp hZ2]
    have hsqprod : ((t * e) * Z) * ((t * e) * Z) = 1 := by
      calc ((t * e) * Z) * ((t * e) * Z)
          = (t * e) * (Z * (t * e)) * Z := by group
        _ = (t * e) * ((t * e) * Z) * Z := by rw [habel Z hZN (t * e) hcN]
        _ = ((t * e) * (t * e)) * (Z * Z) := by group
        _ = 1 := by rw [hcsq, hZsq, one_mul]
    rw [hc'eq]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsqprod)
  · have hco : Nat.Coprime (orderOf (t * e)) (orderOf Z) := by
      rw [hc2]
      exact Odd.coprime_two_left hZodd
    have hcomm : Commute (t * e) Z := habel (t * e) hcN Z hZN
    have horder : orderOf (t * e') = orderOf (t * e) * orderOf Z := by
      rw [hc'eq]
      exact hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco
    rcases hprod t ht e' he' with hd | ho
    · rw [horder, hc2] at hd
      have hm : orderOf Z = 1 := by
        have hdvd : orderOf Z ∣ 1 :=
          Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa using hd)
        exact Nat.dvd_one.mp hdvd
      simp [horder, hc2, hm]
    · rw [horder, hc2] at ho
      obtain ⟨k, hk⟩ := ho
      omega

theorem false_of_orderOf_mul_eq_two {T : Set Y} {t : Y} (ht : t ∈ T)
    (hconj : ∀ e ∈ T, IsConj t e) (hsq : ∀ e ∈ T, e * e = 1)
    (hgen : Subgroup.closure T = ⊤) (hder : derivedSeries Y 2 = ⊥)
    (hprod : ∀ e ∈ T, ∀ e' ∈ T, orderOf (e * e') ∣ 2 ∨ Odd (orderOf (e * e')))
    {e : Y} (he : e ∈ T) (hc2 : orderOf (t * e) = 2) : False := by
  have hdvd : ∀ e' ∈ T, orderOf (t * e') ∣ 2 :=
    orderOf_dvd_two_of_orderOf_eq_two ht hconj hsq hder hprod he hc2
  have hNcomm : IsMulCommutative (derivedSeries Y 1) := isMulCommutative_derivedSeries_one hder
  have habel : ∀ a ∈ derivedSeries Y 1, ∀ b ∈ derivedSeries Y 1, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hNcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hpair : T.Pairwise Commute := by
    intro e₁ he₁ e₂ he₂ _
    have hc₁N : t * e₁ ∈ derivedSeries Y 1 := by
      rw [derivedSeries_one]
      exact mul_mem_commutator_of_isConj (hconj e₁ he₁) (hsq t ht)
    have hc₂N : t * e₂ ∈ derivedSeries Y 1 := by
      rw [derivedSeries_one]
      exact mul_mem_commutator_of_isConj (hconj e₂ he₂) (hsq t ht)
    have h₁ : (t * e₁) * (t * e₁) = 1 := by
      rw [← pow_two, (orderOf_dvd_iff_pow_eq_one).mp (hdvd e₁ he₁)]
    have h₂ : (t * e₂) * (t * e₂) = 1 := by
      rw [← pow_two, (orderOf_dvd_iff_pow_eq_one).mp (hdvd e₂ he₂)]
    have hkey₁ : e₁ * e₂ = (t * e₁)⁻¹ * (t * e₂) := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t ht),
        inv_eq_of_mul_eq_one_right (hsq e₁ he₁)]
      rw [mul_assoc, ← mul_assoc t t e₂, hsq t ht, one_mul]
    have hkey₂ : e₂ * e₁ = (t * e₂)⁻¹ * (t * e₁) := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t ht),
        inv_eq_of_mul_eq_one_right (hsq e₂ he₂)]
      rw [mul_assoc, ← mul_assoc t t e₁, hsq t ht, one_mul]
    show e₁ * e₂ = e₂ * e₁
    rw [hkey₁, hkey₂, inv_eq_of_mul_eq_one_right h₁, inv_eq_of_mul_eq_one_right h₂]
    exact habel (t * e₁) hc₁N (t * e₂) hc₂N
  have hY : IsMulCommutative Y := isMulCommutative_of_closure_pairwise hpair hgen
  have hNbot : derivedSeries Y 1 = ⊥ := by
    rw [derivedSeries_one]
    exact (commutator_eq_bot_iff Y).mpr hY
  have hcN : t * e ∈ derivedSeries Y 1 := by
    rw [derivedSeries_one]
    exact mul_mem_commutator_of_isConj (hconj e he) (hsq t ht)
  have hcone : t * e = 1 := by
    rw [hNbot] at hcN
    exact Subgroup.mem_bot.mp hcN
  rw [hcone, orderOf_one] at hc2
  exact absurd hc2 (by norm_num)

theorem odd_orderOf_mul_of_isConj {T : Set Y} {t : Y} (ht : t ∈ T)
    (hconj : ∀ e ∈ T, IsConj t e) (hsq : ∀ e ∈ T, e * e = 1)
    (hgen : Subgroup.closure T = ⊤) (hder : derivedSeries Y 2 = ⊥)
    (hprod : ∀ e ∈ T, ∀ e' ∈ T, orderOf (e * e') ∣ 2 ∨ Odd (orderOf (e * e'))) :
    ∀ e ∈ T, ∀ e' ∈ T, Odd (orderOf (e * e')) := by
  intro e he e' he'
  rcases hprod e he e' he' with hdvd | hodd
  · rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · rw [h1]
      exact odd_one
    · exfalso
      have hc2 : ∀ z ∈ T, ¬ Odd (orderOf (t * z)) → orderOf (t * z) = 2 := by
        intro z hz hzodd
        rcases hprod t ht z hz with hd | ho
        · rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2'
          · rw [h1] at hzodd
            exact absurd odd_one hzodd
          · exact h2'
        · exact absurd ho hzodd
      by_cases hce : Odd (orderOf (t * e))
      · by_cases hc'e : Odd (orderOf (t * e'))
        · have hNcomm : IsMulCommutative (derivedSeries Y 1) :=
            isMulCommutative_derivedSeries_one hder
          have habel : ∀ a ∈ derivedSeries Y 1, ∀ b ∈ derivedSeries Y 1, a * b = b * a := by
            intro a ha b hb
            exact congrArg Subtype.val (hNcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
          have hcN : t * e ∈ derivedSeries Y 1 := by
            rw [derivedSeries_one]
            exact mul_mem_commutator_of_isConj (hconj e he) (hsq t ht)
          have hc'N : t * e' ∈ derivedSeries Y 1 := by
            rw [derivedSeries_one]
            exact mul_mem_commutator_of_isConj (hconj e' he') (hsq t ht)
          have hkey : e * e' = (t * e)⁻¹ * (t * e') := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq t ht),
              inv_eq_of_mul_eq_one_right (hsq e he)]
            rw [mul_assoc, ← mul_assoc t t e', hsq t ht, one_mul]
          have hZodd : Odd (orderOf ((t * e)⁻¹ * (t * e'))) := by
            apply odd_orderOf_mul_of_commute
            · exact habel (t * e)⁻¹ ((derivedSeries Y 1).inv_mem hcN) (t * e') hc'N
            · rwa [orderOf_inv]
            · exact hc'e
          rw [← hkey, h2] at hZodd
          exact absurd hZodd (by decide)
        · exact (false_of_orderOf_mul_eq_two ht hconj hsq hgen hder hprod he'
            (hc2 e' he' hc'e)).elim
      · exact (false_of_orderOf_mul_eq_two ht hconj hsq hgen hder hprod he
          (hc2 e he hce)).elim
  · exact hodd

end CFSG.GroupTheory
