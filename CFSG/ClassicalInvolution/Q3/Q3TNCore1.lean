module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Q3.Q3UFix

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores

variable {G : Type} [Group G]

theorem mem_centralizer_of_acts_as {T : Subgroup G} {g x : G} (hg : Odd (orderOf g))
    (hx : x * x = 1) (hxT : ∀ a ∈ T, x * a * x⁻¹ ∈ T)
    (hact : ∀ a ∈ T, g * a * g⁻¹ = x * a * x⁻¹) : x ∈ Subgroup.centralizer (T : Set G) := by
  have hpow : ∀ n : ℕ, ∀ a ∈ T, x ^ n * a * (x ^ n)⁻¹ ∈ T ∧
      g ^ n * a * (g ^ n)⁻¹ = x ^ n * a * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih =>
      intro a ha
      obtain ⟨h1, h2⟩ := ih a ha
      refine ⟨?_, ?_⟩
      · have := hxT _ h1
        rwa [show x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ = x ^ (n + 1) * a * (x ^ (n + 1))⁻¹ by
          rw [pow_succ']; group] at this
      · calc g ^ (n + 1) * a * (g ^ (n + 1))⁻¹ = g * (g ^ n * a * (g ^ n)⁻¹) * g⁻¹ := by
              rw [pow_succ']; group
          _ = g * (x ^ n * a * (x ^ n)⁻¹) * g⁻¹ := by rw [h2]
          _ = x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ := hact _ h1
          _ = x ^ (n + 1) * a * (x ^ (n + 1))⁻¹ := by rw [pow_succ']; group
  obtain ⟨j, hj⟩ := hg
  have hxj : x ^ orderOf g = x := by
    rw [hj, pow_succ, pow_mul, show x ^ 2 = 1 by rw [pow_two]; exact hx, one_pow, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h := (hpow (orderOf g) a ha).2
  rw [pow_orderOf_eq_one, hxj, one_mul, inv_one, mul_one] at h
  calc a * x = x * a * x⁻¹ * x := by rw [← h]
    _ = x * a := by group

theorem conjSub_pow_eq_self {T : Subgroup G} {g : G} (h : conjSub g T = T) :
    ∀ n : ℕ, conjSub (g ^ n) T = T
  | 0 => by rw [pow_zero, conjSub_one]
  | n + 1 => by rw [pow_succ', conjSub_mul, conjSub_pow_eq_self h n, h]

theorem conjSub_eq_of_sq {T : Subgroup G} {σ : G} (hσ : Odd (orderOf σ))
    (h : conjSub (σ * σ) T = T) : conjSub σ T = T := by
  obtain ⟨j, hj⟩ := hσ
  have hσ' : σ = (σ * σ) ^ (j + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf σ + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [hσ']
  exact conjSub_pow_eq_self h _

theorem conjSub_ne_of_odd {T : Subgroup G} {σ : G} (hσ : Odd (orderOf σ))
    (hσT : conjSub σ T ≠ T) :
    conjSub σ⁻¹ T ≠ T ∧ conjSub (σ⁻¹ * σ⁻¹) T ≠ T ∧ conjSub σ T ≠ conjSub σ⁻¹ T ∧
      conjSub (σ⁻¹ * σ⁻¹) T ≠ conjSub σ⁻¹ T := by
  have h1 : conjSub σ⁻¹ T ≠ T := by
    intro h
    apply hσT
    calc conjSub σ T = conjSub σ (conjSub σ⁻¹ T) := by rw [h]
      _ = T := conjSub_conjSub_inv σ T
  have hsq : conjSub (σ * σ) T ≠ T := fun h => hσT (conjSub_eq_of_sq hσ h)
  refine ⟨h1, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · apply hsq
    calc conjSub (σ * σ) T = conjSub (σ * σ) (conjSub (σ⁻¹ * σ⁻¹) T) := by rw [h]
      _ = T := by rw [← conjSub_mul, show σ * σ * (σ⁻¹ * σ⁻¹) = 1 by group, conjSub_one]
  · apply hsq
    calc conjSub (σ * σ) T = conjSub σ (conjSub σ T) := conjSub_mul σ σ T
      _ = conjSub σ (conjSub σ⁻¹ T) := by rw [h]
      _ = T := conjSub_conjSub_inv σ T
  · apply h1
    calc conjSub σ⁻¹ T = conjSub σ (conjSub (σ⁻¹ * σ⁻¹) T) := by
          rw [← conjSub_mul, show σ * (σ⁻¹ * σ⁻¹) = σ⁻¹ by group]
      _ = conjSub σ (conjSub σ⁻¹ T) := by rw [h]
      _ = T := conjSub_conjSub_inv σ T

theorem conj_inv_mem {T : Subgroup G} {σ x : G} (hxT : x ∈ T) :
    σ⁻¹ * x * σ ∈ conjSub σ⁻¹ T ∧ σ⁻¹ * σ⁻¹ * x * σ * σ ∈ conjSub (σ⁻¹ * σ⁻¹) T := by
  refine ⟨?_, ?_⟩
  · have := conj_mem_conjSub (n := σ⁻¹) hxT
    rwa [inv_inv] at this
  · have := conj_mem_conjSub (n := σ⁻¹ * σ⁻¹) hxT
    rwa [mul_inv_rev, inv_inv, ← mul_assoc] at this

theorem acts_as_d [Finite G] {T : Subgroup G} (hTc : IsComponent T) {σ x : G} (hσ : Odd (orderOf σ))
    (hσT : conjSub σ T ≠ T) (hxT : x ∈ T) (hx2 : x * x = 1) :
    (∀ a ∈ T, σ⁻¹ * (x * σ * x⁻¹) * a * (σ⁻¹ * (x * σ * x⁻¹))⁻¹ = x * a * x⁻¹) ∧
      σ⁻¹ * (x * σ * x⁻¹) ∈ Subgroup.centralizer (conjSub σ T : Set G) := by
  obtain ⟨h1, -, h3, -⟩ := conjSub_ne_of_odd hσ hσT
  have hTm1 : IsComponent (conjSub σ⁻¹ T) := isComponent_map_mulEquiv (MulAut.conj σ⁻¹) hTc
  have hT1 : IsComponent (conjSub σ T) := isComponent_map_mulEquiv (MulAut.conj σ) hTc
  have hu := (conj_inv_mem (σ := σ) hxT).1
  have hd : σ⁻¹ * (x * σ * x⁻¹) = (σ⁻¹ * x * σ) * x⁻¹ := by group
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  refine ⟨fun a ha => ?_, ?_⟩
  · have hb : x⁻¹ * a * x ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hxT) ha) hxT
    have hub := commute_of_ne_isComponent hTm1 hTc h1 hu hb
    rw [hd]
    calc σ⁻¹ * x * σ * x⁻¹ * a * (σ⁻¹ * x * σ * x⁻¹)⁻¹
        = (σ⁻¹ * x * σ) * (x⁻¹ * a * x) * (σ⁻¹ * x * σ)⁻¹ := by group
      _ = (x⁻¹ * a * x) * (σ⁻¹ * x * σ) * (σ⁻¹ * x * σ)⁻¹ := by rw [hub]
      _ = x * a * x⁻¹ := by rw [mul_inv_cancel_right, hxinv]
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hub := commute_of_ne_isComponent hTm1 hT1 (Ne.symm h3) hu hb
    have hxb := commute_of_ne_isComponent hTc hT1 (Ne.symm hσT) hxT hb
    have hxb' : b * x⁻¹ = x⁻¹ * b := by
      calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
        _ = x⁻¹ * (b * x) * x⁻¹ := by rw [hxb]
        _ = x⁻¹ * b := by group
    rw [hd]
    calc b * (σ⁻¹ * x * σ * x⁻¹) = (b * (σ⁻¹ * x * σ)) * x⁻¹ := by group
      _ = (σ⁻¹ * x * σ) * (b * x⁻¹) := by rw [← hub]; group
      _ = σ⁻¹ * x * σ * x⁻¹ * b := by rw [hxb']; group

theorem acts_as_e [Finite G] {T : Subgroup G} (hTc : IsComponent T) {σ x : G} (hσ : Odd (orderOf σ))
    (hσT : conjSub σ T ≠ T) (hxT : x ∈ T) :
    ∀ a ∈ T, σ⁻¹ * (σ⁻¹ * (x * σ * x⁻¹)) * σ * (σ⁻¹ * (x * σ * x⁻¹))⁻¹ * a *
        (σ⁻¹ * (σ⁻¹ * (x * σ * x⁻¹)) * σ * (σ⁻¹ * (x * σ * x⁻¹))⁻¹)⁻¹ = x * a * x⁻¹ := by
  intro a ha
  obtain ⟨h1, h2, -, -⟩ := conjSub_ne_of_odd hσ hσT
  have hTm1 : IsComponent (conjSub σ⁻¹ T) := isComponent_map_mulEquiv (MulAut.conj σ⁻¹) hTc
  have hTm2 : IsComponent (conjSub (σ⁻¹ * σ⁻¹) T) :=
    isComponent_map_mulEquiv (MulAut.conj (σ⁻¹ * σ⁻¹)) hTc
  have hu1 := (conj_inv_mem (σ := σ) (T.inv_mem hxT)).1
  have hu2 := (conj_inv_mem (σ := σ) hxT).2
  have he : σ⁻¹ * (σ⁻¹ * (x * σ * x⁻¹)) * σ * (σ⁻¹ * (x * σ * x⁻¹))⁻¹ =
      (σ⁻¹ * σ⁻¹ * x * σ * σ) * (σ⁻¹ * x⁻¹ * σ) * x * (σ⁻¹ * x⁻¹ * σ) := by group
  have hxa : x * a * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hxT ha) (T.inv_mem hxT)
  have c1 := commute_of_ne_isComponent hTm1 hTc h1 hu1 ha
  have c2 := commute_of_ne_isComponent hTm1 hTc h1 hu1 hxa
  have c3 := commute_of_ne_isComponent hTm2 hTc h2 hu2 hxa
  rw [he]
  calc (σ⁻¹ * σ⁻¹ * x * σ * σ) * (σ⁻¹ * x⁻¹ * σ) * x * (σ⁻¹ * x⁻¹ * σ) * a *
        ((σ⁻¹ * σ⁻¹ * x * σ * σ) * (σ⁻¹ * x⁻¹ * σ) * x * (σ⁻¹ * x⁻¹ * σ))⁻¹
      = (σ⁻¹ * σ⁻¹ * x * σ * σ) * ((σ⁻¹ * x⁻¹ * σ) * (x * ((σ⁻¹ * x⁻¹ * σ) * a *
          (σ⁻¹ * x⁻¹ * σ)⁻¹) * x⁻¹) * (σ⁻¹ * x⁻¹ * σ)⁻¹) * (σ⁻¹ * σ⁻¹ * x * σ * σ)⁻¹ := by
        group
    _ = (σ⁻¹ * σ⁻¹ * x * σ * σ) * ((σ⁻¹ * x⁻¹ * σ) * (x * a * x⁻¹) * (σ⁻¹ * x⁻¹ * σ)⁻¹) *
          (σ⁻¹ * σ⁻¹ * x * σ * σ)⁻¹ := by rw [c1, mul_inv_cancel_right]
    _ = (σ⁻¹ * σ⁻¹ * x * σ * σ) * (x * a * x⁻¹) * (σ⁻¹ * σ⁻¹ * x * σ * σ)⁻¹ := by
        rw [c2, mul_inv_cancel_right]
    _ = x * a * x⁻¹ := by rw [c3, mul_inv_cancel_right]

end CFSG.ClassicalInvolution.Q3.Q3T
