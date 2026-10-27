module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup

section Key

variable {G : Type*} [Group G]

theorem commute_of_commute_pow {r a : ℕ} (hr : r.Prime) (ha : ¬ r ∣ a) {y z : G}
    (hz : orderOf z = r) (h : y * z ^ a = z ^ a * y) : y * z = z * y := by
  have hcop : Nat.Coprime a r := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hr).2 ha))
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  have hzk : z ^ (a * k) = z := by
    rw [← pow_mod_orderOf, hz, hk, pow_one]
  have h' : y * (z ^ a) ^ k = (z ^ a) ^ k * y :=
    (Commute.pow_right (show Commute y (z ^ a) from h) k).eq
  rwa [← pow_mul, hzk] at h'

theorem exists_mem_centralizer_not_mem_normalizer {r : ℕ} (hr : r.Prime) (hr3 : ¬ r ∣ 3)
    (L : Subgroup G) (z c : G) (hz : orderOf z = r) (hc : orderOf c = r)
    (hLz : ∀ l ∈ L, l * z = z * l) (hcL : c ∈ L)
    (hZ3 : ∀ θ ∈ L, (∀ l ∈ L, θ * l = l * θ) → θ ^ 3 = 1)
    (hCc : ∀ a ∈ L, ∀ b ∈ L, a * c = c * a → b * c = c * b → a * b = b * a)
    (hperf : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer {z} → P ≤ L) {a b : ℕ}
    (ha : ¬ r ∣ a) (hb : ¬ r ∣ b)
    (hR : ⁅⁅centralizer ({z ^ a * c ^ b} : Set G), centralizer ({z ^ a * c ^ b} : Set G)⁆,
      ⁅centralizer ({z ^ a * c ^ b} : Set G), centralizer ({z ^ a * c ^ b} : Set G)⁆⁆ =
      ⁅centralizer ({z ^ a * c ^ b} : Set G), centralizer ({z ^ a * c ^ b} : Set G)⁆)
    (hnc : ∃ u ∈ ⁅centralizer ({z ^ a * c ^ b} : Set G), centralizer ({z ^ a * c ^ b} : Set G)⁆,
      ∃ v ∈ ⁅centralizer ({z ^ a * c ^ b} : Set G), centralizer ({z ^ a * c ^ b} : Set G)⁆,
        u * v ≠ v * u) :
    ∃ y ∈ centralizer ({z ^ a * c ^ b} : Set G), y ∉ normalizer (L : Set G) := by
  by_contra hcon
  push Not at hcon
  set x : G := z ^ a * c ^ b with hx
  set D : Subgroup G := centralizer ({x} : Set G) with hD
  have hcz : ∀ l ∈ L, l * z ^ a = z ^ a * l := fun l hl =>
    (Commute.pow_right (show Commute l z from hLz l hl) a).eq
  have hcb : c ^ b ∈ L := L.pow_mem hcL b
  have hcop : Nat.Coprime 3 r := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hr).2 hr3)
  have hord : ∀ y ∈ D, y * z = z * y ∧ y * c = c * y := by
    intro y hy
    have hxy : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    have hyN := hcon y hy
    rw [Subgroup.mem_normalizer_iff] at hyN
    have hyl : ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun l hl => (hyN l).1 hl
    have hyl' : ∀ l ∈ L, y⁻¹ * l * y ∈ L := by
      intro l hl
      refine (hyN (y⁻¹ * l * y)).2 ?_
      have e : y * (y⁻¹ * l * y) * y⁻¹ = l := by group
      rw [e]
      exact hl
    set z' : G := y * z ^ a * y⁻¹ with hz'
    set c' : G := y * c ^ b * y⁻¹ with hc'
    have hc'L : c' ∈ L := hyl _ hcb
    have hz'L : ∀ l ∈ L, l * z' = z' * l := by
      intro l hl
      have h1 := hcz (y⁻¹ * l * y) (hyl' l hl)
      calc l * z' = y * ((y⁻¹ * l * y) * z ^ a) * y⁻¹ := by rw [hz']; group
        _ = y * (z ^ a * (y⁻¹ * l * y)) * y⁻¹ := by rw [h1]
        _ = z' * l := by rw [hz']; group
    have hprod : z' * c' = z ^ a * c ^ b := by
      have e : z' * c' = y * (z ^ a * c ^ b) * y⁻¹ := by rw [hz', hc']; group
      rw [e]
      calc y * (z ^ a * c ^ b) * y⁻¹ = (z ^ a * c ^ b) * y * y⁻¹ := by rw [← hx, hxy]
        _ = z ^ a * c ^ b := by group
    set θ : G := (z ^ a)⁻¹ * z' with hθ
    have hθc' : c' = θ⁻¹ * c ^ b := by
      have h1 : c' = z'⁻¹ * (z ^ a * c ^ b) := eq_inv_mul_of_mul_eq hprod
      rw [h1, hθ]
      group
    have hθL : θ ∈ L := by
      have : θ = c ^ b * c'⁻¹ := by rw [hθc']; group
      rw [this]
      exact L.mul_mem hcb (L.inv_mem hc'L)
    have hθcen : ∀ l ∈ L, θ * l = l * θ := by
      intro l hl
      have h1 : (z ^ a)⁻¹ * l = l * (z ^ a)⁻¹ :=
        (Commute.inv_left (show Commute (z ^ a) l from (hcz l hl).symm)).eq
      have h2 := hz'L l hl
      calc θ * l = (z ^ a)⁻¹ * (z' * l) := by rw [hθ]; group
        _ = (z ^ a)⁻¹ * (l * z') := by rw [h2]
        _ = ((z ^ a)⁻¹ * l) * z' := by group
        _ = (l * (z ^ a)⁻¹) * z' := by rw [h1]
        _ = l * θ := by rw [hθ]; group
    have hθ3 : θ ^ 3 = 1 := hZ3 θ hθL hθcen
    have hcr : c ^ r = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    have hθr : θ ^ r = 1 := by
      have h1 : c' ^ r = 1 := by
        rw [hc', conj_pow, ← pow_mul, mul_comm, pow_mul, hcr, one_pow]
        group
      have hcomm : Commute θ⁻¹ (c ^ b) := (Commute.inv_left (show Commute θ (c ^ b) from
        hθcen _ hcb)) 
      rw [hθc', hcomm.mul_pow, ← pow_mul, mul_comm b r, pow_mul, hcr, one_pow, mul_one,
        inv_pow, inv_eq_one] at h1
      exact h1
    have hθ1 : θ = 1 := by
      have := (pow_gcd_eq_one (a := θ)).2 ⟨hθ3, hθr⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
    have hc'eq : c' = c ^ b := by rw [hθc', hθ1]; group
    have hz'eq : z' = z ^ a := by
      have : (z ^ a)⁻¹ * z' = 1 := by rw [← hθ]; exact hθ1
      exact (inv_mul_eq_one.1 this).symm
    have hya : y * z ^ a = z ^ a * y := by
      have : y * z ^ a * y⁻¹ = z ^ a := by rw [← hz']; exact hz'eq
      exact mul_inv_eq_iff_eq_mul.1 this
    have hyb : y * c ^ b = c ^ b * y := by
      have : y * c ^ b * y⁻¹ = c ^ b := by rw [← hc']; exact hc'eq
      exact mul_inv_eq_iff_eq_mul.1 this
    exact ⟨commute_of_commute_pow hr ha hz hya, commute_of_commute_pow hr hb hc hyb⟩
  have hDz : D ≤ centralizer {z} := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2 (hord y hy).1
  have hRD : ⁅D, D⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hg₁ hg₂) (D.inv_mem hg₁)) (D.inv_mem hg₂)
  have hRL := hperf ⁅D, D⁆ hR (hRD.trans hDz)
  obtain ⟨u, hu, v, hv, huv⟩ := hnc
  exact huv (hCc u (hRL hu) v (hRL hv) (hord u (hRD hu)).2 (hord v (hRD hv)).2)

end Key

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
