module

public import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_isElemAbelian_card_prime_sq_of_mulEquiv_zmod_sq {A : Subgroup G} {m r : ℕ}
    (e : ↥A ≃* Multiplicative (ZMod m × ZMod m)) (hr : r.Prime) (hdvd : r ∣ m) :
    ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hcardA : Nat.card ↥A = m * m := by
    calc Nat.card ↥A = Nat.card (Multiplicative (ZMod m × ZMod m)) := Nat.card_congr e.toEquiv
      _ = Nat.card (ZMod m × ZMod m) := Nat.card_congr Multiplicative.toAdd
      _ = m * m := by simp [Nat.card_prod, Nat.card_zmod]
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm, mul_zero] at hcardA
    exact (Nat.card_pos (α := ↥A)).ne' hcardA
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hmr : r ≤ m := Nat.le_of_dvd hmpos hdvd
  let x0 : ZMod m := (m / r : ℕ)
  have hx0_r : (r : ZMod m) * x0 = 0 := by
    have hc : ((m / r * r : ℕ) : ZMod m) = 0 := by
      rw [Nat.div_mul_cancel hdvd, ZMod.natCast_self]
    calc (r : ZMod m) * x0 = ((r * (m / r) : ℕ) : ZMod m) := by push_cast [x0]; ring
      _ = ((m / r * r : ℕ) : ZMod m) := by rw [mul_comm]
      _ = 0 := hc
  have hx0_ne : x0 ≠ 0 := by
    intro hx
    have hdvd' : m ∣ m / r := (ZMod.natCast_eq_zero_iff (m / r) m).1 hx
    have hle : m ≤ m / r := Nat.le_of_dvd (Nat.div_pos hmr hr.pos) hdvd'
    have hlt : m / r < m := Nat.div_lt_self hmpos hr.one_lt
    omega
  let g1 : Multiplicative (ZMod m × ZMod m) := Multiplicative.ofAdd (x0, 0)
  let g2 : Multiplicative (ZMod m × ZMod m) := Multiplicative.ofAdd (0, x0)
  have hg1_r : g1 ^ r = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext <;> simp [g1, hx0_r]
  have hg2_r : g2 ^ r = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    ext <;> simp [g2, hx0_r]
  have hg1_ne : g1 ≠ 1 := by
    intro h
    apply hx0_ne
    have hc := congrArg (fun z => (Multiplicative.toAdd z).1) h
    simpa [g1] using hc
  have hg2_ne : g2 ≠ 1 := by
    intro h
    apply hx0_ne
    have hc := congrArg (fun z => (Multiplicative.toAdd z).2) h
    simpa [g2] using hc
  let x : ↥A := e.symm g1
  let v : ↥A := e.symm g2
  have hxr : x ^ r = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simpa [x] using hg1_r
  have hvr : v ^ r = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simpa [v] using hg2_r
  have hxne : x ≠ 1 := by
    intro h
    apply hg1_ne
    rw [← map_one e, ← h]
    simp [x]
  have hvne : v ≠ 1 := by
    intro h
    apply hg2_ne
    rw [← map_one e, ← h]
    simp [v]
  have hxord : orderOf x = r := orderOf_eq_prime hxr hxne
  have hvord : orderOf v = r := orderOf_eq_prime hvr hvne
  have hxcard : Nat.card (Subgroup.zpowers x) = r := by
    rw [Nat.card_zpowers, hxord]
  have hxv : v ∉ Subgroup.zpowers x := by
    intro hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have h2 : g2 = g1 ^ k := by
      have h3 : e v = e (x ^ k) := by rw [hk]
      simpa [v, x] using h3
    have hc := congrArg (fun z => (Multiplicative.toAdd z).2) h2
    rw [toAdd_zpow] at hc
    simp [g1, g2] at hc
    exact hx0_ne hc
  have hcomm : ∀ a ∈ Subgroup.zpowers x, a * v = v * a := by
    have hcomm_eq : x * v = v * x := by
      apply e.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left hcomm_eq k).eq
  obtain ⟨hEel, hEcard⟩ :=
    isElemAbelian_sup_zpowers_of_commute (r := r) hxcard hvord hxv hcomm
  refine ⟨(Subgroup.zpowers x ⊔ Subgroup.zpowers v).map A.subtype, Subgroup.map_subtype_le _,
    hEel.map A.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hEcard]

theorem exists_isElemAbelian_card_nine_of_mulEquiv_zmod_sq {A : Subgroup G} {m : ℕ}
    (e : ↥A ≃* Multiplicative (ZMod m × ZMod m)) (h3 : 3 ∣ m) :
    ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 :=
  exists_isElemAbelian_card_prime_sq_of_mulEquiv_zmod_sq e Nat.prime_three h3

end CFSG.GroupTheory
