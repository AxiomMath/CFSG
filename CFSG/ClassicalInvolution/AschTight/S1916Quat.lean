module

public import CFSG.ClassicalInvolution.AschTight.TzConj
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

theorem IsQuaternionSub.conjSub' {P : Subgroup G} (h : IsQuaternionSub P) (g : G) :
    IsQuaternionSub (conjSub g P) := by
  obtain ⟨a, b, ha4, hcard, hb2, hbab, hcl⟩ := h
  have hord : orderOf (g * a * g⁻¹) = orderOf a := by
    have := (MulAut.conj g).orderOf_eq a
    simpa [MulAut.conj_apply] using this
  refine ⟨g * a * g⁻¹, g * b * g⁻¹, hord ▸ ha4, ?_, ?_, ?_, ?_⟩
  · rw [hord, ← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  · rw [hord, conj_pow, ← hb2]
    group
  · calc g * b * g⁻¹ * (g * a * g⁻¹) * (g * b * g⁻¹)⁻¹ = g * (b * a * b⁻¹) * g⁻¹ := by group
      _ = (g * a * g⁻¹)⁻¹ := by rw [hbab]; group
  · rw [← hcl, conjSub, MonoidHom.map_closure, Set.image_pair]
    rfl

theorem pow_four_eq_one_of_not_mem_zpowers {P : Subgroup G} {a b : G}
    (hb2 : b * b = a ^ (orderOf a / 2)) (hbab : b * a * b⁻¹ = a⁻¹)
    (hcl : Subgroup.closure {a, b} = P) {u : G} (hu : u ∈ P)
    (hua : u ∉ Subgroup.zpowers a) : u ^ 4 = 1 := by
  have hconj : ∀ i : ℤ, b * a ^ i * b⁻¹ = a ^ (-i) := fun i => by
    rw [← _root_.conj_zpow, hbab, inv_zpow']
  have hconj' : ∀ i : ℤ, b⁻¹ * a ^ i * b = a ^ (-i) := fun i => by
    have h1 := hconj (-i)
    rw [neg_neg] at h1
    calc b⁻¹ * a ^ i * b = b⁻¹ * (b * a ^ (-i) * b⁻¹) * b := by rw [h1]
      _ = a ^ (-i) := by group
  have hbN : b ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [hconj]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
    · intro hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
      have e : w = b⁻¹ * a ^ i * b := by rw [hi]; group
      rw [e, hconj']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have hu' : u ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [← closure_pair_eq_sup_zpowers, hcl]
    exact hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr hbN)] at hu'
  obtain ⟨v, hv, w, hw, rfl⟩ := Set.mem_mul.mp hu'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hb2' : b ^ (2 : ℤ) = a ^ ((orderOf a / 2 : ℕ) : ℤ) := by
    rw [zpow_two, hb2, zpow_natCast]
  have hm : a ^ (orderOf a / 2) * a ^ (orderOf a / 2) = 1 := by
    have h1 : b * (b * b) * b⁻¹ = b * b := by group
    rw [hb2, ← zpow_natCast, hconj, zpow_neg, zpow_natCast] at h1
    calc a ^ (orderOf a / 2) * a ^ (orderOf a / 2) =
          a ^ (orderOf a / 2) * (a ^ (orderOf a / 2))⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exfalso
    apply hua
    rw [← two_mul, zpow_mul, hb2', ← zpow_mul]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _)
  · have hqa : a ^ i * b ^ (2 * m + 1) = a ^ (i + ((orderOf a / 2 : ℕ) : ℤ) * m) * b := by
      rw [zpow_add_one, zpow_mul, hb2', ← zpow_mul, ← mul_assoc, ← zpow_add]
    rw [hqa]
    set j : ℤ := i + ((orderOf a / 2 : ℕ) : ℤ) * m
    have hsq : a ^ j * b * (a ^ j * b) = b * b := by
      calc a ^ j * b * (a ^ j * b) = a ^ j * (b * a ^ j * b⁻¹) * (b * b) := by group
        _ = b * b := by rw [hconj, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    calc (a ^ j * b) ^ 4 = (a ^ j * b * (a ^ j * b)) * (a ^ j * b * (a ^ j * b)) := by
          rw [pow_succ, pow_succ, pow_succ, pow_one]; group
      _ = 1 := by rw [hsq, hb2, hm]

theorem IsQuaternionSub.eq_of_cyclic [Finite G] {P U U' : Subgroup G} (hP : IsQuaternionSub P)
    (h16 : 16 ≤ Nat.card P) (hUP : U ≤ P) (hU'P : U' ≤ P) (hU : IsCyclic ↥U)
    (hU' : IsCyclic ↥U') (hcU : Nat.card P = 2 * Nat.card U) (hcU' : Nat.card P = 2 * Nat.card U') :
    U = U' := by
  obtain ⟨a, b, ha4, hcard, hb2, hbab, hcl⟩ := hP
  have key : ∀ V : Subgroup G, V ≤ P → IsCyclic ↥V → Nat.card P = 2 * Nat.card V →
      V = Subgroup.zpowers a := by
    intro V hVP hV hcV
    obtain ⟨⟨v, hvV⟩, hv⟩ := hV.exists_generator
    have hVeq : V = Subgroup.zpowers v := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := hv ⟨x, hx⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      · rintro ⟨k, rfl⟩
        exact V.zpow_mem hvV k
    have hordv : orderOf v = orderOf a := by
      have h1 : Nat.card V = orderOf v := by rw [hVeq, Nat.card_zpowers]
      omega
    have hva : v ∈ Subgroup.zpowers a := by
      by_contra hna
      have h4 := pow_four_eq_one_of_not_mem_zpowers hb2 hbab hcl (hVP hvV) hna
      have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h4)
      omega
    have hle : V ≤ Subgroup.zpowers a := by
      rw [hVeq, Subgroup.zpowers_le]
      exact hva
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers]
    omega
  rw [key U hUP hU hcU, key U' hU'P hU' hcU']

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
