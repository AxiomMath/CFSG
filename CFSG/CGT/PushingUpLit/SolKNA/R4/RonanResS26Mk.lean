module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

theorem quatPair_mk {r : ℕ} (hr : 4 ≤ r) {X : Type} [Group X] {u b z : X}
    (hzn : z ∉ Subgroup.center X) (hou : orderOf u = 2 ^ (r - 1)) (hbu : b * u * b⁻¹ = u⁻¹)
    (hbb : b * b = u ^ 2 ^ (r - 2)) (hzu : u ^ 2 ^ (r - 2) = z) :
    orderOf (QuotientGroup.mk u : X ⧸ Subgroup.center X) = 2 ^ (r - 1) ∧
      (QuotientGroup.mk b : X ⧸ Subgroup.center X) * QuotientGroup.mk u *
        (QuotientGroup.mk b)⁻¹ = (QuotientGroup.mk u)⁻¹ ∧
      (QuotientGroup.mk b : X ⧸ Subgroup.center X) * QuotientGroup.mk b =
        (QuotientGroup.mk u) ^ 2 ^ (r - 2) ∧
      (QuotientGroup.mk u : X ⧸ Subgroup.center X) ^ 2 ^ (r - 2) = QuotientGroup.mk z := by
  have hmkz : (QuotientGroup.mk z : X ⧸ Subgroup.center X) ≠ 1 := fun h =>
    hzn ((QuotientGroup.eq_one_iff z).mp h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : ¬ (QuotientGroup.mk u : X ⧸ Subgroup.center X) ^ 2 ^ (r - 2) = 1 := by
      rw [← QuotientGroup.mk_pow, hzu]
      exact hmkz
    have h2 : (QuotientGroup.mk u : X ⧸ Subgroup.center X) ^ 2 ^ (r - 2 + 1) = 1 := by
      rw [← QuotientGroup.mk_pow, show r - 2 + 1 = r - 1 by omega, ← hou, pow_orderOf_eq_one,
        QuotientGroup.mk_one]
    rw [orderOf_eq_prime_pow h1 h2, show r - 2 + 1 = r - 1 by omega]
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, hbu]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hbb]
  · rw [← QuotientGroup.mk_pow, hzu]

theorem lift_comm_conj {X : Type} [Group X] {z u : X}
    (hnt : ∀ y : X, ∀ m ∈ Subgroup.center X, y * z * y⁻¹ = z * m → m = 1) {g : X}
    (hy : (QuotientGroup.mk g : X ⧸ Subgroup.center X) * QuotientGroup.mk z *
      (QuotientGroup.mk g)⁻¹ ≠ QuotientGroup.mk z)
    (hc : (QuotientGroup.mk u : X ⧸ Subgroup.center X) *
        ((QuotientGroup.mk g) * QuotientGroup.mk z * (QuotientGroup.mk g)⁻¹) =
      ((QuotientGroup.mk g) * QuotientGroup.mk z * (QuotientGroup.mk g)⁻¹) * QuotientGroup.mk u) :
    g * z * g⁻¹ ≠ z ∧ u * (g * z * g⁻¹) = (g * z * g⁻¹) * u := by
  refine ⟨fun h => hy ?_, ?_⟩
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  · obtain ⟨y, hydef⟩ : ∃ y : X, y = g * z * g⁻¹ := ⟨_, rfl⟩
    rw [← hydef]
    have h1 : (QuotientGroup.mk (u * y) : X ⧸ Subgroup.center X) = QuotientGroup.mk (y * u) := by
      rw [hydef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hc
    have h2 : (u * y)⁻¹ * (y * u) ∈ Subgroup.center X := QuotientGroup.eq.mp h1
    obtain ⟨m, hmdef⟩ : ∃ m : X, m = (u * y)⁻¹ * (y * u) := ⟨_, rfl⟩
    have hm : m ∈ Subgroup.center X := hmdef ▸ h2
    have hyu : y * u = u * y * m := by rw [hmdef]; group
    have hminv : m⁻¹ ∈ Subgroup.center X := (Subgroup.center X).inv_mem hm
    have huyu : u * y * u⁻¹ = y * m⁻¹ := by
      have hc1 : u * m⁻¹ = m⁻¹ * u := Subgroup.mem_center_iff.mp hminv u
      calc u * y * u⁻¹ = (u * y * m) * m⁻¹ * u⁻¹ := by group
        _ = (y * u) * m⁻¹ * u⁻¹ := by rw [← hyu]
        _ = y * (u * m⁻¹) * u⁻¹ := by group
        _ = y * m⁻¹ := by rw [hc1]; group
    have hw : (g⁻¹ * u * g) * z * (g⁻¹ * u * g)⁻¹ = z * m⁻¹ := by
      have e1 : (g⁻¹ * u * g) * z * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * y * u⁻¹) * g := by
        rw [hydef]; group
      have e3 : g⁻¹ * y * g = z := by rw [hydef]; group
      have e4 : g⁻¹ * m⁻¹ * g = m⁻¹ := by
        have := Subgroup.mem_center_iff.mp hminv g⁻¹
        rw [this]; group
      calc (g⁻¹ * u * g) * z * (g⁻¹ * u * g)⁻¹ = g⁻¹ * (u * y * u⁻¹) * g := e1
        _ = g⁻¹ * (y * m⁻¹) * g := by rw [huyu]
        _ = (g⁻¹ * y * g) * (g⁻¹ * m⁻¹ * g) := by group
        _ = z * m⁻¹ := by rw [e3, e4]
    have h0 := hnt (g⁻¹ * u * g) m⁻¹ hminv hw
    have hm1 : m = 1 := inv_eq_one.mp h0
    rw [hyu, hm1, mul_one]

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
