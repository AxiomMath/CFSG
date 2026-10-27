module

public import CFSG.ClassicalInvolution.Q3.Q3ZBOdd

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

section Central

variable {G : Type*} [Group G]

theorem comm_data_inv {x v c : G} (hcx : Commute c x) (h : x * v = v * x * c) :
    x⁻¹ * v = v * x⁻¹ * c⁻¹ := by
  have h1 : v * x = x * v * c⁻¹ := by rw [h]; group
  calc x⁻¹ * v = x⁻¹ * (v * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * v * c⁻¹) * x⁻¹ := by rw [h1]
    _ = v * (c⁻¹ * x⁻¹) := by group
    _ = v * x⁻¹ * c⁻¹ := by rw [hcx.inv_inv.eq, mul_assoc]

theorem comm_of_conj {a x y v g : G} {j₁ j₂ k : ℤ} (hay : Commute a y) (hav : Commute a v)
    (hag : Commute a g) (hgv : Commute g v) (hxv : x * v = v * x * a ^ j₁)
    (hyv : y * v = v * y * a ^ j₂) (hg : g * x * g⁻¹ = x * y * a ^ k) : y * v = v * y := by
  have hgiv : g⁻¹ * v = v * g⁻¹ := hgv.inv_left.eq
  have hz : ∀ (n : ℤ) (w : G), Commute a w → a ^ n * w = w * a ^ n := fun n w h =>
    (h.zpow_left n).eq
  have s1 : g * x * g⁻¹ * v = v * (g * x * g⁻¹) * a ^ j₁ := by
    calc g * x * g⁻¹ * v = g * (x * (g⁻¹ * v)) := by group
      _ = g * (x * (v * g⁻¹)) := by rw [hgiv]
      _ = g * (x * v) * g⁻¹ := by group
      _ = g * (v * x * a ^ j₁) * g⁻¹ := by rw [hxv]
      _ = (g * v) * x * (a ^ j₁ * g⁻¹) := by group
      _ = (v * g) * x * (g⁻¹ * a ^ j₁) := by
          rw [hgv.eq, (hag.zpow_left j₁).inv_right.eq]
      _ = v * (g * x * g⁻¹) * a ^ j₁ := by group
  have s2 : (x * y * a ^ k) * v = v * (x * y * a ^ k) * a ^ j₁ := by rw [← hg]; exact s1
  have s3 : (x * y * a ^ k) * v = v * x * y * (a ^ j₁ * a ^ j₂ * a ^ k) := by
    calc x * y * a ^ k * v = x * y * (a ^ k * v) := by group
      _ = x * y * (v * a ^ k) := by rw [hz k v hav]
      _ = x * (y * v) * a ^ k := by group
      _ = x * (v * y * a ^ j₂) * a ^ k := by rw [hyv]
      _ = (x * v) * y * a ^ j₂ * a ^ k := by group
      _ = (v * x * a ^ j₁) * y * a ^ j₂ * a ^ k := by rw [hxv]
      _ = v * x * (a ^ j₁ * y) * a ^ j₂ * a ^ k := by group
      _ = v * x * (y * a ^ j₁) * a ^ j₂ * a ^ k := by rw [hz j₁ y hay]
      _ = v * x * y * (a ^ j₁ * a ^ j₂ * a ^ k) := by group
  have s4 : v * (x * y * a ^ k) * a ^ j₁ = v * x * y * (a ^ k * a ^ j₁) := by group
  have h5 : a ^ j₁ * a ^ j₂ * a ^ k = a ^ k * a ^ j₁ :=
    mul_left_cancel (a := v * x * y) (s3.symm.trans (s2.trans s4))
  rw [← zpow_add, ← zpow_add, ← zpow_add] at h5
  have h6 : a ^ j₂ = 1 := by
    have e : a ^ j₂ = a ^ (j₁ + j₂ + k) * (a ^ (k + j₁))⁻¹ := by
      rw [← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [e, h5, mul_inv_cancel]
  rw [hyv, h6, mul_one]

theorem mem_of_inverted {S : Subgroup G} {zh a c : G} (hodd : Odd (orderOf c)) (hzh : zh ∈ S)
    (ha : a ∈ S) (hcom : Commute c a) (hnorm : c * zh⁻¹ * c⁻¹ ∈ S) {j : ℤ}
    (hj : zh * c * zh⁻¹ = c⁻¹ * a ^ j) : c ∈ S := by
  have h1 : zh * (c * zh⁻¹ * c⁻¹) ∈ S := S.mul_mem hzh hnorm
  have h2 : zh * (c * zh⁻¹ * c⁻¹) = c⁻¹ * a ^ j * c⁻¹ := by
    calc zh * (c * zh⁻¹ * c⁻¹) = (zh * c * zh⁻¹) * c⁻¹ := by group
      _ = _ := by rw [hj]
  rw [h2] at h1
  have hc' : a ^ j * c⁻¹ = c⁻¹ * a ^ j := ((hcom.inv_left).symm.zpow_left j).eq
  have h3 : c⁻¹ * c⁻¹ ∈ S := by
    have h4 : (c⁻¹ * a ^ j * c⁻¹) * (a ^ j)⁻¹ ∈ S := S.mul_mem h1 (S.inv_mem (S.zpow_mem ha j))
    have h5 : c⁻¹ * a ^ j * c⁻¹ * (a ^ j)⁻¹ = c⁻¹ * c⁻¹ := by
      calc c⁻¹ * a ^ j * c⁻¹ * (a ^ j)⁻¹ = c⁻¹ * (a ^ j * c⁻¹) * (a ^ j)⁻¹ := by group
        _ = c⁻¹ * (c⁻¹ * a ^ j) * (a ^ j)⁻¹ := by rw [hc']
        _ = c⁻¹ * c⁻¹ := by group
    rwa [h5] at h4
  have h6 : c * c ∈ S := by
    have := S.inv_mem h3
    simpa using this
  exact mem_of_sq_mem_of_odd hodd h6

end Central

end CFSG.ClassicalInvolution.Q3.Q3ZB
