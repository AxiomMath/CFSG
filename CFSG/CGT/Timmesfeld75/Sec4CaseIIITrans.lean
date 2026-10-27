module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIRel

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {U V : Subgroup G}

theorem Cfg.comm_mul_right (c : Cfg U V) {u x y : G} (hu : u ∈ U) (hx : x ∈ normIn V U)
    (hy : y ∈ normIn V U) : ⁅u, x * y⁆ = ⁅u, x⁆ * ⁅u, y⁆ := by
  have hxy : x * ⁅u, y⁆ = ⁅u, y⁆ * x := (c.comm_L_L₁ (c.comm_mem_normIn hu hy) hx).symm
  calc ⁅u, x * y⁆ = ⁅u, x⁆ * (x * ⁅u, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = ⁅u, x⁆ * ⁅u, y⁆ := by rw [mul_inv_eq_iff_eq_mul.2 hxy]

theorem Cfg.comm_inv_right (c : Cfg U V) {u x : G} (hu : u ∈ U) (hx : x ∈ normIn V U) :
    ⁅u, x⁻¹⁆ = ⁅u, x⁆⁻¹ := by
  have h1 := c.comm_mul_right hu hx ((normIn V U).inv_mem hx)
  rw [mul_inv_cancel] at h1
  have h2 : ⁅u, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem Cfg.commutator_conj_eq (c : Cfg U V) {κ : G}
    (hκU : ∀ y ∈ U, κ * y * κ⁻¹ * y⁻¹ ∈ normIn U V) {u v : G} (hu : u ∈ U)
    (hv : v ∈ normIn V U) (hκv : κ * v * κ⁻¹ ∈ normIn V U) :
    ⁅κ, ⁅u, v⁆⁆ = ⁅u, ⁅κ, v⁆⁆ := by
  have hw : κ * u * κ⁻¹ * u⁻¹ ∈ normIn U V := hκU u hu
  have hwv : (κ * u * κ⁻¹ * u⁻¹) * (κ * v * κ⁻¹) = (κ * v * κ⁻¹) * (κ * u * κ⁻¹ * u⁻¹) :=
    c.comm_L_L₁ hw hκv
  have huv : ⁅u, κ * v * κ⁻¹⁆ ∈ normIn U V := c.comm_mem_normIn hu hκv
  have hwc : (κ * u * κ⁻¹ * u⁻¹) * ⁅u, κ * v * κ⁻¹⁆ = ⁅u, κ * v * κ⁻¹⁆ * (κ * u * κ⁻¹ * u⁻¹) :=
    elemAbelian_mul_comm c.wc.1 (normIn_le U V hw) (normIn_le U V huv)
  have h1 : κ * ⁅u, v⁆ * κ⁻¹ = ⁅u, κ * v * κ⁻¹⁆ := by
    set w : G := κ * u * κ⁻¹ * u⁻¹ with hwdef
    set v' : G := κ * v * κ⁻¹ with hv'def
    have e1 : κ * ⁅u, v⁆ * κ⁻¹ = ⁅w * u, v'⁆ := by
      rw [hwdef, hv'def]
      simp only [commutatorElement_def]
      group
    rw [e1]
    have e2 : ⁅w * u, v'⁆ = w * ⁅u, v'⁆ * (v' * w⁻¹ * v'⁻¹) := by
      simp only [commutatorElement_def]
      group
    have e3 : v' * w⁻¹ * v'⁻¹ = w⁻¹ := by
      have := (Commute.inv_left (show Commute w v' from hwv)).eq
      calc v' * w⁻¹ * v'⁻¹ = (w⁻¹ * v') * v'⁻¹ := by rw [this]
        _ = w⁻¹ := by group
    rw [e2, e3, hwc]
    group
  have hκv' : κ * v * κ⁻¹ * v⁻¹ ∈ normIn V U := (normIn V U).mul_mem hκv ((normIn V U).inv_mem hv)
  have h2 : ⁅u, κ * v * κ⁻¹ * v⁻¹⁆ = ⁅u, κ * v * κ⁻¹⁆ * ⁅u, v⁆⁻¹ := by
    rw [c.comm_mul_right hu hκv ((normIn V U).inv_mem hv), c.comm_inv_right hu hv]
  show κ * ⁅u, v⁆ * κ⁻¹ * ⁅u, v⁆⁻¹ = ⁅u, κ * v * κ⁻¹ * v⁻¹⁆
  rw [h2, h1]

theorem Cfg.comm_mem_centralizer_iff (c : Cfg U V) {κ : G}
    (hκU : ∀ y ∈ U, κ * y * κ⁻¹ * y⁻¹ ∈ normIn U V)
    (hκV : ∀ v ∈ normIn V U, κ * v * κ⁻¹ ∈ normIn V U) {u v : G} (hu : u ∈ U)
    (huL : u ∉ normIn U V) (hv : v ∈ normIn V U) :
    κ * v = v * κ ↔ κ * ⁅u, v⁆ = ⁅u, v⁆ * κ := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← commutatorElement_eq_one_iff_mul_comm]
  have hconj := c.commutator_conj_eq hκU hu hv (hκV v hv)
  have hκv : ⁅κ, v⁆ ∈ normIn V U :=
    (normIn V U).mul_mem (hκV v hv) ((normIn V U).inv_mem hv)
  constructor
  · intro h
    rw [hconj, h]
    simp [commutatorElement_def]
  · intro h
    by_contra hne
    exact c.comm_ne_one hu huL hκv hne (by rw [← hconj]; exact h)

theorem Cfg.const_transfer (c : Cfg U V) {κ : G}
    (hκU : ∀ y ∈ U, κ * y * κ⁻¹ * y⁻¹ ∈ normIn U V)
    (hκV : ∀ v ∈ normIn V U, κ * v * κ⁻¹ ∈ normIn V U) {u : G} (hu : u ∈ U)
    (huL : u ∉ normIn U V)
    (hconst : ∀ l ∈ normIn U V, ∀ l' ∈ normIn U V, κ * l ≠ l * κ → κ * l' ≠ l' * κ →
      ⁅κ, l⁆ = ⁅κ, l'⁆) :
    ∀ e ∈ normIn V U, ∀ e' ∈ normIn V U, κ * e ≠ e * κ → κ * e' ≠ e' * κ →
      ⁅κ, e⁆ = ⁅κ, e'⁆ := by
  intro e he e' he' hne hne'
  have h1 : κ * ⁅u, e⁆ ≠ ⁅u, e⁆ * κ := fun h =>
    hne ((c.comm_mem_centralizer_iff hκU hκV hu huL he).2 h)
  have h2 : κ * ⁅u, e'⁆ ≠ ⁅u, e'⁆ * κ := fun h =>
    hne' ((c.comm_mem_centralizer_iff hκU hκV hu huL he').2 h)
  have h3 := hconst _ (c.comm_mem_normIn hu he) _ (c.comm_mem_normIn hu he') h1 h2
  rw [c.commutator_conj_eq hκU hu he (hκV e he), c.commutator_conj_eq hκU hu he' (hκV e' he')] at h3
  have hκe : ⁅κ, e⁆ ∈ normIn V U := (normIn V U).mul_mem (hκV e he) ((normIn V U).inv_mem he)
  have hκe' : ⁅κ, e'⁆ ∈ normIn V U :=
    (normIn V U).mul_mem (hκV e' he') ((normIn V U).inv_mem he')
  have h4 : ⁅u, ⁅κ, e⁆ * ⁅κ, e'⁆⁻¹⁆ = 1 := by
    rw [c.comm_mul_right hu hκe ((normIn V U).inv_mem hκe'), c.comm_inv_right hu hκe', h3]
    group
  by_contra hne2
  have : ⁅κ, e⁆ * ⁅κ, e'⁆⁻¹ ≠ 1 := fun h => hne2 (mul_inv_eq_one.1 h)
  exact c.comm_ne_one hu huL ((normIn V U).mul_mem hκe ((normIn V U).inv_mem hκe')) this h4

theorem Cfg.conj_commutator_eq (c : Cfg U V) {κ : G}
    (hκU : ∀ y ∈ U, κ * y * κ⁻¹ * y⁻¹ ∈ normIn U V) {u v : G} (hu : u ∈ U)
    (hv : v ∈ normIn V U) (hκv : κ * v * κ⁻¹ ∈ normIn V U) :
    u * ⁅κ, v⁆ * u⁻¹ = ⁅κ, ⁅u, v⁆⁆ * ⁅κ, v⁆ := by
  rw [c.commutator_conj_eq hκU hu hv hκv]
  simp only [commutatorElement_def]
  group

end CFSG.CGT.Timmesfeld75
