module

public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open scoped commutatorElement
open CFSG.SectionRank.OddCover

section Commutators

variable {E : Type*} [Group E]

theorem comm_central_mul_left {z a b : E} (hz : z ∈ Subgroup.center E) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.1 hz
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹) * z * z⁻¹ * b⁻¹ := by rw [← h (a * b * a⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_central_mul_right {z a b : E} (hz : z ∈ Subgroup.center E) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff.1 hz a]
  exact comm_central_mul_left hz

theorem comm_mul_central_left {z a b : E} (hz : z ∈ Subgroup.center E) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, comm_central_mul_left hz, commutatorElement_inv]

theorem comm_mul_central_right {z a b : E} (hz : z ∈ Subgroup.center E) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff.1 hz b]
  exact comm_mul_central_left hz

theorem conj_comm (h a b : E) : h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right_eq (s a b : E) : ⁅s, a * b⁆ = ⁅s, a⁆ * (a * ⁅s, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem conj_of_mem_center {z : E} (hz : z ∈ Subgroup.center E) (a : E) : a * z * a⁻¹ = z := by
  rw [Subgroup.mem_center_iff.1 hz a, mul_inv_cancel_right]

theorem comm_comm_eq_one_of_mem_center {a b y : E} (ha : ⁅a, y⁆ ∈ Subgroup.center E)
    (hb : ⁅b, y⁆ ∈ Subgroup.center E) : ⁅⁅a, b⁆, y⁆ = 1 := by
  have ha' : ⁅y, a⁆ ∈ Subgroup.center E := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ ha
  have hb' : ⁅y, b⁆ ∈ Subgroup.center E := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ hb
  have e1 : y * a * y⁻¹ = ⁅y, a⁆ * a := by rw [commutatorElement_def]; group
  have e2 : y * b * y⁻¹ = ⁅y, b⁆ * b := by rw [commutatorElement_def]; group
  have h : y * ⁅a, b⁆ * y⁻¹ = ⁅a, b⁆ := by
    rw [conj_comm, e1, e2, comm_central_mul_left ha', comm_mul_central_left hb']
  rw [commutatorElement_eq_one_iff_mul_comm]
  calc ⁅a, b⁆ * y = (y * ⁅a, b⁆ * y⁻¹) * y := by rw [h]
    _ = y * ⁅a, b⁆ := by group

theorem conj_conj_comm_of_comm_mem_center {g z : E} (h : ⁅g, z⁆ ∈ Subgroup.center E) (y : E) :
    g * (z * y * z⁻¹) * g⁻¹ = z * (g * y * g⁻¹) * z⁻¹ := by
  have e1 : g * z * g⁻¹ = ⁅g, z⁆ * z := by rw [commutatorElement_def]; group
  calc g * (z * y * z⁻¹) * g⁻¹ = (g * z * g⁻¹) * (g * y * g⁻¹) * (g * z * g⁻¹)⁻¹ := by group
    _ = ⁅g, z⁆ * (z * (g * y * g⁻¹) * z⁻¹) * ⁅g, z⁆⁻¹ := by rw [e1]; group
    _ = z * (g * y * g⁻¹) * z⁻¹ := by
      rw [← Subgroup.mem_center_iff.1 h _, mul_inv_cancel_right]

end Commutators

section Lifts

variable {E X : Type*} [Group E] [Group X] {π : E →* X}

theorem comm_mem_ker_of_commute {a b : E} (h : Commute (π a) (π b)) : ⁅a, b⁆ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 h.eq

theorem comm_mem_center_of_commute_map (hcen : π.ker ≤ Subgroup.center E) {a b : E}
    (h : Commute (π a) (π b)) : ⁅a, b⁆ ∈ Subgroup.center E :=
  hcen (comm_mem_ker_of_commute h)

theorem comm_eq_of_map_eq (hcen : π.ker ≤ Subgroup.center E) {a a' b b' : E}
    (ha : π a = π a') (hb : π b = π b') : ⁅a, b⁆ = ⁅a', b'⁆ := by
  have h1 : a' = (a' * a⁻¹) * a := by group
  have h2 : b' = (b' * b⁻¹) * b := by group
  have hk1 : a' * a⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ha, mul_inv_cancel]
  have hk2 : b' * b⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb, mul_inv_cancel]
  rw [h1, h2, comm_central_mul_left (hcen hk1), comm_mul_central_left (hcen hk2)]

theorem exists_lift_pow_eq_one (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    {z : X} {m : ℕ} (hz : z ^ m = 1) (hm : Nat.Coprime m (Nat.card π.ker)) :
    ∃ e : E, π e = z ∧ e ^ m = 1 := by
  obtain ⟨e, he⟩ := hπ z
  have hc : e ^ m ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, he, hz]
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * Nat.card π.ker = 1 :=
    Nat.isCoprime_iff_coprime.2 hm
  have hcpow : (e ^ m) ^ (Nat.card π.ker) = 1 := by
    have := pow_card_eq_one' (G := π.ker) (x := ⟨e ^ m, hc⟩)
    exact congrArg Subtype.val this
  have hc' : (e ^ m) ^ a ∈ π.ker := π.ker.zpow_mem hc a
  have hcomm : Commute e ((e ^ m) ^ a) := Subgroup.mem_center_iff.1 (hcen hc') e
  refine ⟨e * ((e ^ m) ^ a)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, he, MonoidHom.mem_ker.1 hc', inv_one, mul_one]
  · have h1 : ((e ^ m) ^ a) ^ m = (e ^ m) ^ (a * m) := by rw [← zpow_natCast, ← zpow_mul]
    calc (e * ((e ^ m) ^ a)⁻¹) ^ m = e ^ m * (((e ^ m) ^ a) ^ m)⁻¹ := by
          rw [(hcomm.inv_right).mul_pow, inv_pow]
      _ = (e ^ m) ^ (1 - a * m) := by
          rw [h1, zpow_sub, zpow_one]
      _ = (e ^ m) ^ (b * Nat.card π.ker) := by congr 1; linarith
      _ = 1 := by rw [mul_comm b, zpow_mul, zpow_natCast, hcpow, one_zpow]

end Lifts

section Vanishing

variable {E : Type*} [Group E]

theorem comm_eq_one_of_conj_surj {s h : E} {Y : Subgroup E}
    (hs : ∀ y ∈ Y, ⁅s, y⁆ ∈ Subgroup.center E) (hY : ∀ y ∈ Y, h * y * h⁻¹ ∈ Y)
    (hh : ⁅h, s⁆ ∈ Subgroup.center E)
    (hsurj : ∀ y ∈ Y, ∃ y₁ ∈ Y, ∃ w : E, ⁅s, w⁆ = 1 ∧ y = w * (h * y₁ * h⁻¹ * y₁⁻¹)) :
    ∀ y ∈ Y, ⁅s, y⁆ = 1 := by
  intro y hy
  obtain ⟨y₁, hy₁, w, hw, rfl⟩ := hsurj y hy
  have hv : h * y₁ * h⁻¹ * y₁⁻¹ ∈ Y := Y.mul_mem (hY y₁ hy₁) (Y.inv_mem hy₁)
  have hc₁ := hs y₁ hy₁
  have hsh : h⁻¹ * s * h = (⁅h, s⁆)⁻¹ * s := by
    have e1 : h * s * h⁻¹ = ⁅h, s⁆ * s := by rw [commutatorElement_def]; group
    have e2 : s = ⁅h, s⁆ * (h⁻¹ * s * h) := by
      calc s = h⁻¹ * (h * s * h⁻¹) * h := by group
        _ = h⁻¹ * (⁅h, s⁆ * s) * h := by rw [e1]
        _ = (h⁻¹ * ⁅h, s⁆ * h) * (h⁻¹ * s * h) := by group
        _ = ⁅h, s⁆ * (h⁻¹ * s * h) := by
          have := conj_of_mem_center hh h⁻¹
          rw [inv_inv] at this
          rw [this]
    exact (inv_mul_eq_of_eq_mul e2).symm
  have h2 : ⁅h⁻¹ * s * h, y₁⁆ = ⁅s, y₁⁆ := by
    rw [hsh, comm_central_mul_left (Subgroup.inv_mem _ hh)]
  have hc₂ : ⁅s, h * y₁ * h⁻¹⁆ = ⁅s, y₁⁆ := by
    have e1 := conj_comm h⁻¹ s (h * y₁ * h⁻¹)
    rw [show h⁻¹ * (h * y₁ * h⁻¹) * h⁻¹⁻¹ = y₁ by group, inv_inv, h2] at e1
    have e2 : ⁅s, h * y₁ * h⁻¹⁆ = h * (h⁻¹ * ⁅s, h * y₁ * h⁻¹⁆ * h) * h⁻¹ := by group
    rw [e2, e1, conj_of_mem_center hc₁]
  have hc₃ : ⁅s, y₁⁻¹⁆ = ⁅s, y₁⁆⁻¹ := by
    have := comm_mul_right_eq s y₁ y₁⁻¹
    rw [mul_inv_cancel, commutatorElement_one_right, conj_of_mem_center (by
      have := hs y₁⁻¹ (Y.inv_mem hy₁)
      exact this) y₁] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hcv : ⁅s, h * y₁ * h⁻¹ * y₁⁻¹⁆ = 1 := by
    rw [comm_mul_right_eq, hc₂, hc₃, conj_of_mem_center (Subgroup.inv_mem _ hc₁), mul_inv_cancel]
  rw [comm_mul_right_eq, hw, one_mul, conj_of_mem_center (hs _ hv), hcv]

end Vanishing

end CFSG.ClassicalInvolution.ModelFacts.OddCover
