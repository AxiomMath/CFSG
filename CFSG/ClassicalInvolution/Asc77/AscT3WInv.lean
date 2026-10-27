module

public import CFSG.ClassicalInvolution.Asc77.AscT3WMod
public import CFSG.ClassicalInvolution.Asc77.AscT3WStmt
public import CFSG.ClassicalInvolution.Asc77.AscT3WGood
public import CFSG.ClassicalInvolution.AschTight.Sec7L98C

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.w_conj_t (d : Std20 p f K K' J S R R' W V z t) {r : G} (hrR : r ∈ R)
    (hrW : r ∉ W) : r * t * r⁻¹ = z * t := by
  have hc := d.late_cfg98 d.late_JW
  obtain ⟨u, v, T, hu, hv, tor⟩ := Sec7.Cfg98.exists_tor hc Sec6Gen.l6_4ThreeGenAll
  refine tor.he1 r (by rw [← d.late_R_eq]; exact hrR) fun h => hrW ?_
  have : r ∈ K ⊓ W := hu ▸ h
  exact this.2

theorem Std20.w_conj_facts (d : Std20 p f K K' J S R R' W V z t) {r : G} (hrR : r ∈ R)
    (hrW : r ∉ W) : (∀ x ∈ K ⊓ W, r * x * r⁻¹ = x⁻¹) ∧ r * r = z := by
  obtain ⟨u, hu, hdK⟩ := d.w_dData hrR hrW
  refine ⟨fun x hx => ?_, hdK.sq_r⟩
  rw [← hu] at hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hdK.conj_u, inv_zpow]

theorem Std20.w_tinv (d : Std20 p f K K' J S R R' W V z t) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hb2 : b * b = 1)
    (hbX : b ∉ sec20X (CoreAssembly.conjClass K) z K K') {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) {r : G} (hrR : r ∈ R)
    (hrW : r ∉ W) (hra : b * r = r * b) :
    ∃ b' ∈ (S : Subgroup G), b' * b' = 1 ∧
      b' ∉ sec20X (CoreAssembly.conjClass K) z K K' ∧ b' * t = t * b' ∧
      ((∀ x ∈ K ⊓ W, b' * x * b'⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
        ∀ x ∈ K ⊓ W, b' * x * b'⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) := by
  have hWc := d.late_hWc
  have hI := d.viol.hzK
  have htW := d.late_t_mem_W
  have hzW := d.late_z_mem_W
  have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hbS)
  rcases d.late_S_act_t hbS with hat | hat
  · refine ⟨b, hbS, hb2, hbX, ?_, Or.inl hact⟩
    calc b * t = b * t * b⁻¹ * b := by group
      _ = t * b := by rw [hat]
  obtain ⟨hrinv, hr2⟩ := d.w_conj_facts hrR hrW
  have hrt := d.w_conj_t hrR hrW
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hzu : z = u ^ 2 ^ k := by
    have h := (w_isUniqueInvolution_zpowers huo).unique z (hu ▸ ⟨hI.mem, hzW⟩) hI.sq
    exact h.resolve_left hI.ne_one
  have hu2k : u ^ ((2 : ℤ) ^ k + 1) = u * z := by
    rw [zpow_add_one, show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hzu,
      hWc _ hzW _ huKW.2]
  have hrz : r * z = z * r := by rw [← hr2, ← mul_assoc]
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hur : b * (u * r) * b⁻¹ = (u * r)⁻¹ := by
    have h1 : b * (u * r) * b⁻¹ = (b * u * b⁻¹) * (b * r * b⁻¹) := by group
    have h2 : b * r * b⁻¹ = r := by rw [hra]; group
    have h3 : r⁻¹ = r * z := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hr2, hI.sq]
    have h4 : r⁻¹ * u⁻¹ = u * r⁻¹ := by
      have := hrinv u huKW
      calc r⁻¹ * u⁻¹ = r⁻¹ * (r * u * r⁻¹) := by rw [this]
        _ = u * r⁻¹ := by group
    rw [h1, h2, hact u huKW, hu2k, mul_inv_rev, h4, h3]
    calc u * z * r = u * (z * r) := by group
      _ = u * (r * z) := by rw [hrz]
  have hur_mem : u * r ∈ K := K.mul_mem huKW.1 (d.hR.1 hrR)
  refine ⟨b * (u * r), (S : Subgroup G).mul_mem hbS ((S : Subgroup G).mul_mem
    (d.hWS huKW.2) (d.hRS hrR)), ?_, ?_, ?_, Or.inr fun x hx => ?_⟩
  · calc b * (u * r) * (b * (u * r)) = (b * (u * r) * b⁻¹) * (u * r) := by
          rw [hbi]; group
      _ = 1 := by rw [hur, inv_mul_cancel]
  · intro h
    apply hbX
    have hur' : (u * r)⁻¹ ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
      le_sec20X_left (K.inv_mem hur_mem)
    have := (sec20X (CoreAssembly.conjClass K) z K K').mul_mem h hur'
    rwa [mul_inv_cancel_right] at this
  · have hzt : z * t ∈ W := W.mul_mem hzW htW
    have e1 : (u * r) * t * (u * r)⁻¹ = z * t := by
      calc (u * r) * t * (u * r)⁻¹ = u * (r * t * r⁻¹) * u⁻¹ := by group
        _ = u * (z * t) * u⁻¹ := by rw [hrt]
        _ = z * t := by rw [hWc u huKW.2 _ hzt]; group
    have e2 : b * (u * r) * t * (b * (u * r))⁻¹ = t := by
      calc b * (u * r) * t * (b * (u * r))⁻¹ = b * ((u * r) * t * (u * r)⁻¹) * b⁻¹ := by group
        _ = (b * z * b⁻¹) * (b * t * b⁻¹) := by rw [e1]; group
        _ = z * (z * t) := by rw [hat, show b * z * b⁻¹ = z by rw [hbz]; group]
        _ = t := by rw [← mul_assoc, hI.sq, one_mul]
    calc b * (u * r) * t = b * (u * r) * t * (b * (u * r))⁻¹ * (b * (u * r)) := by group
      _ = t * (b * (u * r)) := by rw [e2]
  · have hx' : u * r * x * (u * r)⁻¹ = x⁻¹ := by
      calc u * r * x * (u * r)⁻¹ = u * (r * x * r⁻¹) * u⁻¹ := by group
        _ = u * x⁻¹ * u⁻¹ := by rw [hrinv x hx]
        _ = x⁻¹ := by rw [hWc u huKW.2 _ (W.inv_mem hx.2)]; group
    have hxo : x ^ ((2 : ℤ) ^ (k + 1)) = 1 := by
      rw [← hu] at hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_mul, mul_comm, zpow_mul, show ((2 : ℤ) ^ (k + 1)) = ((2 ^ (k + 1) : ℕ) : ℤ) by
        push_cast; ring, zpow_natCast, ← huo, pow_orderOf_eq_one, one_zpow]
    calc b * (u * r) * x * (b * (u * r))⁻¹ = b * (u * r * x * (u * r)⁻¹) * b⁻¹ := by group
      _ = (b * x * b⁻¹)⁻¹ := by rw [hx']; group
      _ = (x ^ ((2 : ℤ) ^ k + 1))⁻¹ := by rw [hact x hx]
      _ = x ^ ((2 : ℤ) ^ k - 1) * (x ^ ((2 : ℤ) ^ (k + 1)))⁻¹ := by
          rw [← zpow_neg, ← zpow_neg, ← zpow_add]
          congr 1
          ring
      _ = x ^ ((2 : ℤ) ^ k - 1) := by rw [hxo, inv_one, mul_one]

theorem Std20.w_exists_inv (d : Std20 p f K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z)
    {a₀ : G} (haS : a₀ ∈ (S : Subgroup G)) (ha2 : a₀ * a₀ = 1)
    (haX : a₀ ∉ sec20X (CoreAssembly.conjClass K) z K K')
    (hFK : InducesFAut K R a₀) (hFK' : InducesFAut K' R' a₀) :
    ∃ b : G, FieldInv20 S K K' W z t b := by
  obtain ⟨b₁, hb₁S, hb₁2, hb₁X, hF1, -, Q, hQR, hQb, hQq, hQcard⟩ :=
    d.w_good haS ha2 haX hFK hFK'
  obtain ⟨u, k, hk, hu, huo, hact, r, hrR, hrW, hra⟩ :=
    d.w_modular c7 hb₁S hb₁X hF1.1 hQR hQb (isQuatSub_not_isCyclic hQq) hQq.eight_le hQcard
  obtain ⟨b, hbS, hb2, hbX, hbt, hbmod⟩ := d.w_tinv hb₁S hb₁2 hb₁X hu huo hact hrR hrW hra
  have hat : b * t * b⁻¹ = t := by
    calc b * t * b⁻¹ = t * b * b⁻¹ := by rw [hbt]
      _ = t := by group
  obtain ⟨c, hcb, hcz⟩ := d.v_conj_t hbS hb2 hat hk hu huo hbmod
  exact ⟨b, hbS, hb2, hbX, hbt, ⟨c, hcb, hcz⟩, u, k, hk, hu, huo, hbmod⟩

end Std

variable (p f : ℕ) [Fact p.Prime]


theorem res10aInv'_proved : Res10aInv' p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8
  obtain ⟨a₀, haS, ha2, haX, hFK, hFK'⟩ :=
    res10aInv p f G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8
  exact d.w_exists_inv c7 haS ha2 haX hFK hFK'

end CFSG.ClassicalInvolution.Asc77.T3CII
