module

public import CFSG.GH74.GLS.Stage4.T6SylN

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem Yv_card (h : T6Ctx N u p) (hcard : Nat.card ↥(R₂ N p) = N.q₂ ^ 3) :
    Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {u}) = N.q₂ ∧
      Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {N.z * u}) = N.q₂ := by
  have h1 := R₂_card_RA h
  rw [hcard] at h1
  have hq : 0 < N.q₂ := by have := h.sec5.loc.q₂_ge; omega
  have h2 : Nat.card ↥(RA N p u) ^ 2 = N.q₂ ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hq
    calc N.q₂ * Nat.card ↥(RA N p u) ^ 2 = N.q₂ ^ 3 := h1.symm
      _ = N.q₂ * N.q₂ ^ 2 := by ring
  have h3 : Nat.card ↥(RA N p u) = N.q₂ := (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) h2
  exact ⟨h3, (RA_card_eq_RB h).trans h3⟩

theorem exists_vb (h : T6Ctx N u p) {v : G} (hv : v = u ∨ v = N.z * u) :
    ∃ b : G, b * v * b⁻¹ = N.z ∧ b * N.z * b⁻¹ = N.z * v ∧ b ∈ Subgroup.normalizer (N.H : Set G) ∧
      ∀ w : G, (w = N.w₁ ∨ w = N.w₂) → ∃ k ∈ N.H, b * w * b = k * w := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  obtain ⟨ha1, ha2⟩ := a_conj_facts h
  have hW := h.sec5.weyl
  have haH := hW.a_normH
  have hHa : ∀ k ∈ N.H, N.a * k * N.a⁻¹ ∈ N.H := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 haH k).1 hk
  have hwa : ∀ w : G, (w = N.w₁ ∨ w = N.w₂) → ∃ k ∈ N.H, N.a * w * N.a = k * w := by
    intro w hw
    obtain ⟨k, hk, hwk⟩ : ∃ k ∈ N.H, w * N.a * w⁻¹ = N.a⁻¹ * k := by
      rcases hw with rfl | rfl
      · exact hW.w₁_a
      · exact hW.w₂_a
    refine ⟨k, hk, ?_⟩
    calc N.a * w * N.a = N.a * (w * N.a * w⁻¹) * w := by group
      _ = k * w := by rw [hwk]; group
  have h1 : N.a * (N.z * u) * N.a⁻¹ = u := by
    calc N.a * (N.z * u) * N.a⁻¹ = (N.a * N.z * N.a⁻¹) * (N.a * u * N.a⁻¹) := by group
      _ = (N.z * u) * N.z := by rw [ha2, ha1]
      _ = (u * N.z) * N.z := by rw [hzu]
      _ = u * (N.z * N.z) := by group
      _ = u := by rw [hz2, mul_one]
  rcases hv with rfl | rfl
  · refine ⟨N.a, ha1, ha2, haH, hwa⟩
  · refine ⟨N.a * N.a, ?_, ?_, (Subgroup.normalizer _).mul_mem haH haH, ?_⟩
    · calc N.a * N.a * (N.z * u) * (N.a * N.a)⁻¹ = N.a * (N.a * (N.z * u) * N.a⁻¹) * N.a⁻¹ := by group
        _ = N.z := by rw [h1, ha1]
    · calc N.a * N.a * N.z * (N.a * N.a)⁻¹ = N.a * (N.a * N.z * N.a⁻¹) * N.a⁻¹ := by group
        _ = N.a * (N.z * u) * N.a⁻¹ := by rw [ha2]
        _ = u := h1
        _ = N.z * (N.z * u) := by
          calc u = (N.z * N.z) * u := by rw [hz2, one_mul]
            _ = N.z * (N.z * u) := by group
    · intro w hw
      obtain ⟨k, hk, hwk⟩ := hwa w hw
      refine ⟨N.a * k * N.a⁻¹ * k, N.H.mul_mem (hHa k hk) hk, ?_⟩
      calc N.a * N.a * w * (N.a * N.a) = N.a * (N.a * w * N.a) * N.a := by group
        _ = N.a * (k * w) * N.a := by rw [hwk]
        _ = (N.a * k * N.a⁻¹) * (N.a * w * N.a) := by group
        _ = (N.a * k * N.a⁻¹) * (k * w) := by rw [hwk]
        _ = (N.a * k * N.a⁻¹ * k) * w := by group


omit [Finite G] in
theorem sq_eq_one_of_odd {x : G} (hodd : Odd (orderOf x)) (h : x * x = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
  · exact orderOf_eq_one_iff.1 h4
  · rw [h4] at hodd; exact absurd hodd (by decide)

theorem v_inv_X (h : T6Ctx N u p) {v : G} (hv : v = u ∨ v = N.z * u) :
    (∀ x ∈ N.X₁, v * x * v⁻¹ = x⁻¹) ∧ (∀ x ∈ N.X₂, v * x * v⁻¹ = x⁻¹) := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hz : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  rcases hv with rfl | rfl
  · exact ⟨h.sec5.loc.u_inv_X₁, h.sec5.loc.u_inv_X₂⟩
  · refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h1 := h.sec5.loc.u_inv_X₁ x hx
      have hxz : x * N.z = N.z * x := z_cent_X₁ h hx
      have hxz' : x⁻¹ * N.z = N.z * x⁻¹ := z_cent_X₁ h (N.X₁.inv_mem hx)
      calc N.z * u * x * (N.z * u)⁻¹ = N.z * (u * x * u⁻¹) * N.z⁻¹ := by group
        _ = N.z * x⁻¹ * N.z := by rw [h1, hz]
        _ = x⁻¹ * N.z * N.z := by rw [← hxz']
        _ = x⁻¹ := by rw [mul_assoc, hz2, mul_one]
    · have h1 := h.sec5.loc.u_inv_X₂ x hx
      have hxz' : x⁻¹ * N.z = N.z * x⁻¹ := z_cent_X₂ h (N.X₂.inv_mem hx)
      calc N.z * u * x * (N.z * u)⁻¹ = N.z * (u * x * u⁻¹) * N.z⁻¹ := by group
        _ = N.z * x⁻¹ * N.z := by rw [h1, hz]
        _ = x⁻¹ * N.z * N.z := by rw [← hxz']
        _ = x⁻¹ := by rw [mul_assoc, hz2, mul_one]

theorem v_fix_X (h : T6Ctx N u p) {v : G} (hv : v = u ∨ v = N.z * u) :
    (∀ x ∈ N.X₁, v * x = x * v → x = 1) ∧ (∀ x ∈ N.X₂, v * x = x * v → x = 1) := by
  obtain ⟨h1, h2⟩ := v_inv_X h hv
  have hodd₁ : ∀ x ∈ N.X₁, Odd (orderOf x) := fun x hx => t6_odd_of_pGroup h.prime h.p_ne_two (X₁_pGroup h) hx
  have hodd₂ : ∀ x ∈ N.X₂, Odd (orderOf x) := fun x hx =>
    t6_odd_of_pGroup h.prime h.p_ne_two (R₂_pGroup N h.prime) (X₂_le_R₂ h hx)
  have key : ∀ x : G, (v * x * v⁻¹ = x⁻¹) → Odd (orderOf x) → v * x = x * v → x = 1 := by
    intro x hx hodd hc
    have : v * x * v⁻¹ = x := by rw [hc]; group
    have hxx : x = x⁻¹ := by rw [← hx, this]
    apply sq_eq_one_of_odd hodd
    calc x * x = x * x⁻¹ := by rw [← hxx]
      _ = 1 := by group
  exact ⟨fun x hx hc => key x (h1 x hx) (hodd₁ x hx) hc, fun x hx hc => key x (h2 x hx) (hodd₂ x hx) hc⟩

theorem Yv_facts (h : T6Ctx N u p) {v : G} (hv : v = u ∨ v = N.z * u) :
    (∀ y ∈ R₂ N p ⊓ Subgroup.centralizer {v}, N.z * y * N.z⁻¹ = y⁻¹) ∧
    (∀ y ∈ R₂ N p ⊓ Subgroup.centralizer {v}, ∀ y' ∈ R₂ N p ⊓ Subgroup.centralizer {v}, y * y' = y' * y) ∧
    (∀ k ∈ N.H, ∀ y ∈ R₂ N p ⊓ Subgroup.centralizer {v}, k * y * k⁻¹ ∈ R₂ N p ⊓ Subgroup.centralizer {v}) ∧
    IsPGroup p ↥(R₂ N p ⊓ Subgroup.centralizer {v}) := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  have hz : N.z⁻¹ = N.z := inv_eq_of_mul_eq_one_right hz2
  have hHz : ∀ k ∈ N.H, k * N.z = N.z * k := fun k hk => h.sec5.loc.H_comm k hk N.z h.sec5.loc.z_mem_H
  have hHu : ∀ k ∈ N.H, k * u = u * k := fun k hk => h.sec5.loc.H_comm k hk u h.sec5.loc.u_mem_H
  have hHv : ∀ k ∈ N.H, k * v = v * k := by
    intro k hk
    rcases hv with rfl | rfl
    · exact hHu k hk
    · calc k * (N.z * u) = (k * N.z) * u := by group
        _ = (N.z * k) * u := by rw [hHz k hk]
        _ = N.z * (k * u) := by group
        _ = N.z * (u * k) := by rw [hHu k hk]
        _ = N.z * u * k := by group
  have hzv : N.z * v = v * N.z := by
    rcases hv with rfl | rfl
    · exact hzu
    · calc N.z * (N.z * u) = (N.z * N.z) * u := by group
        _ = u := by rw [hz2, one_mul]
        _ = (N.z * u) * N.z := by
          calc u = u * (N.z * N.z) := by rw [hz2, mul_one]
            _ = (u * N.z) * N.z := by group
            _ = (N.z * u) * N.z := by rw [hzu]
  have hboth : (∀ y ∈ R₂ N p ⊓ Subgroup.centralizer {v}, N.z * y * N.z⁻¹ = y⁻¹) ∧
      (∀ y ∈ R₂ N p ⊓ Subgroup.centralizer {v}, ∀ y' ∈ R₂ N p ⊓ Subgroup.centralizer {v}, y * y' = y' * y) := by
    refine t6_inv_of_fpf (A := R₂ N p ⊓ Subgroup.centralizer {v}) hz2 (fun a ha => ?_) (fun a ha hfix => ?_)
    · refine ⟨R₂_norm N p (z_mem_M₂ h) ha.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hav : a * v = v * a := Subgroup.mem_centralizer_singleton_iff.1 ha.2
      show N.z * a * N.z⁻¹ * v = v * (N.z * a * N.z⁻¹)
      rw [hz]
      calc N.z * a * N.z * v = N.z * a * (N.z * v) := by group
        _ = N.z * a * (v * N.z) := by rw [hzv]
        _ = N.z * (a * v) * N.z := by group
        _ = N.z * (v * a) * N.z := by rw [hav]
        _ = (N.z * v) * a * N.z := by group
        _ = (v * N.z) * a * N.z := by rw [hzv]
        _ = v * (N.z * a * N.z) := by group
    · have haX : a ∈ N.X₂ := R₂_Cz h a ha.1 hfix
      exact (v_fix_X h hv).2 a haX (Subgroup.mem_centralizer_singleton_iff.1 ha.2).symm
  refine ⟨hboth.1, hboth.2, ?_, (R₂_pGroup N h.prime).to_le inf_le_left⟩
  · intro k hk y hy
    refine ⟨R₂_norm N p (H_le_M₂ h hk) hy.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hyv : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
    have hkv := hHv k hk
    have hkv' : k⁻¹ * v = v * k⁻¹ := by
      calc k⁻¹ * v = k⁻¹ * (v * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * v) * k⁻¹ := by rw [hkv]
        _ = v * k⁻¹ := by group
    show k * y * k⁻¹ * v = v * (k * y * k⁻¹)
    calc k * y * k⁻¹ * v = k * y * (k⁻¹ * v) := by group
      _ = k * y * (v * k⁻¹) := by rw [hkv']
      _ = k * (y * v) * k⁻¹ := by group
      _ = k * (v * y) * k⁻¹ := by rw [hyv]
      _ = (k * v) * y * k⁻¹ := by group
      _ = (v * k) * y * k⁻¹ := by rw [hkv]
      _ = v * (k * y * k⁻¹) := by group


theorem v_mem_S (h : T6Ctx N u p) {v : G} (hv : v = u ∨ v = N.z * u) : v ∈ N.S := by
  rcases hv with rfl | rfl
  · exact h.sec5.loc.u_mem_S
  · exact N.S.mul_mem h.sec5.loc.z_mem_S h.sec5.loc.u_mem_S

theorem Yv_K (h : T6Ctx N u p) {v b : G} (hv : v = u ∨ v = N.z * u) (hb1 : b * v * b⁻¹ = N.z)
    (hb2 : b * N.z * b⁻¹ = N.z * v) {y : G} (hy : y ∈ R₂ N p ⊓ Subgroup.centralizer {v}) :
    b * y * b⁻¹ ∈ N.K₁ ⊔ N.K₂ := by
  obtain ⟨hinv, -⟩ := Yv_facts h hv
  have hodd : Odd (orderOf (b * y * b⁻¹)) := by
    have : orderOf (b * y * b⁻¹) = orderOf y := by
      have := MulEquiv.orderOf_eq (MulAut.conj b) y
      simpa [MulAut.conj_apply] using this
    rw [this]
    exact t6_odd_of_pGroup h.prime h.p_ne_two (R₂_pGroup N h.prime) hy.1
  have hyv : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.1 hy.2
  refine t6_pelt_K h ?_ hodd (v := N.z * v)
    (N.S.mul_mem h.sec5.loc.z_mem_S (v_mem_S h hv)) ?_
  · calc b * y * b⁻¹ * N.z = b * y * b⁻¹ * (b * v * b⁻¹) := by rw [hb1]
      _ = b * (y * v) * b⁻¹ := by group
      _ = b * (v * y) * b⁻¹ := by rw [hyv]
      _ = (b * v * b⁻¹) * (b * y * b⁻¹) := by group
      _ = N.z * (b * y * b⁻¹) := by rw [hb1]
  · rw [← hb2]
    calc b * N.z * b⁻¹ * (b * y * b⁻¹) * (b * N.z * b⁻¹)⁻¹ = b * (N.z * y * N.z⁻¹) * b⁻¹ := by group
      _ = b * y⁻¹ * b⁻¹ := by rw [hinv y hy]
      _ = (b * y * b⁻¹)⁻¹ := by group


omit [Finite G] in
theorem map_conj_H_inv {B : Subgroup G} {b : G} (hbH : b ∈ Subgroup.normalizer (N.H : Set G))
    (hBH : ∀ k ∈ N.H, ∀ y ∈ B, k * y * k⁻¹ ∈ B) :
    ∀ k ∈ N.H, ∀ y ∈ B.map (MulAut.conj b).toMonoidHom, k * y * k⁻¹ ∈ B.map (MulAut.conj b).toMonoidHom := by
  intro k hk y hy
  obtain ⟨r, hr, rfl⟩ := hy
  have hbH' : b⁻¹ * k * b ∈ N.H := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hbH) k).1 hk
    simpa using this
  refine ⟨(b⁻¹ * k * b) * r * (b⁻¹ * k * b)⁻¹, hBH _ hbH' r hr, ?_⟩
  show b * ((b⁻¹ * k * b) * r * (b⁻¹ * k * b)⁻¹) * b⁻¹ = k * (b * r * b⁻¹) * k⁻¹
  group

theorem Yv_hinv_card (h : T6Ctx N u p) {v b : G} (hv : v = u ∨ v = N.z * u) (hb1 : b * v * b⁻¹ = N.z)
    (hb2 : b * N.z * b⁻¹ = N.z * v) (hbH : b ∈ Subgroup.normalizer (N.H : Set G)) {B : Subgroup G}
    (hB : B ≤ R₂ N p ⊓ Subgroup.centralizer {v}) (hBH : ∀ k ∈ N.H, ∀ y ∈ B, k * y * k⁻¹ ∈ B) :
    ∃ A₁ A₂ : Subgroup G, A₁ ≤ N.K₁ ∧ A₂ ≤ N.K₂ ∧ B.map (MulAut.conj b).toMonoidHom = A₁ ⊔ A₂ ∧
      Nat.card ↥B = Nat.card ↥A₁ * Nat.card ↥A₂ ∧ (Nat.card ↥A₁ = 1 ∨ Nat.card ↥A₁ = N.q₁) ∧
      (Nat.card ↥A₂ = 1 ∨ Nat.card ↥A₂ = N.q₂) := by
  obtain ⟨-, habel, -, -⟩ := Yv_facts h hv
  set A' : Subgroup G := B.map (MulAut.conj b).toMonoidHom with hA'
  have hmem : ∀ y, y ∈ A' ↔ ∃ r ∈ B, b * r * b⁻¹ = y := by
    intro y
    simp [hA', Subgroup.mem_map]
  have hAK : A' ≤ N.K₁ ⊔ N.K₂ := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := (hmem y).1 hy
    exact Yv_K h hv hb1 hb2 (hB hr)
  have hAp : IsPGroup p ↥A' := ((R₂_pGroup N h.prime).to_le (hB.trans inf_le_left)).map _
  have hAab : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ := (hmem x).1 hx
    obtain ⟨s, hs, rfl⟩ := (hmem y).1 hy
    have := habel r (hB hr) s (hB hs)
    calc b * r * b⁻¹ * (b * s * b⁻¹) = b * (r * s) * b⁻¹ := by group
      _ = b * (s * r) * b⁻¹ := by rw [this]
      _ = b * s * b⁻¹ * (b * r * b⁻¹) := by group
  have hAH : ∀ x ∈ N.H, ∀ y ∈ A', x * y * x⁻¹ ∈ A' := map_conj_H_inv hbH hBH
  obtain ⟨A₁, A₂, h1, h2, h3, h4, h5, h6, -, -⟩ := t6_hinv h hAK hAp hAab hAH
  refine ⟨A₁, A₂, h1, h2, h3, ?_, h5, h6⟩
  rw [← h4, hA', Subgroup.card_map_of_injective (MulAut.conj b).injective]

theorem Yv_pos (h : T6Ctx N u p) (hq : N.q₁ = N.q₂) {v b : G} (hv : v = u ∨ v = N.z * u)
    (hb1 : b * v * b⁻¹ = N.z) (hb2 : b * N.z * b⁻¹ = N.z * v) (hbH : b ∈ Subgroup.normalizer (N.H : Set G))
    (hcard : Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {v}) = N.q₂) :
    (R₂ N p ⊓ Subgroup.centralizer {v}).map (MulAut.conj b).toMonoidHom = N.X₁ ∨
      (R₂ N p ⊓ Subgroup.centralizer {v}).map (MulAut.conj b).toMonoidHom = N.X₁' ∨
      (R₂ N p ⊓ Subgroup.centralizer {v}).map (MulAut.conj b).toMonoidHom = N.X₂ ∨
      (R₂ N p ⊓ Subgroup.centralizer {v}).map (MulAut.conj b).toMonoidHom = N.X₂' := by
  classical
  set Y : Subgroup G := R₂ N p ⊓ Subgroup.centralizer {v} with hY
  obtain ⟨-, habel, hYH, hYp⟩ := Yv_facts h hv
  obtain ⟨A₁, A₂, hA₁, hA₂, hmap, hcardY, hc₁, hc₂⟩ :=
    Yv_hinv_card h hv hb1 hb2 hbH (B := Y) le_rfl hYH
  have hloc := h.sec5.loc
  have hq5 : 5 ≤ N.q₁ := hloc.q₁_ge
  have hAH := map_conj_H_inv hbH hYH
  have hAp : IsPGroup p ↥(Y.map (MulAut.conj b).toMonoidHom) := hYp.map _
  have hcase : (Nat.card ↥A₁ = N.q₁ ∧ Nat.card ↥A₂ = 1) ∨ (Nat.card ↥A₁ = 1 ∧ Nat.card ↥A₂ = N.q₂) := by
    rcases hc₁ with h1 | h1 <;> rcases hc₂ with h2 | h2
    · exfalso
      rw [h1, h2] at hcardY
      omega
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso
      rw [h1, h2, hq] at hcardY
      have h3 : N.q₂ * N.q₂ = N.q₂ * 1 := by rw [← hcardY, hcard, mul_one]
      have := Nat.eq_of_mul_eq_mul_left (by omega) h3
      omega
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hA₂b : A₂ = ⊥ := Subgroup.card_eq_one.1 h2
    have hAeq : Y.map (MulAut.conj b).toMonoidHom = A₁ := by rw [hmap, hA₂b, sup_bot_eq]
    obtain ⟨F, iF, fF, φ, hcF, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₁
    obtain ⟨m, hm⟩ := h.q₁_pow
    have hF : Nat.card F = p ^ m := hcF.trans hm
    have hodd : Odd (Nat.card F) := by rw [hcF]; exact hloc.q₁_odd
    have h5 : 5 ≤ Nat.card F := by rw [hcF]; exact hq5
    have hBr : A₁ ≤ φ.range := by rw [hrange]; exact hA₁
    have hB : IsPGroup p ↥A₁ := by rw [← hAeq]; exact hAp
    have hT : ∀ t ∈ tSub F, ∀ y ∈ A₁, φ t * y * (φ t)⁻¹ ∈ A₁ := by
      intro t ht y hy
      have hφt : φ t ∈ N.H ⊓ N.K₁ := by rw [hHK]; exact Subgroup.mem_map_of_mem φ ht
      have := hAH _ hφt.1 y (by rw [hAeq]; exact hy)
      rwa [hAeq] at this
    have hne : A₁ ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h1
      omega
    rcases t6_pSub_inv hinj h.prime hF hodd h5 hBr hB hT with h' | h' | h'
    · exact absurd h' hne
    · left; rw [hAeq, h', hX]
    · right; left; rw [hAeq, h', hX']
  · have hA₁b : A₁ = ⊥ := Subgroup.card_eq_one.1 h1
    have hAeq : Y.map (MulAut.conj b).toMonoidHom = A₂ := by rw [hmap, hA₁b, bot_sup_eq]
    obtain ⟨F, iF, fF, φ, hcF, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₂
    obtain ⟨m, hm⟩ := h.q₂_pow
    have hF : Nat.card F = p ^ m := hcF.trans hm
    have hodd : Odd (Nat.card F) := by rw [hcF]; exact hloc.q₂_odd
    have h5 : 5 ≤ Nat.card F := by rw [hcF]; omega
    have hBr : A₂ ≤ φ.range := by rw [hrange]; exact hA₂
    have hB : IsPGroup p ↥A₂ := by rw [← hAeq]; exact hAp
    have hT : ∀ t ∈ tSub F, ∀ y ∈ A₂, φ t * y * (φ t)⁻¹ ∈ A₂ := by
      intro t ht y hy
      have hφt : φ t ∈ N.H ⊓ N.K₂ := by rw [hHK]; exact Subgroup.mem_map_of_mem φ ht
      have := hAH _ hφt.1 y (by rw [hAeq]; exact hy)
      rwa [hAeq] at this
    have hne : A₂ ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h2
      omega
    rcases t6_pSub_inv hinj h.prime hF hodd h5 hBr hB hT with h' | h' | h'
    · exact absurd h' hne
    · right; right; left; rw [hAeq, h', hX]
    · right; right; right; rw [hAeq, h', hX']

theorem Yv_inv_sub (h : T6Ctx N u p) (hq : N.q₁ = N.q₂) {v b : G} (hv : v = u ∨ v = N.z * u)
    (hb1 : b * v * b⁻¹ = N.z) (hb2 : b * N.z * b⁻¹ = N.z * v) (hbH : b ∈ Subgroup.normalizer (N.H : Set G))
    (hcard : Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {v}) = N.q₂) {B : Subgroup G}
    (hB : B ≤ R₂ N p ⊓ Subgroup.centralizer {v}) (hBH : ∀ k ∈ N.H, ∀ y ∈ B, k * y * k⁻¹ ∈ B)
    (hB1 : B ≠ ⊥) : B = R₂ N p ⊓ Subgroup.centralizer {v} := by
  obtain ⟨A₁, A₂, -, -, -, hcardB, hc₁, hc₂⟩ := Yv_hinv_card h hv hb1 hb2 hbH hB hBH
  have hle : Nat.card ↥B ≤ N.q₂ := hcard ▸ Subgroup.card_le_of_le hB
  have hq5 : 5 ≤ N.q₁ := h.sec5.loc.q₁_ge
  have hBc : Nat.card ↥B = N.q₂ := by
    rcases hc₁ with h1 | h1 <;> rcases hc₂ with h2 | h2
    · exfalso
      apply hB1
      rw [← Subgroup.card_eq_one]
      rw [h1, h2] at hcardB
      simpa using hcardB
    · rw [hcardB, h1, h2]; simp
    · rw [hcardB, h1, h2, hq]; simp
    · exfalso
      rw [h1, h2, hq] at hcardB
      rw [hcardB] at hle
      have h3 : N.q₂ * N.q₂ ≤ N.q₂ * 1 := by simpa using hle
      have := Nat.le_of_mul_le_mul_left h3 (by omega)
      omega
  exact Subgroup.eq_of_le_of_card_ge hB (by rw [hcard, hBc])


theorem U_norm_X₁ (h : T6Ctx N u p) {g : G} (hg : g ∈ t2U N.z u) {x : G} (hx : x ∈ N.X₁) :
    g * x * g⁻¹ ∈ N.X₁ := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  rcases (t2U_mem hz2 hu2 hzu).1 hg with rfl | rfl | rfl | rfl
  · simpa using hx
  · have := z_cent_X₁ h hx
    rw [show N.z * x * N.z⁻¹ = x by rw [← this]; group]
    exact hx
  · rw [(v_inv_X h (Or.inl rfl)).1 x hx]
    exact N.X₁.inv_mem hx
  · rw [(v_inv_X h (Or.inr rfl)).1 x hx]
    exact N.X₁.inv_mem hx

theorem H_cent_X₁ (h : T6Ctx N u p) {k : G} (hk : k ∈ N.H) {y : G} (hy : ∀ x ∈ N.X₁, x * y = y * x) :
    ∀ x ∈ N.X₁, x * (k * y * k⁻¹) = (k * y * k⁻¹) * x := by
  intro x hx
  have hx' : k⁻¹ * x * k ∈ N.X₁ := by
    have := h.sec5.loc.H_norm_X₁ k⁻¹ (N.H.inv_mem hk) x hx
    simpa using this
  have := hy _ hx'
  calc x * (k * y * k⁻¹) = k * ((k⁻¹ * x * k) * y) * k⁻¹ := by group
    _ = k * (y * (k⁻¹ * x * k)) * k⁻¹ := by rw [this]
    _ = (k * y * k⁻¹) * x := by group

theorem exists_Y (h : T6Ctx N u p) (hq : N.q₁ = N.q₂) (hcard : Nat.card ↥(R₂ N p) = N.q₂ ^ 3)
    (hD : N.X₂ < R₂ N p ⊓ Subgroup.centralizer (N.X₁ : Set G)) :
    ∃ v : G, (v = u ∨ v = N.z * u) ∧
      ∀ y ∈ R₂ N p ⊓ Subgroup.centralizer {v}, ∀ x ∈ N.X₁, x * y = y * x := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  set D : Subgroup G := R₂ N p ⊓ Subgroup.centralizer (N.X₁ : Set G) with hDdef
  have hXD : N.X₂ ≤ D := hD.le
  have hDR : D ≤ R₂ N p := inf_le_left
  have hDX : ∀ y ∈ D, ∀ x ∈ N.X₁, x * y = y * x := fun y hy x hx =>
    Subgroup.mem_centralizer_iff.1 hy.2 x hx
  have hKU : ∀ g ∈ t2U N.z u, ∀ k ∈ D, g * k * g⁻¹ ∈ D := by
    intro g hg k hk
    refine ⟨R₂_norm N p (U_le_M₂ h hg) hk.1, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    have hg' : g⁻¹ ∈ t2U N.z u := (t2U N.z u).inv_mem hg
    have hx' : g⁻¹ * x * g ∈ N.X₁ := by
      have := U_norm_X₁ h hg' hx
      simpa using this
    have := hDX k hk _ hx'
    calc x * (g * k * g⁻¹) = g * ((g⁻¹ * x * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = (g * k * g⁻¹) * x := by group
  have hbw := card_four_decomp h hXD hDR hKU
  have hlt : N.q₂ < Nat.card ↥D := by
    by_contra hnot
    push Not at hnot
    have : N.X₂ = D := Subgroup.eq_of_le_of_card_ge hXD (by rw [h.sec5.loc.card_X₂]; exact hnot)
    exact hD.ne this
  have hq2 : 0 < N.q₂ := by have := h.sec5.loc.q₂_ge; omega
  have hY := Yv_card h hcard
  have key : ∀ v : G, (v = u ∨ v = N.z * u) → Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {v}) = N.q₂ →
      D ⊓ Subgroup.centralizer {v} ≠ ⊥ →
      ∀ y ∈ R₂ N p ⊓ Subgroup.centralizer {v}, ∀ x ∈ N.X₁, x * y = y * x := by
    intro v hv hvc hne y hy x hx
    obtain ⟨b, hb1, hb2, hbH, -⟩ := exists_vb h hv
    obtain ⟨-, -, hYH, -⟩ := Yv_facts h hv
    have hBY : D ⊓ Subgroup.centralizer {v} ≤ R₂ N p ⊓ Subgroup.centralizer {v} :=
      inf_le_inf_right _ hDR
    have hBH : ∀ k ∈ N.H, ∀ y ∈ D ⊓ Subgroup.centralizer {v}, k * y * k⁻¹ ∈ D ⊓ Subgroup.centralizer {v} := by
      intro k hk y hy
      have h1 := hYH k hk y (hBY hy)
      refine ⟨⟨h1.1, Subgroup.mem_centralizer_iff.2 (H_cent_X₁ h hk (hDX y hy.1))⟩, h1.2⟩
    have heq := Yv_inv_sub h hq hv hb1 hb2 hbH hvc hBY hBH hne
    have hyB : y ∈ D ⊓ Subgroup.centralizer {v} := by rw [heq]; exact hy
    exact hDX y hyB.1 x hx
  by_cases h1 : D ⊓ Subgroup.centralizer {u} = ⊥
  · by_cases h2 : D ⊓ Subgroup.centralizer {N.z * u} = ⊥
    · exfalso
      rw [h1, h2, Subgroup.card_bot, mul_one, mul_one] at hbw
      omega
    · exact ⟨N.z * u, Or.inr rfl, key _ (Or.inr rfl) hY.2 h2⟩
  · exact ⟨u, Or.inl rfl, key _ (Or.inl rfl) hY.1 h1⟩

end CFSG.GH74.GLS.Stage4.Rest.T6.P71
