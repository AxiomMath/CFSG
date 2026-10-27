module

public import CFSG.CGT.Foote81L6.Bridge.Core

public section

namespace CFSG.CGT.Foote81L6.Bridge

open Subgroup

namespace Gen

variable (n : ℕ)

@[expose] def hC : PHat n := κ₀ n * κ₁ n * b₁H n * s n

@[expose] def tC : PHat n := κ₀ n * κ₁ n

variable {n} (hn : 3 ≤ n)
include hn

theorem hC_mul_hC : hC n * hC n = (ρ₀ n)⁻¹ * (ρ₁ n)⁻¹ * cz n := by
  ext <;> simp only [hC, κ₀, κ₁, b₁H, s, ρ₀, ρ₁, cz, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃,
      PHat.mul_e, PHat.inv_x₁, PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one,
      PHat.sw₂_zero, PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i,
      SD.mul_j, SD.inv_i, SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr,
      SD.σ, SD.ω, SD.z, add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem t_mul_hC : t n * hC n = hC n * t n := by
  ext <;> simp only [hC, κ₀, κ₁, b₁H, s, t, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃,
      PHat.mul_e, PHat.inv_x₁, PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one,
      PHat.sw₂_zero, PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i,
      SD.mul_j, SD.inv_i, SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr,
      SD.σ, SD.ω, SD.z, add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

theorem tC_mul_hC : tC n * hC n = (hC n)⁻¹ * b₀H n * b₁H n * tC n := by
  ext <;> simp only [hC, tC, κ₀, κ₁, b₀H, b₁H, s, PHat.mul_x₁, PHat.mul_x₂, PHat.mul_x₃,
      PHat.mul_e, PHat.inv_x₁, PHat.inv_x₂, PHat.inv_x₃, PHat.inv_e, PHat.sw₁_zero, PHat.sw₁_one,
      PHat.sw₂_zero, PHat.sw₂_one, PHat.one_x₁, PHat.one_x₂, PHat.one_x₃, PHat.one_e, SD.mul_i,
      SD.mul_j, SD.inv_i, SD.inv_j, SD.one_i, SD.one_j, tw_zero, tw_one, θ, hf_eq_two_mul_qr,
      SD.σ, SD.ω, SD.z, add_zero, zero_add, PHat.one_add_one_zmod_two] <;> qr_close n hn

end Gen

variable {n : ℕ} (hn : 3 ≤ n)
include hn

omit hn in
theorem conj_mul_conj_inv {G : Type*} [Group G] (g x y : G) :
    g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group

theorem w_conj_ρ₀T : sT n * tT n * ρ₀T n * (sT n * tT n)⁻¹ = ρ₀T n ^ (θ n).val := by
  rw [mul_inv_rev, show sT n * tT n * ρ₀T n * ((tT n)⁻¹ * (sT n)⁻¹) =
    sT n * (tT n * ρ₀T n * (tT n)⁻¹) * (sT n)⁻¹ by group, tT_conj_ρ₀T hn, sT_conj_ρ₁T hn]

theorem w_conj_κ₀T : sT n * tT n * κ₀T n * (sT n * tT n)⁻¹ = κ₀T n * ρ₀T n ^ (2 ^ (n - 2) - 1) := by
  rw [mul_inv_rev, show sT n * tT n * κ₀T n * ((tT n)⁻¹ * (sT n)⁻¹) =
    sT n * (tT n * κ₀T n * (tT n)⁻¹) * (sT n)⁻¹ by group, tT_conj_κ₀T hn, sT_conj_κ₁T hn]

theorem w_conj_mem_B₀T {u : TM n} (hu : u ∈ B₀T hn) :
    sT n * tT n * u * (sT n * tT n)⁻¹ ∈ B₀T hn := by
  rw [mul_inv_rev, show sT n * tT n * u * ((tT n)⁻¹ * (sT n)⁻¹) =
    sT n * (tT n * u * (tT n)⁻¹) * (sT n)⁻¹ by group]
  exact conj_sT_mem_B₀T hn (conj_tT_mem_B₁T hn hu)

theorem w_conj_mem_B₁T {v : TM n} (hv : v ∈ B₁T hn) :
    sT n * tT n * v * (sT n * tT n)⁻¹ ∈ B₁T hn := by
  rw [mul_inv_rev, show sT n * tT n * v * ((tT n)⁻¹ * (sT n)⁻¹) =
    sT n * (tT n * v * (tT n)⁻¹) * (sT n)⁻¹ by group]
  exact conj_sT_mem_B₁T hn (conj_tT_mem_B₀T hn hv)

theorem w_mul_w : sT n * tT n * (sT n * tT n) = b₀T hn * b₁T hn := by
  have h := tT_conj_sT hn
  rw [← b₀T_eq hn, ← b₁T_eq hn] at h
  calc sT n * tT n * (sT n * tT n) = sT n * (tT n * sT n * (tT n)⁻¹) * (tT n * tT n) := by
        group
    _ = b₀T hn * b₁T hn := by
        rw [h, tT_mul_tT hn, mul_one, ← mul_assoc, ← mul_assoc, sT_mul_sT hn, one_mul]

theorem mul_w_conj_mul_b₀T_ne_one {u : TM n} (hu : u ∈ B₀T hn) :
    u * (sT n * tT n * u * (sT n * tT n)⁻¹) * b₀T hn ≠ 1 := by
  have hord := orderOf_ρ₀T hn
  have hθ : (θ n).val = 2 ^ (n - 1) - 1 := θ_val (by omega)
  obtain ⟨i, rfl | rfl⟩ := (mem_dihedralLift_range_iff _ _ _ _ _ _).1 hu
  · rw [← conj_pow, w_conj_ρ₀T hn, ← pow_mul, ← pow_add, b₀T_eq hn, ← pow_add, hθ]
    intro h
    apply ρ₀T_pow_qr_ne_one hn
    rw [← h, show i.val + (2 ^ (n - 1) - 1) * i.val + 2 ^ (n - 2) =
      2 ^ (n - 1) * i.val + 2 ^ (n - 2) by
        have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        zify [this]; ring, pow_add, pow_mul, ρ₀T_pow_hf hn, one_pow, one_mul]
  · intro h
    have hκinv : (κ₀T n)⁻¹ = κ₀T n := inv_eq_of_mul_eq_one_right (κ₀T_mul_κ₀T hn)
    have hκρ : ∀ k : ℕ, κ₀T n * ρ₀T n ^ k * κ₀T n = (ρ₀T n)⁻¹ ^ k := by
      intro k
      calc κ₀T n * ρ₀T n ^ k * κ₀T n = κ₀T n * ρ₀T n ^ k * (κ₀T n)⁻¹ := by rw [hκinv]
        _ = (κ₀T n * ρ₀T n * (κ₀T n)⁻¹) ^ k := conj_pow.symm
        _ = (ρ₀T n)⁻¹ ^ k := by rw [κ₀T_conj_ρ₀T hn]
    have hconj : sT n * tT n * (κ₀T n * ρ₀T n ^ i.val) * (sT n * tT n)⁻¹ =
        κ₀T n * ρ₀T n ^ (2 ^ (n - 2) - 1) * (ρ₀T n ^ (θ n).val) ^ i.val := by
      rw [show sT n * tT n * (κ₀T n * ρ₀T n ^ i.val) * (sT n * tT n)⁻¹ =
        (sT n * tT n * κ₀T n * (sT n * tT n)⁻¹) * (sT n * tT n * ρ₀T n ^ i.val *
          (sT n * tT n)⁻¹) by group, ← conj_pow, w_conj_κ₀T hn, w_conj_ρ₀T hn]
    rw [hconj, b₀T_eq hn] at h
    have h2 : (ρ₀T n)⁻¹ ^ i.val * ρ₀T n ^ (2 ^ (n - 2) - 1) * (ρ₀T n ^ (θ n).val) ^ i.val *
        ρ₀T n ^ 2 ^ (n - 2) = 1 := by
      rw [← hκρ, ← h]
      group
    generalize i.val = k at h2
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, inv_zpow', ← zpow_add, ← zpow_add, ← zpow_add, ← orderOf_dvd_iff_zpow_eq_one,
      hord, hθ] at h2
    obtain ⟨P, hPdef⟩ : ∃ P, P = 2 ^ (n - 2) := ⟨_, rfl⟩
    have hP1 : 2 ^ (n - 1) = 2 * P := by rw [hPdef, ← pow_succ']; congr 1; omega
    have hPpos : 1 ≤ P := hPdef ▸ Nat.one_le_two_pow
    rw [hP1, ← hPdef] at h2
    have h5 : (2 : ℤ) ∣ -(k : ℤ) + ((P - 1 : ℕ) : ℤ) + ((2 * P - 1 : ℕ) : ℤ) * k + P :=
      (show (2 : ℤ) ∣ ((2 * P : ℕ) : ℤ) by push_cast; exact dvd_mul_right 2 _).trans h2
    rw [Nat.cast_sub hPpos, Nat.cast_sub (by omega : 1 ≤ 2 * P)] at h5
    push_cast at h5
    rw [show -(k : ℤ) + ((P : ℤ) - 1) + (2 * (P : ℤ) - 1) * k + P =
      2 * ((P : ℤ) + P * k - k) - 1 by ring] at h5
    generalize (P : ℤ) + P * k - k = Y at h5
    omega

theorem Bt_conj : ∀ x ∈ BT hn, (x * tT n) ^ 2 = 1 → ∃ y ∈ BT hn, y * (x * tT n) * y⁻¹ = tT n := by
  intro x hx hx2
  have ht2 := tT_mul_tT hn
  have htinv := tT_inv hn
  rcases (mem_BT_iff hn).1 hx with ⟨u, hu, v, hv, rfl⟩ | ⟨u, hu, v, hv, rfl⟩
  ·
    have htu : tT n * u * (tT n)⁻¹ ∈ B₁T hn := conj_tT_mem_B₁T hn hu
    have htv : tT n * v * (tT n)⁻¹ ∈ B₀T hn := conj_tT_mem_B₀T hn hv
    have hc1 := B₀T_comm_B₁T hn _ htv _ hv
    have hc2 := B₀T_comm_B₁T hn _ htv _ htu
    have hsq : (u * (tT n * v * (tT n)⁻¹)) * (v * (tT n * u * (tT n)⁻¹)) = 1 := by
      rw [← hx2]
      calc (u * (tT n * v * (tT n)⁻¹)) * (v * (tT n * u * (tT n)⁻¹))
          = u * ((tT n * v * (tT n)⁻¹) * v) * (tT n * u * (tT n)⁻¹) := by group
        _ = u * v * ((tT n * v * (tT n)⁻¹) * (tT n * u * (tT n)⁻¹)) := by rw [hc1]; group
        _ = u * v * ((tT n * u * (tT n)⁻¹) * (tT n * v * (tT n)⁻¹)) := by rw [hc2]
        _ = u * v * tT n * (u * v * (tT n)⁻¹) := by group
        _ = (u * v * tT n) ^ 2 := by rw [htinv, pow_two]
    have h0 : u * (tT n * v * (tT n)⁻¹) = 1 := by
      have hmem : u * (tT n * v * (tT n)⁻¹) ∈ B₀T hn ⊓ B₁T hn := by
        refine Subgroup.mem_inf.2 ⟨mul_mem hu htv, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hsq]
        exact inv_mem (mul_mem hv htu)
      rw [B₀T_inf_B₁T hn, mem_bot] at hmem
      exact hmem
    refine ⟨u⁻¹, B₀T_le_BT hn (inv_mem hu), ?_⟩
    have hv' : v = (tT n)⁻¹ * u⁻¹ * tT n := by
      have := eq_inv_of_mul_eq_one_right h0
      rw [← this]
      group
    rw [hv', inv_inv]
    calc u⁻¹ * (u * ((tT n)⁻¹ * u⁻¹ * tT n) * tT n) * u =
        (tT n)⁻¹ * u⁻¹ * (tT n * tT n) * u := by group
      _ = tT n := by rw [ht2, mul_one, inv_mul_cancel_right, htinv]
  ·
    exfalso
    set w := sT n * tT n with hw
    have hwu := w_conj_mem_B₀T hn hu
    have hwv := w_conj_mem_B₁T hn hv
    have hb₀ := b₀T_mem hn
    have hb₁ := b₁T_mem hn
    have c1 := B₀T_comm_B₁T hn _ hwu _ hv
    have c2 := B₀T_comm_B₁T hn _ hb₀ _ hv
    have c3 := B₀T_comm_B₁T hn _ hb₀ _ hwv
    have hsq : (u * (w * u * w⁻¹) * b₀T hn) * (v * (w * v * w⁻¹) * b₁T hn) = 1 := by
      rw [← hx2]
      calc (u * (w * u * w⁻¹) * b₀T hn) * (v * (w * v * w⁻¹) * b₁T hn)
          = u * (w * u * w⁻¹) * (b₀T hn * v) * (w * v * w⁻¹) * b₁T hn := by group
        _ = u * (w * u * w⁻¹) * (v * b₀T hn) * (w * v * w⁻¹) * b₁T hn := by rw [c2]
        _ = u * ((w * u * w⁻¹) * v) * (b₀T hn * (w * v * w⁻¹)) * b₁T hn := by group
        _ = u * (v * (w * u * w⁻¹)) * ((w * v * w⁻¹) * b₀T hn) * b₁T hn := by rw [c1, c3]
        _ = u * v * (w * u * w⁻¹) * (w * v * w⁻¹) * (b₀T hn * b₁T hn) := by group
        _ = u * v * (w * u * w⁻¹) * (w * v * w⁻¹) * (w * w) := by rw [hw, w_mul_w hn]
        _ = (u * v * sT n * tT n) ^ 2 := by rw [pow_two, hw]; group
    have h0 : u * (w * u * w⁻¹) * b₀T hn = 1 := by
      have hmem : u * (w * u * w⁻¹) * b₀T hn ∈ B₀T hn ⊓ B₁T hn := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hu hwu) hb₀, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hsq]
        exact inv_mem (mul_mem (mul_mem hv hwv) hb₁)
      rw [B₀T_inf_B₁T hn, mem_bot] at hmem
      exact hmem
    exact mul_w_conj_mul_b₀T_ne_one hn hu h0

@[expose] noncomputable def hCT : TM n := κ₀T n * κ₁T n * b₁T hn * sT n

omit hn in
@[expose] def tCT (n : ℕ) : TM n := κ₀T n * κ₁T n

omit hn in
theorem Gen.det_b₁H : (Gen.b₁H n).det = 0 := by
  rw [PHat.det, Gen.b₁H]
  simp only [SD.det_mk, SD.det_one, add_zero, par_neg]
  exact CharTwo.add_self_eq_zero _

omit hn in
theorem Gen.det_b₀H : (Gen.b₀H n).det = 0 := by
  rw [PHat.det, Gen.b₀H]
  simp only [SD.det_mk, SD.det_one, add_zero]
  exact CharTwo.add_self_eq_zero _

theorem Gen.det_hC : (Gen.hC n).det = 0 := by
  simp only [Gen.hC, PHat.det_mul, Gen.det_κ₀, Gen.det_κ₁, Gen.det_b₁H, Gen.det_s hn, add_zero]

omit hn in
theorem Gen.det_tC : (Gen.tC n).det = 0 := by
  simp only [Gen.tC, PHat.det_mul, Gen.det_κ₀, Gen.det_κ₁, add_zero]

theorem b₁T_eq' : b₁T hn = πT n (toP (Gen.b₁H n)) := by
  rw [b₁T_eq hn, ρ₁T, ← map_pow]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_toP Gen.det_ρ₁, coe_toP Gen.det_b₁H, Gen.ρ₁_pow_qr hn]

theorem b₀T_eq' : b₀T hn = πT n (toP (Gen.b₀H n)) := by
  rw [b₀T_eq hn, ρ₀T, ← map_pow]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_toP Gen.det_ρ₀, coe_toP Gen.det_b₀H, Gen.ρ₀_pow_qr hn]

theorem hCT_eq : hCT hn = πT n (toP (Gen.hC n)) := by
  rw [hCT, b₁T_eq' hn, κ₀T, κ₁T, sT, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_toP (Gen.det_hC hn), Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_toP Gen.det_κ₀, coe_toP Gen.det_κ₁, coe_toP Gen.det_b₁H, coe_toP (Gen.det_s hn)]
  rfl

omit hn in
theorem tCT_eq : tCT n = πT n (toP (Gen.tC n)) := by
  rw [tCT, κ₀T, κ₁T, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_toP Gen.det_tC, Subgroup.coe_mul, coe_toP Gen.det_κ₀, coe_toP Gen.det_κ₁]
  rfl

theorem hCT_mul_hCT : hCT hn * hCT hn = (ρ₀T n)⁻¹ * (ρ₁T n)⁻¹ := by
  rw [hCT_eq hn, ← map_mul, ρ₀T, ρ₁T, ← map_inv, ← map_inv, ← map_mul]
  apply πT_eq_of_coe_eq_mul_cz
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
    coe_toP Gen.det_ρ₀, coe_toP Gen.det_ρ₁, coe_toP (Gen.det_hC hn), Gen.hC_mul_hC hn]

theorem commute_tT_hCT : Commute (tT n) (hCT hn) := by
  rw [Commute, SemiconjBy, hCT_eq hn, tT, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_toP Gen.det_t, coe_toP (Gen.det_hC hn),
    Gen.t_mul_hC hn]

theorem commute_tT_tCT : Commute (tT n) (tCT n) := by
  have h : tT n * tCT n * (tT n)⁻¹ = tCT n := by
    rw [tCT, ← conj_mul_conj_inv, tT_conj_κ₀T hn, tT_conj_κ₁T hn, (commute_κ₀T_κ₁T hn).eq]
  calc tT n * tCT n = tT n * tCT n * (tT n)⁻¹ * tT n := by group
    _ = tCT n * tT n := by rw [h]

theorem tCT_mul_tCT : tCT n * tCT n = 1 := by
  rw [tCT]
  calc κ₀T n * κ₁T n * (κ₀T n * κ₁T n) = κ₀T n * (κ₁T n * κ₀T n) * κ₁T n := by group
    _ = κ₀T n * (κ₀T n * κ₁T n) * κ₁T n := by rw [(commute_κ₀T_κ₁T hn).eq]
    _ = (κ₀T n * κ₀T n) * (κ₁T n * κ₁T n) := by group
    _ = 1 := by rw [κ₀T_mul_κ₀T hn, κ₁T_mul_κ₁T hn, one_mul]

theorem tCT_conj_hCT : tCT n * hCT hn * (tCT n)⁻¹ = (hCT hn)⁻¹ * (b₀T hn * b₁T hn) := by
  rw [mul_inv_eq_iff_eq_mul, hCT_eq hn, tCT_eq, b₀T_eq' hn, b₁T_eq' hn, ← map_mul, ← map_inv,
    ← map_mul, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_toP Gen.det_tC, coe_toP (Gen.det_hC hn), coe_toP Gen.det_b₀H, coe_toP Gen.det_b₁H,
    Gen.tC_mul_hC hn, mul_assoc ((Gen.hC n)⁻¹)]

end CFSG.CGT.Foote81L6.Bridge
