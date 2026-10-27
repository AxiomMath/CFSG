module

public import CFSG.ClassicalInvolution.Asc77.AscT3YSw

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


theorem Std20.z_W_le_N_K (d : Std20 p f K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K : Set G) := by
  rw [d.late_hW]
  refine sup_le ?_ ?_
  · exact inf_le_right.trans Subgroup.le_normalizer
  · rw [inf_comm]
    exact d.late_JW_le_N_K d.late_JW

theorem Std20.z_W_le_N_K' (d : Std20 p f K K' J S R R' W V z t) :
    W ≤ Subgroup.normalizer (K' : Set G) := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := d.hSz (d.hWS hx)
  exact mem_normalizer_iff_conjSub_eq.mpr
    ((d.late_conj_iff hxC).mp (mem_normalizer_iff_conjSub_eq.mp (d.z_W_le_N_K hx)))

theorem Std20.z_scalar (d : Std20 p f K K' J S R R' W V z t) {u : G} {k : ℕ}
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1)) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hbK : conjSub b K = K) (hbt : b * t * b⁻¹ = t) {κ : ℤ}
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ κ) : ∀ w ∈ W, b * w * b⁻¹ = w ^ κ := by
  obtain ⟨l, hl⟩ := d.y_scalar hu huo hbS hbK hbt
  obtain ⟨v₀, -, hv₀o, -, -, hWgen, huv, -⟩ := d.v_W_gen hu huo
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have h1 : u ^ l = u ^ κ := by rw [← hl u huKW.2, hact u huKW]
  have h2 : ((2 : ℤ) ^ (k + 1)) ∣ l - κ := by
    have h3 : u ^ (l - κ) = 1 := by rw [zpow_sub, h1, mul_inv_cancel]
    have h4 := (orderOf_dvd_iff_zpow_eq_one (x := u) (i := l - κ)).mpr h3
    rwa [huo, Nat.cast_pow, Nat.cast_ofNat] at h4
  have h5 : v₀ ^ (l - κ) = 1 := by
    refine (orderOf_dvd_iff_zpow_eq_one (x := v₀) (i := l - κ)).mp ?_
    rwa [hv₀o, Nat.cast_pow, Nat.cast_ofNat]
  intro w hw
  rw [hl w hw]
  have hw' := hw
  rw [hWgen] at hw'
  obtain ⟨i, j, rfl⟩ := T3V.mem_sup_zpowers_of_commute huv hw'
  have hc : Commute (u ^ i) (v₀ ^ j) := (show Commute u v₀ from huv).zpow_zpow i j
  rw [hc.mul_zpow, hc.mul_zpow]
  have e1 : (u ^ i) ^ l = (u ^ i) ^ κ := by
    rw [← zpow_mul, ← zpow_mul, mul_comm i l, mul_comm i κ, zpow_mul, zpow_mul, h1]
  have e2 : (v₀ ^ j) ^ l = (v₀ ^ j) ^ κ := by
    have : v₀ ^ l = v₀ ^ κ := by
      rw [zpow_sub, mul_inv_eq_one] at h5
      exact h5
    rw [← zpow_mul, ← zpow_mul, mul_comm j l, mul_comm j κ, zpow_mul, zpow_mul, this]
  rw [e1, e2]

theorem Std20.z_frattini (d : Std20 p f K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z)
    {b : G} (hbS : b ∈ (S : Subgroup G)) (hb2 : b * b = 1) (hbK : conjSub b K = K)
    (hbt : b * t * b⁻¹ = t) {u : G} {k : ℕ} (hk : 2 ≤ k) (hu : Subgroup.zpowers u = K ⊓ W)
    (huo : orderOf u = 2 ^ (k + 1)) {κ : ℤ} (hκ : κ = 2 ^ k + 1 ∨ κ = 2 ^ k - 1)
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ κ) {w : G} (hwS : w ∈ (S : Subgroup G)) :
    ∃ x ∈ W, (x⁻¹ * w) * b = b * (x⁻¹ * w) := by
  have hα := d.z_scalar hu huo hbS hbK hbt hact
  obtain ⟨v₀, -, hv₀o, -, -, hWgen, huv, hdis⟩ := d.v_W_gen hu huo
  have hcW : ⁅b, w⁆ ∈ W := d.y_comm_of_scalar c7 hbS hα hwS
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  set w₁ : G := ⁅b, w⁆⁻¹ with hw₁
  have hw₁W : w₁ ∈ W := W.inv_mem hcW
  have hbw : w * b * w⁻¹ = w₁ * b := by
    simp only [hw₁, commutatorElement_def]
    group
  have hb'2 : (w₁ * b) * (w₁ * b) = 1 := by
    rw [← hbw]
    calc w * b * w⁻¹ * (w * b * w⁻¹) = w * (b * b) * w⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have hcoc : w₁ * (b * w₁ * b⁻¹) = 1 := by
    have : (w₁ * b) * (w₁ * b) = w₁ * (b * w₁ * b⁻¹) * (b * b) := by group
    rw [this, hb2, mul_one] at hb'2
    exact hb'2
  obtain ⟨x, hxW, hx⟩ := T3V.cocycle_cob hk hκ hWgen huv huo hv₀o hdis hα hw₁W hcoc
  have hxb : w₁ * b = x * b * x⁻¹ := by
    have h1 : w₁ = x * (b * x * b⁻¹)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact hx
    rw [h1]
    group
  refine ⟨x, hxW, ?_⟩
  have h1 : x⁻¹ * (w * b * w⁻¹) * x = b := by
    rw [hbw, hxb]
    group
  calc x⁻¹ * w * b = (x⁻¹ * (w * b * w⁻¹) * x) * (x⁻¹ * w) := by group
    _ = b * (x⁻¹ * w) := by rw [h1]

theorem Std20.z_swap_comm (d : Std20 p f K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z)
    {b : G} (hbS : b ∈ (S : Subgroup G)) (hb2 : b * b = 1) (hbK : conjSub b K = K)
    (hbt : b * t * b⁻¹ = t) {u : G} {k : ℕ} (hk : 2 ≤ k) (hu : Subgroup.zpowers u = K ⊓ W)
    (huo : orderOf u = 2 ^ (k + 1)) {κ : ℤ} (hκ : κ = 2 ^ k + 1 ∨ κ = 2 ^ k - 1)
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ κ) :
    ∃ s ∈ (S : Subgroup G), conjSub s K = K' ∧ s * b = b * s := by
  obtain ⟨w, hwS, hwK⟩ := d.late_exists_swap
  obtain ⟨x, hxW, hx⟩ := d.z_frattini c7 hbS hb2 hbK hbt hk hu huo hκ hact hwS
  refine ⟨x⁻¹ * w, S.mul_mem (S.inv_mem (d.hWS hxW)) hwS, ?_, hx⟩
  rw [conjSub_mul, hwK]
  have hxN : x⁻¹ ∈ Subgroup.normalizer (K' : Set G) := Subgroup.inv_mem _ (d.z_W_le_N_K' hxW)
  exact mem_normalizer_iff_conjSub_eq.mp hxN

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
