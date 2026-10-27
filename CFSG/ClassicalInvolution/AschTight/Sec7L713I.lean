module

public import CFSG.ClassicalInvolution.AschTight.Sec7L713A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_not_mem_W (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {T L : Subgroup G} (hT : T ∈ DSet Ω W) (hL : L ∈ Ω)
    (hTL : T ≤ L) : ∃ t ∈ T, t ∉ W := by
  obtain ⟨-, -, hcard, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hT hL hTL
  by_contra h
  push Not at h
  have hTW : T ⊓ W = T := inf_eq_left.mpr h
  rw [hTW] at hcard
  have := (Nat.card_pos : 0 < Nat.card ↥T)
  omega

theorem quat_data (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (h611 : EtaMeets Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {T L : Subgroup G} (hT : T ∈ DSet Ω W) (hL : L ∈ Ω)
    (hTL : T ≤ L) {v t : G} (hv : Subgroup.zpowers v = T ⊓ W) (htT : t ∈ T) (htW : t ∉ W) :
    ∃ k : ℕ, 2 ≤ k ∧ orderOf v = 2 ^ k ∧ t * v * t⁻¹ = v⁻¹ ∧ t⁻¹ * v * t = v⁻¹ ∧
      t * t = v ^ (2 ^ (k - 1)) := by
  obtain ⟨-, -, hcard, -⟩ := inf_W_of_mem_DSet hp hΩ h611 hW hT hL hTL
  have hQ := hΩ.isQuatSub_of_mem_RSet hp hT.1
  have h8 := hΩ.eight_le_of_mem_RSet hp hT.1
  have hT2 := isPGroup_of_mem_RSet hT.1
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hp hq hL
  have hzT : zL ∈ T := hzL.mem_of_le hTL hT2 (by omega)
  have hz := AscL62.isUniqueInvolution_of_le hzL hTL hzT
  have hCT : T ⊓ W ≤ T := inf_le_left
  have hCc : IsCyclic ↥(T ⊓ W) := by rw [← hv]; infer_instance
  have htC : t ∉ T ⊓ W := fun h => htW (Subgroup.mem_inf.mp h).2
  have htiC : t⁻¹ ∉ T ⊓ W := fun h => htC (by simpa using (T ⊓ W).inv_mem h)
  have hvC : v ∈ T ⊓ W := hv ▸ Subgroup.mem_zpowers v
  have h1 := AscL62.conj_eq_inv_of_not_mem hQ hz hCT hCc hcard htT htC hvC
  have h2 := AscL62.conj_eq_inv_of_not_mem hQ hz hCT hCc hcard (T.inv_mem htT) htiC hvC
  rw [inv_inv] at h2
  have htt := AscL62.sq_eq_of_not_mem hQ hz hCT hCc hcard htT htC
  obtain ⟨k, hk⟩ := (hT2.to_le hCT).exists_card_eq
  have hov : orderOf v = 2 ^ k := by rw [← Nat.card_zpowers, hv, hk]
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨k, hk2, hov, h1, h2, ?_⟩
  rw [htt]
  have hw2 : v ^ (2 ^ (k - 1)) * v ^ (2 ^ (k - 1)) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k), ← hov,
      pow_orderOf_eq_one]
  have hw1 : v ^ (2 ^ (k - 1)) ≠ 1 := by
    intro h
    have h3 := orderOf_dvd_of_pow_eq_one h
    rw [hov] at h3
    have h4 := Nat.le_of_dvd (pow_pos two_pos _) h3
    have h5 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rcases hz.unique _ (T.pow_mem (hCT hvC) _) hw2 with h | h
  · exact absurd h hw1
  · exact h.symm

theorem exists_zpow_mul {W R : Subgroup G} (hW2 : IsPGroup 2 W) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (W : Set G)) {u : G} (hu : Subgroup.zpowers u = R ⊓ W)
    {h : G} (h1 : h ∈ R ⊔ OCW W) (h2 : h ∈ W ⊔ OCW W) :
    ∃ j : ℤ, ∃ x₁ ∈ OCW W, h = u ^ j * x₁ := by
  have hRX : R ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    hRN.trans (normalizer_le_normalizer_OCW W)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right R (OCW W) hRX
  have h1' : h ∈ ((R ⊔ OCW W : Subgroup G) : Set G) := h1
  rw [hcoe] at h1'
  obtain ⟨ρ, hρ, x₁, hx₁, rfl⟩ := h1'
  have hρWX : ρ ∈ W ⊔ OCW W := by
    have e : ρ = (ρ * x₁) * x₁⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ h2 (Subgroup.mem_sup_right (Subgroup.inv_mem _ hx₁))
  have hρW : ρ ∈ W :=
    mem_of_isPGroup_of_mem_sup_OCW hW2 hρWX (hR2.to_le (Subgroup.zpowers_le.mpr hρ))
  have hρu : ρ ∈ Subgroup.zpowers u := hu ▸ Subgroup.mem_inf.mpr ⟨hρ, hρW⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hρu
  exact ⟨j, x₁, hx₁, by rw [hj]⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
