module

public import CFSG.ClassicalInvolution.Asc77.AscT7XFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7X

namespace Frame24

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G} (D : Frame24 p f Ω W)


omit [Finite G] in
theorem x₁_mem : D.x₁ ∈ W := (D.h₁ ▸ Subgroup.mem_zpowers D.x₁ : D.x₁ ∈ D.F.ρ.R ⊓ W).2

omit [Finite G] in
theorem x₂_mem : D.x₂ ∈ W := (D.h₂ ▸ Subgroup.mem_zpowers D.x₂ : D.x₂ ∈ D.F.ρ'.R ⊓ W).2

omit [Finite G] in
theorem x₃_mem : D.x₃ ∈ W := (D.h₃ ▸ Subgroup.mem_zpowers D.x₃ : D.x₃ ∈ D.F.ρ₃.R ⊓ W).2

theorem comm12 : Commute D.x₁ D.x₂ :=
  Thompson.commutes_of_mem_WSet D.c.hp D.c.hq D.c.hΩ D.c.hW D.x₁ D.x₁_mem D.x₂ D.x₂_mem

theorem comm13 : Commute D.x₁ D.x₃ :=
  Thompson.commutes_of_mem_WSet D.c.hp D.c.hq D.c.hΩ D.c.hW D.x₁ D.x₁_mem D.x₃ D.x₃_mem

theorem comm23 : Commute D.x₂ D.x₃ :=
  Thompson.commutes_of_mem_WSet D.c.hp D.c.hq D.c.hΩ D.c.hW D.x₂ D.x₂_mem D.x₃ D.x₃_mem

omit [Finite G] in
theorem pow₁ : D.x₁ ^ (4 * D.m) = 1 := by simpa [D.o₁] using pow_orderOf_eq_one D.x₁

omit [Finite G] in
theorem pow₂ : D.x₂ ^ (4 * D.m) = 1 := by simpa [D.o₂] using pow_orderOf_eq_one D.x₂

omit [Finite G] in
theorem pow₃ : D.x₃ ^ (4 * D.m) = 1 := by simpa [D.o₃] using pow_orderOf_eq_one D.x₃

omit [Finite G] in
theorem z_eq : D.x₁ ^ (2 * D.m) = D.x₂ ^ (2 * D.m) := D.z₁.trans D.z₂.symm


omit [Finite G] in
theorem zpow_four {x : G} (hx : x ^ (4 * D.m) = 1) (a : ℤ) : x ^ (a + 4 * (D.m : ℤ)) = x ^ a := by
  have h4 : x ^ (4 * (D.m : ℤ)) = 1 := by exact_mod_cast hx
  rw [zpow_add, h4, mul_one]

omit [Finite G] in
theorem zpow_shift {x : G} (hx : x ^ (4 * D.m) = 1) {a b : ℤ} (h : a + 4 * (D.m : ℤ) = b) :
    x ^ a = x ^ b := by
  rw [← h, zpow_four D hx]

theorem eps_pow_eq (D : Frame24 p f Ω W) :
    (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m =
      D.x₁ ^ (D.m : ℤ) * D.x₂ ^ (-(D.m : ℤ)) * D.x₃ ^ (2 * (D.m : ℤ)) := by
  rw [← zpow_natCast, A3Mod.pow_triple D.comm12 D.comm13 D.comm23]

theorem eps_pow_fixed_r :
    D.F.ρ.r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * D.F.ρ.r⁻¹ =
      (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
  rw [eps_pow_eq, A3Mod.conj_nf_r D.comm12 D.comm13 D.r₁ D.r₂ D.r₃]
  have h : 2 * (D.m : ℤ) - (D.m : ℤ) = (D.m : ℤ) := by ring
  rw [h]

theorem eps_pow_fixed_t :
    D.F.ρ'.r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * D.F.ρ'.r⁻¹ =
      (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
  rw [eps_pow_eq, A3Mod.conj_nf_t D.comm23 D.t₁ D.t₂ D.t₃]
  have h : D.x₂ ^ (2 * (D.m : ℤ) - -(D.m : ℤ)) = D.x₂ ^ (-(D.m : ℤ)) :=
    (D.zpow_shift D.pow₂ (a := -(D.m : ℤ)) (b := 2 * (D.m : ℤ) - -(D.m : ℤ)) (by ring)).symm
  rw [h]

theorem eps_pow_fixed_s :
    D.F.ρ₃.r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * D.F.ρ₃.r⁻¹ =
      (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
  rw [eps_pow_eq, A3Mod.conj_nf_s D.comm13 D.comm23 D.s₁ D.s₂ D.s₃]
  have h : D.x₃ ^ ((D.m : ℤ) + -(D.m : ℤ) - 2 * (D.m : ℤ)) = D.x₃ ^ (2 * (D.m : ℤ)) :=
    D.zpow_shift D.pow₃ (a := (D.m : ℤ) + -(D.m : ℤ) - 2 * (D.m : ℤ)) (b := 2 * (D.m : ℤ))
      (by ring)
  rw [h]

theorem eps_pow_eq_one (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m = 1 := by
  have hεW : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m ∈ W :=
    W.pow_mem (W.mul_mem (W.mul_mem D.x₁_mem (W.inv_mem D.x₂_mem)) (W.pow_mem D.x₃_mem 2)) _
  have hfix : ∀ R₀ : Subgroup G, R₀ ∈ DSet Ω W → ∀ r : G, r ∈ R₀ →
      r * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * r⁻¹ = (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m :=
    fun R₀ hR₀ r hr => T7C2.fixed_of_frame D.c D.hφ D.F D.hab D.hcomm D.hac hεW
      D.eps_pow_fixed_r D.eps_pow_fixed_t D.eps_pow_fixed_s hR₀ hr
  have hcent : ∀ n ∈ Subgroup.normalizer (W : Set G),
      n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ = (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m := by
    intro n hn
    have hn' : n⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hn
    have hfW : n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ ∈ W :=
      (Thompson.mem_normalizer_iff_of_mem hn _).mpr hεW
    have hfixc : ∀ σ : Thompson.Rep Ω W,
        σ.r * (n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹) * σ.r⁻¹ =
          n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ := by
      intro σ
      have hmemD : n⁻¹ * σ.r * n ∈ conjSub n⁻¹ σ.R := by
        rw [mem_conjSub_iff]
        have h1 : (n⁻¹)⁻¹ * (n⁻¹ * σ.r * n) * n⁻¹ = σ.r := by group
        rw [h1]
        exact σ.hr
      have := hfix _ (Thompson.conjSub_mem_D D.c.hΩ σ.hR hn') _ hmemD
      calc σ.r * (n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹) * σ.r⁻¹
          = n * ((n⁻¹ * σ.r * n) * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m *
              (n⁻¹ * σ.r * n)⁻¹) * n⁻¹ := by group
        _ = n * (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m * n⁻¹ := by rw [this]
    rcases A3Mod.fixed_eq_one_or D.comm12 D.comm13 D.comm23 D.o₁ D.o₂ D.o₃ D.z_eq D.r₁ D.r₂ D.r₃
        D.t₁ D.t₂ D.t₃ D.s₁ D.s₂ D.s₃ (D.hgen hfW) (hfixc D.F.ρ) (hfixc D.F.ρ') (hfixc D.F.ρ₃)
      with h | h
    · have h0 : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m = 1 := conj_eq_one_iff.mp h
      rw [h0]
      group
    · exact h
  have hmemC : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m ∈ centerIn (Subgroup.normalizer (W : Set G)) :=
    T7C2.mem_centerIn_of_forall (Subgroup.le_normalizer hεW) hcent
  have hmem : (D.x₁ * D.x₂⁻¹ * D.x₃ ^ 2) ^ D.m ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)) :=
    ⟨hεW, hmemC⟩
  rw [hZ] at hmem
  exact Subgroup.mem_bot.mp hmem


theorem m_even (h8 : 8 < Nat.card ↥D.F.ρ.R) : 2 ∣ D.m := by
  have hcard : Nat.card ↥D.F.ρ.R = 8 * D.m := by
    have h1 := Thompson.D_card D.c.hp D.c.hq D.c.hΩ D.c.hW D.F.ρ.hR
    have h2 : Nat.card ↥(D.F.ρ.R ⊓ W) = 4 * D.m := by
      rw [← D.h₁, Nat.card_zpowers, D.o₁]
    omega
  obtain ⟨n, hn⟩ := D.F.ρ.hRK.2.1.exists_card_eq
  have hdvd : D.m ∣ 2 ^ n := ⟨8, by omega⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hm1 : D.m ≠ 1 := by omega
  rcases k with _ | k
  · exact absurd (by simpa using hk) hm1
  · rw [hk, pow_succ]
    exact dvd_mul_left 2 _

def eEl (c : ℕ) : G :=
  D.x₁ ^ (c : ℤ) * D.x₂ ^ (3 * (c : ℤ)) * D.x₃ ^ (2 * (c : ℤ))

omit [Finite G] in
theorem eEl_mem (c : ℕ) : D.eEl c ∈ W :=
  W.mul_mem (W.mul_mem (W.zpow_mem D.x₁_mem _) (W.zpow_mem D.x₂_mem _))
    (W.zpow_mem D.x₃_mem _)

theorem eEl_r (c : ℕ) : D.F.ρ.r * D.eEl c * D.F.ρ.r⁻¹ = D.eEl c := by
  unfold eEl
  rw [A3Mod.conj_nf_r D.comm12 D.comm13 D.r₁ D.r₂ D.r₃]
  have h : 2 * (c : ℤ) - (c : ℤ) = (c : ℤ) := by ring
  rw [h]

theorem eEl_s (c : ℕ) : D.F.ρ₃.r * D.eEl c * D.F.ρ₃.r⁻¹ = D.eEl c := by
  unfold eEl
  rw [A3Mod.conj_nf_s D.comm13 D.comm23 D.s₁ D.s₂ D.s₃]
  have h : (c : ℤ) + 3 * (c : ℤ) - 2 * (c : ℤ) = 2 * (c : ℤ) := by ring
  rw [h]

theorem eEl_t (c : ℕ) :
    D.F.ρ'.r * D.eEl c * D.F.ρ'.r⁻¹ = D.eEl c * D.x₂ ^ (-(4 * (c : ℤ))) := by
  unfold eEl
  rw [A3Mod.conj_nf_t D.comm23 D.t₁ D.t₂ D.t₃]
  have h1 : D.x₃ ^ (2 * (c : ℤ)) * D.x₂ ^ (-(4 * (c : ℤ))) =
      D.x₂ ^ (-(4 * (c : ℤ))) * D.x₃ ^ (2 * (c : ℤ)) :=
    (D.comm23.zpow_zpow (-(4 * (c : ℤ))) (2 * (c : ℤ))).eq.symm
  calc D.x₁ ^ (c : ℤ) * D.x₂ ^ (2 * (c : ℤ) - 3 * (c : ℤ)) * D.x₃ ^ (2 * (c : ℤ))
      = D.x₁ ^ (c : ℤ) * (D.x₂ ^ (3 * (c : ℤ)) * D.x₂ ^ (-(4 * (c : ℤ)))) *
          D.x₃ ^ (2 * (c : ℤ)) := by
        rw [← zpow_add]
        congr 3
        ring
    _ = D.x₁ ^ (c : ℤ) * D.x₂ ^ (3 * (c : ℤ)) * (D.x₂ ^ (-(4 * (c : ℤ))) *
          D.x₃ ^ (2 * (c : ℤ))) := by group
    _ = D.x₁ ^ (c : ℤ) * D.x₂ ^ (3 * (c : ℤ)) * (D.x₃ ^ (2 * (c : ℤ)) *
          D.x₂ ^ (-(4 * (c : ℤ)))) := by rw [h1]
    _ = D.x₁ ^ (c : ℤ) * D.x₂ ^ (3 * (c : ℤ)) * D.x₃ ^ (2 * (c : ℤ)) *
          D.x₂ ^ (-(4 * (c : ℤ))) := by group

theorem eEl_sq {c : ℕ} (hc : 2 * c = D.m)
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    D.eEl c * D.eEl c = 1 := by
  have h1 := D.eps_pow_eq_one hZ
  rw [D.eps_pow_eq] at h1
  unfold eEl
  rw [T7E.nf_mul D.comm12 D.comm13 D.comm23]
  have hm : (D.m : ℤ) = 2 * (c : ℤ) := by exact_mod_cast hc.symm
  have e1 : (c : ℤ) + (c : ℤ) = (D.m : ℤ) := by rw [hm]; ring
  have e3 : (2 * (c : ℤ)) + 2 * (c : ℤ) = 2 * (D.m : ℤ) := by rw [hm]; ring
  have e2 : D.x₂ ^ (3 * (c : ℤ) + 3 * (c : ℤ)) = D.x₂ ^ (-(D.m : ℤ)) := by
    refine (D.zpow_shift D.pow₂ (a := -(D.m : ℤ)) (b := 3 * (c : ℤ) + 3 * (c : ℤ)) ?_).symm
    rw [hm]
    ring
  rw [e1, e2, e3]
  exact h1

theorem eEl_ne_one {c : ℕ} (hc : 2 * c = D.m) : D.eEl c ≠ 1 := by
  intro h
  have h1 := D.eEl_t c
  rw [h, mul_one, one_mul, mul_inv_cancel] at h1
  have hz : D.x₂ ^ (-(4 * (c : ℤ))) = D.F.z := by
    have hm : (D.m : ℤ) = 2 * (c : ℤ) := by exact_mod_cast hc.symm
    have h2 : D.x₂ ^ (-(4 * (c : ℤ))) = D.x₂ ^ (2 * (D.m : ℤ)) := by
      refine D.zpow_shift D.pow₂ (a := -(4 * (c : ℤ))) (b := 2 * (D.m : ℤ)) ?_
      rw [hm]
      ring
    rw [h2]
    have h3 : D.x₂ ^ (2 * (D.m : ℤ)) = D.x₂ ^ (2 * D.m) := by
      rw [show 2 * (D.m : ℤ) = ((2 * D.m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    rw [h3, D.z₂]
  rw [hz] at h1
  exact D.F.hz.ne_one h1.symm

end Frame24

end T7X

end CFSG.ClassicalInvolution.Asc77
