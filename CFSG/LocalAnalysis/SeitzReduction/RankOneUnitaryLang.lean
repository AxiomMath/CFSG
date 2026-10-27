module

public import CFSG.GH74.Uniqueness.Bender.UnitaryOuterRoot
public import CFSG.GH74.Uniqueness.Bender.Aut

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section General

variable {K : Type*} [Group K]

theorem mulAut_mul_conj_eq_conj_mul (σ : MulAut K) (g : K) :
    σ * MulAut.conj g = MulAut.conj (σ g) * σ := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem isPGroup_zpowers_of_mul_self_eq_one {α : MulAut K} (hα : α * α = 1) :
    IsPGroup 2 (zpowers α) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : α ^ (2 : ℤ) = 1 := by rw [zpow_two, hα]
  show (α ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [h2]

theorem exists_sylow_forall_mem_of_mul_self_eq_one [Finite K] {α : MulAut K} (hα : α * α = 1) :
    ∃ Q : Sylow 2 K, ∀ x ∈ (Q : Subgroup K), α x ∈ (Q : Subgroup K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ¬ 2 ∣ Nat.card (Sylow 2 K) := by
    have := card_sylow_modEq_one 2 K
    unfold Nat.ModEq at this
    omega
  obtain ⟨Q, hQ⟩ :=
    (isPGroup_zpowers_of_mul_self_eq_one hα).nonempty_fixed_point_of_prime_not_dvd_card
      (Sylow 2 K) hnd
  refine ⟨Q, fun x hx => ?_⟩
  have h1 : (⟨α, mem_zpowers α⟩ : zpowers α) • Q = Q := hQ _
  have h2 : α • Q = Q := h1
  have h3 : α x ∈ ((α • Q : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul x α _ hx
  rwa [h2] at h3

theorem mem_smul_sylow_iff {p : ℕ} (Q : Sylow p K) (k x : K) :
    x ∈ ((k • Q : Sylow p K) : Subgroup K) ↔ k⁻¹ * x * k ∈ (Q : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem eq_one_of_conj_eq_one (hZ : center K = ⊥) {c : K} (hc : MulAut.conj c = 1) : c = 1 := by
  have hcZ : c ∈ center K := by
    refine mem_center_iff.mpr fun x => ?_
    have := congrArg (fun φ : MulAut K => φ x) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * c = c * x * c⁻¹ * c := by rw [this]
      _ = c * x := by group
  rw [hZ, mem_bot] at hcZ
  exact hcZ

end General

section Bender

variable {K : Type*} [Group K] [Finite K]

theorem image_autComm_eq_commutatorAut_unitary {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {α : MulAut K} (hα : α * α = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹)
    (hQ : ∀ x ∈ (Q : Subgroup K), α x ∈ (Q : Subgroup K)) :
    autComm α '' ((Q : Subgroup K) : Set K) = (commutatorAut (Q : Subgroup K) α : Set K) := by
  classical
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  obtain ⟨-, -, hWcard, -⟩ := h.lemma_3_4_d5_unitary Q α hα hout hQ
  have hsub : autComm α '' ((Q : Subgroup K) : Set K) ⊆
      (commutatorAut (Q : Subgroup K) α : Set K) :=
    Subgroup.subset_closure
  have hinj : ∀ x ∈ ((Q : Subgroup K) : Set K), ∀ x' ∈ ((Q : Subgroup K) : Set K),
      autComm α x = autComm α x' →
      x * x'⁻¹ ∈ rootCenter (Q : Subgroup K) := by
    intro x hx x' hx' hxx
    unfold autComm at hxx
    have hmem : x' * x⁻¹ ∈ (Q : Subgroup K) := mul_mem hx' (inv_mem hx)
    have hfix : α (x' * x⁻¹) = x' * x⁻¹ := by
      rw [map_mul, map_inv]
      calc α x' * (α x)⁻¹ = x' * (x'⁻¹ * α x') * (x⁻¹ * α x)⁻¹ * x⁻¹ := by group
        _ = x' * x⁻¹ := by rw [hxx]; group
    have h1 := (h.fixed_iff_rootCenter_unitary Q α hα hout hQ hmem).mp hfix
    have h2 := inv_mem h1
    rwa [mul_inv_rev, inv_inv] at h2
  have hle := ncard_le_mul_ncard_image (T := ((Q : Subgroup K) : Set K))
    (Z := rootCenter (Q : Subgroup K))
    (autComm α) hinj
  have hQn : ((Q : Subgroup K) : Set K).ncard = (2 ^ n) ^ 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hc.card_eq
  have hWn : ((commutatorAut (Q : Subgroup K) α : Subgroup K) : Set K).ncard = (2 ^ n) ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hWcard
  rw [hQn, hc.card_center] at hle
  have hq : 0 < 2 ^ n := by positivity
  have hge : (2 ^ n) ^ 2 ≤ (autComm α '' ((Q : Subgroup K) : Set K)).ncard := by
    have : 2 ^ n * (2 ^ n) ^ 2 ≤ 2 ^ n * (autComm α '' ((Q : Subgroup K) : Set K)).ncard := by
      calc 2 ^ n * (2 ^ n) ^ 2 = (2 ^ n) ^ 3 := by ring
        _ ≤ _ := hle
    exact Nat.le_of_mul_le_mul_left this hq
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hWn]; exact hge) (Set.toFinite _)

theorem conj_of_outer_involution_of_sylow {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {σ : MulAut K} (hσ : σ * σ = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, σ x = g * x * g⁻¹)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K)) {y : K}
    (hy2 : MulAut.conj y * σ * (MulAut.conj y * σ) = 1)
    (hyQ : ∀ x ∈ (Q : Subgroup K), (MulAut.conj y * σ) x ∈ (Q : Subgroup K)) :
    ∃ z : K, MulAut.conj y * σ = MulAut.conj z * σ * (MulAut.conj z)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := h.center_eq_bot
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun φ : MulAut K => φ x) hσ
    simpa using this
  have hσy : σ y = y⁻¹ := by
    have h0 : MulAut.conj y * σ * (MulAut.conj y * σ) = MulAut.conj (y * σ y) := by
      calc MulAut.conj y * σ * (MulAut.conj y * σ) = MulAut.conj y * (σ * MulAut.conj y) * σ := by
            group
        _ = MulAut.conj y * (MulAut.conj (σ y) * σ) * σ := by
            rw [mulAut_mul_conj_eq_conj_mul σ y]
        _ = MulAut.conj (y * σ y) * (σ * σ) := by rw [map_mul]; group
        _ = MulAut.conj (y * σ y) := by rw [hσ, mul_one]
    have h1 : MulAut.conj (y * σ y) = 1 := by rw [← h0, hy2]
    have h2 := eq_one_of_conj_eq_one hZ h1
    exact eq_inv_of_mul_eq_one_right h2
  have hyN : y ∈ normalizer ((Q : Subgroup K) : Set K) := by
    have hle : (Q : Subgroup K).map (MulAut.conj y).toMonoidHom ≤ (Q : Subgroup K) := by
      rintro _ ⟨x, hx, rfl⟩
      have := hyQ (σ x) (hσQ x hx)
      simpa [MulAut.mul_apply, hσσ] using this
    have heq : (Q : Subgroup K).map (MulAut.conj y).toMonoidHom = (Q : Subgroup K) :=
      eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj y).injective])
    exact mem_normalizer_iff_map_conj_eq.mpr heq
  set N := normalizer ((Q : Subgroup K) : Set K) with hN
  set m := (Q : Subgroup K).relIndex N with hm
  have hmodd : Odd m := by
    have h1 : m ∣ (Q : Subgroup K).index := relIndex_dvd_index_of_le le_normalizer
    have h2 := Q.not_dvd_index
    rw [Nat.odd_iff]
    by_contra h3
    exact h2 (dvd_trans (Nat.dvd_of_mod_eq_zero (by omega)) h1)
  have hym : y ^ m ∈ (Q : Subgroup K) := by
    have := Subgroup.pow_index_mem ((Q : Subgroup K).subgroupOf N) ⟨y, hyN⟩
    rw [mem_subgroupOf] at this
    simpa [hm, relIndex] using this
  obtain ⟨k, hk⟩ := hmodd
  set w := y ^ (k + 1) with hw
  set y₂ := (y ^ m)⁻¹ with hy₂
  have hyw : y₂ * (w * w) = y := by
    rw [hy₂, hw, ← pow_add, show k + 1 + (k + 1) = m + 1 by omega, pow_succ]
    group
  have hcomm : Commute y₂ w := by
    rw [hy₂, hw]
    exact (Commute.pow_pow_self y m (k + 1)).inv_left
  have hσw : σ w = w⁻¹ := by rw [hw, map_pow, hσy, inv_pow]
  have hσy₂ : σ y₂ = y₂⁻¹ := by rw [hy₂, map_inv, map_pow, hσy, inv_pow]
  have hwN : w ∈ N := pow_mem hyN _
  have hy₂Q : y₂ ∈ (Q : Subgroup K) := inv_mem hym
  set σ₁ := MulAut.conj w * σ * (MulAut.conj w)⁻¹ with hσ₁
  have hσ₁app : ∀ x, σ₁ x = w * σ (w⁻¹ * x * w) * w⁻¹ := fun x => by
    rw [hσ₁, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
  have hσ₁σ₁ : σ₁ * σ₁ = 1 := by
    calc σ₁ * σ₁ = MulAut.conj w * (σ * σ) * (MulAut.conj w)⁻¹ := by rw [hσ₁]; group
      _ = 1 := by rw [hσ]; group
  have hσ₁out : ¬ ∃ g : K, ∀ x : K, σ₁ x = g * x * g⁻¹ := by
    rintro ⟨g, hg⟩
    refine hout ⟨w⁻¹ * g * w, fun x => ?_⟩
    have h1 := hg (w * x * w⁻¹)
    rw [hσ₁app] at h1
    have h2 : σ x = w⁻¹ * (g * (w * x * w⁻¹) * g⁻¹) * w := by
      rw [← h1]
      group
    rw [h2]
    group
  have hσ₁Q : ∀ x ∈ (Q : Subgroup K), σ₁ x ∈ (Q : Subgroup K) := by
    intro x hx
    rw [hσ₁app]
    have h1 : w⁻¹ * x * w ∈ (Q : Subgroup K) := (mem_normalizer_iff''.mp hwN x).mp hx
    exact (mem_normalizer_iff.mp hwN _).mp (hσQ _ h1)
  have hσ₁y₂ : σ₁ y₂ = y₂⁻¹ := by
    rw [hσ₁app, show w⁻¹ * y₂ * w = y₂ by rw [mul_assoc, hcomm.eq]; group, hσy₂,
      (hcomm.inv_left.eq).symm]
    group
  have hsplit : MulAut.conj y * σ = MulAut.conj y₂ * σ₁ := by
    have h1 : σ₁ = MulAut.conj (w * w) * σ := by
      rw [hσ₁, ← map_inv, mul_assoc, mulAut_mul_conj_eq_conj_mul σ w⁻¹, map_inv, hσw, inv_inv,
        ← mul_assoc, ← map_mul]
    rw [h1, ← mul_assoc, ← map_mul, hyw]
  obtain ⟨-, -, -, -, -, -, -, -, hW⟩ := h.lemma_3_4_d5_unitary Q σ₁ hσ₁σ₁ hσ₁out hσ₁Q
  have hy₂W : y₂ ∈ commutatorAut (Q : Subgroup K) σ₁ := by
    refine (hW y₂ hy₂Q).mp ?_
    rw [hσ₁y₂, ← mul_inv_rev]
    exact inv_mem (h.sq_mem_rootCenter_unitary Q hy₂Q)
  have himg := image_autComm_eq_commutatorAut_unitary h Q hσ₁σ₁ hσ₁out hσ₁Q
  have hy₂img : y₂ ∈ autComm σ₁ '' ((Q : Subgroup K) : Set K) := by
    rw [himg]
    exact hy₂W
  obtain ⟨x, -, hx⟩ := hy₂img
  unfold autComm at hx
  refine ⟨x⁻¹ * w, ?_⟩
  rw [hsplit, ← hx, map_mul, map_inv, mul_assoc (MulAut.conj x)⁻¹,
    ← mulAut_mul_conj_eq_conj_mul σ₁ x, hσ₁, map_mul, map_inv]
  group

theorem conj_of_outer_involution_unitary {n e : ℕ}
    (h : BenderType K n 3 e) {σ σ' : MulAut K} (hσ : σ * σ = 1) (hσ' : σ' * σ' = 1)
    (hout : ¬ ∃ g : K, ∀ x, σ x = g * x * g⁻¹) (hcoset : ∃ y : K, σ' = MulAut.conj y * σ) :
    ∃ z : K, σ' = MulAut.conj z * σ * (MulAut.conj z)⁻¹ := by
  classical
  obtain ⟨y, rfl⟩ := hcoset
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_forall_mem_of_mul_self_eq_one hσ
  obtain ⟨Q', hQ'⟩ := exists_sylow_forall_mem_of_mul_self_eq_one hσ'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K Q₀ Q'
  set y'' := k⁻¹ * y * σ k with hy''
  have heq : MulAut.conj y'' * σ = (MulAut.conj k)⁻¹ * (MulAut.conj y * σ) * MulAut.conj k := by
    symm
    calc (MulAut.conj k)⁻¹ * (MulAut.conj y * σ) * MulAut.conj k =
          (MulAut.conj k)⁻¹ * MulAut.conj y * (σ * MulAut.conj k) := by group
      _ = (MulAut.conj k)⁻¹ * MulAut.conj y * (MulAut.conj (σ k) * σ) := by
          rw [mulAut_mul_conj_eq_conj_mul σ k]
      _ = MulAut.conj y'' * σ := by rw [hy'', map_mul, map_mul, map_inv]; group
  have hy2 : MulAut.conj y'' * σ * (MulAut.conj y'' * σ) = 1 := by
    rw [heq]
    calc (MulAut.conj k)⁻¹ * (MulAut.conj y * σ) * MulAut.conj k *
          ((MulAut.conj k)⁻¹ * (MulAut.conj y * σ) * MulAut.conj k) =
          (MulAut.conj k)⁻¹ * ((MulAut.conj y * σ) * (MulAut.conj y * σ)) * MulAut.conj k := by
          group
      _ = 1 := by rw [hσ']; group
  have hyQ : ∀ x ∈ (Q₀ : Subgroup K), (MulAut.conj y'' * σ) x ∈ (Q₀ : Subgroup K) := by
    intro x hx
    rw [heq, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    have h1 : k * x * k⁻¹ ∈ ((k • Q₀ : Sylow 2 K) : Subgroup K) := by
      rw [mem_smul_sylow_iff]
      simpa [mul_assoc] using hx
    rw [hk] at h1
    have h2 := hQ' _ h1
    rw [← hk, mem_smul_sylow_iff] at h2
    exact h2
  obtain ⟨z, hz⟩ := conj_of_outer_involution_of_sylow h Q₀ hσ hout hQ₀ hy2 hyQ
  refine ⟨k * z, ?_⟩
  have h1 : MulAut.conj y * σ =
      MulAut.conj k * (MulAut.conj y'' * σ) * (MulAut.conj k)⁻¹ := by
    rw [heq]
    group
  rw [h1, hz, map_mul]
  group

end Bender

end CFSG.SeitzReduction.RankOne
