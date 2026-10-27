module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenCent
public import CFSG.ClassicalInvolution.Asc77.AscL62Cent2
public import CFSG.ClassicalInvolution.AschTight.Sec6GenL33

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {z t : G}

theorem Pair.centralizes_of_normalizes_of_order
    (hΩ : HypOmegaGen Ω) (h : Pair Ω K J z t) {x : G} (hxJ : x ∈ J) {m : ℕ} (hm : 2 ≤ m)
    (hxo : orderOf x = 2 ^ m) {A : Subgroup G} (hAK : A ≤ K) (hA : IsCyclic ↥A)
    (hA2 : IsPGroup 2 ↥A) (hxA : conjSub x A = A) : ∀ a ∈ A, a * x = x * a := by
  by_cases hA1 : Nat.card A ≤ 1
  · intro a ha
    have hbot : A = ⊥ := Subgroup.eq_bot_of_card_le A hA1
    rw [hbot, Subgroup.mem_bot] at ha
    rw [ha, one_mul, mul_one]
  push Not at hA1
  obtain ⟨R, hR, hAR, hcfg, -, hVR, hcomm, hdich⟩ :=
    h.exists_core hΩ hxJ hm hxo hAK hA2 (by omega) hxA
  rcases hdich with hRU | ⟨C, hUC, hCR, hCc, hCcard, hCinv, hVc, hVC, htrans, hwr⟩
  · intro a ha
    have : a ∈ R ⊓ Subgroup.centralizer ({t} : Set G) := by
      rw [hRU]
      exact hAR ha
    exact hcomm a this x (Subgroup.mem_zpowers x)
  · by_cases hAC : A ≤ C
    · intro a ha
      exact hcomm a (hUC ▸ hAC ha) x (Subgroup.mem_zpowers x)
    · exfalso
      obtain ⟨g, hg⟩ := hA.exists_generator
      have hAeq := eq_zpowers_of_generator g hg
      have hgC : (g : G) ∉ C := by
        intro hgC
        apply hAC
        rw [hAeq]
        exact Subgroup.zpowers_le.mpr hgC
      have hgR : (g : G) ∈ R := hAR g.2
      have hgg : (g : G) * g = z := sq_eq_of_not_mem hcfg.quat hcfg.hz hCR hCc hCcard hgR hgC
      have hg4 : (g : G) ^ 4 = 1 := by
        have : (g : G) ^ 4 = ((g : G) * g) * ((g : G) * g) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [this, hgg]
        exact hcfg.hz.sq
      have hAcard : Nat.card A ≤ 4 := by
        have h1 : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
        have h2 : orderOf (g : G) ∣ 4 := orderOf_dvd_of_pow_eq_one hg4
        rw [← h1, ← Subgroup.orderOf_coe]
        exact Nat.le_of_dvd (by norm_num) h2
      have hxgA : x * g * x⁻¹ ∈ A := by
        have := conj_mem_conjSub (n := x) g.2
        rwa [hxA] at this
      have hγA : (g : G)⁻¹ * (x * g * x⁻¹) ∈ A := A.mul_mem (A.inv_mem g.2) hxgA
      have hγC : (g : G)⁻¹ * (x * g * x⁻¹) ∈ C :=
        htrans x (Subgroup.mem_zpowers x) g hgR hgC
      have hcommC : ∀ c ∈ C, ∀ v ∈ Subgroup.zpowers x, c * v = v * c := fun c hc v hv =>
        hcomm c (hUC ▸ hc) v hv
      obtain ⟨φ, hφ⟩ := hcfg.exists_phi hCR hCcard hCinv hcommC hgR hgC
      have hinj := hcfg.phi_injective hCR hCcard hcommC hUC hgR hgC φ hφ
      have hφx : ((φ ⟨x, Subgroup.mem_zpowers x⟩ : ↥C) : G) = (g : G)⁻¹ * (x * g * x⁻¹) :=
        hφ ⟨x, Subgroup.mem_zpowers x⟩
      have hord : orderOf (((g : G)⁻¹ * (x * g * x⁻¹))) = 2 ^ m := by
        rw [← hφx, Subgroup.orderOf_coe, orderOf_injective φ hinj, Subgroup.orderOf_mk, hxo]
      have hdvd : orderOf (((g : G)⁻¹ * (x * g * x⁻¹))) ∣ Nat.card A :=
        by
          have := Subgroup.orderOf_dvd_natCard A hγA
          exact this
      have h4m : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      have hAcard' : Nat.card A = 2 ^ m := by
        have := Nat.le_of_dvd (by omega) hdvd
        rw [hord] at this
        omega
      have hzp : Subgroup.zpowers ((g : G)⁻¹ * (x * g * x⁻¹)) = A := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hγA) ?_
        rw [Nat.card_zpowers, hord, hAcard']
      apply hAC
      rw [← hzp]
      exact Subgroup.zpowers_le.mpr hγC

theorem Pair.exists_swap (hΩ : HypOmegaGen Ω)
    (h : Pair Ω K J z t) {u x : G} (huK : u ∈ K) (hxJ : x ∈ J) (huu : u * u = z)
    (hxx : x * x = t) (hux : u * x = x * u) (hnc : ¬ ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K) :
    ∃ r : G, r * u * r⁻¹ = u⁻¹ ∧ (r * x * r⁻¹ = u * x ∨ r * x * r⁻¹ = u⁻¹ * x) := by
  have hu4 : u ^ 4 = 1 := by
    have : u ^ 4 = (u * u) * (u * u) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, huu]
    exact h.hz.sq
  have hx4 : x ^ 4 = 1 := by
    have : x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this, hxx]
    exact h.ht.sq
  have huord : orderOf u = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := u)
      (by simpa [pow_two, huu] using h.hz.ne_one) (by simpa using hu4)
    simpa using this
  have hxord : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x)
      (by simpa [pow_two, hxx] using h.ht.ne_one) (by simpa using hx4)
    simpa using this
  have hAK : Subgroup.zpowers u ≤ K := Subgroup.zpowers_le.mpr huK
  have hA2 : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, huord]; norm_num)
  have hA1 : 2 ≤ Nat.card (Subgroup.zpowers u) := by
    rw [Nat.card_zpowers, huord]
    norm_num
  have hxA : conjSub x (Subgroup.zpowers u) = Subgroup.zpowers u :=
    conjSub_zpowers_of_commute hux.symm
  obtain ⟨R, hR, hAR, hcfg, hVK, hVR, hcomm, hdich⟩ :=
    h.exists_core hΩ hxJ (m := 2) le_rfl (by simpa using hxord) hAK hA2 hA1 hxA
  rcases hdich with hRU | ⟨C, hUC, hCR, hCc, hCcard, hCinv, hVc, hVC, htrans, hwr⟩
  · exfalso
    apply hnc
    have hcommR : ∀ r ∈ R, ∀ v ∈ Subgroup.zpowers x, r * v = v * r := fun r hr v hv =>
      hcomm r (by rw [hRU]; exact hr) v hv
    intro k hk
    exact hxx ▸ centSylow hΩ h.hK hR hcfg.V2
      (fun y hy => mem_normalizer_iff_conjSub_eq.mp (hVK hy)) hcommR k hk (x * x)
      (Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x))
  · have huR : u ∈ R := hAR (Subgroup.mem_zpowers u)
    have hut : u * t = t * u := by
      rw [← hxx]
      calc u * (x * x) = (u * x) * x := by group
        _ = (x * u) * x := by rw [hux]
        _ = x * (u * x) := by group
        _ = x * (x * u) := by rw [hux]
        _ = (x * x) * u := by group
    have huC : u ∈ C := by
      rw [← hUC]
      exact ⟨huR, Subgroup.mem_centralizer_singleton_iff.mpr hut⟩
    obtain ⟨r, hrR, hrC⟩ : ∃ r ∈ R, r ∉ C := by
      by_contra hcon
      push Not at hcon
      have hle : R ≤ C := hcon
      have := Subgroup.card_le_of_le hle
      have h0 : 0 < Nat.card C := Nat.card_pos
      omega
    have hrinv : ∀ c ∈ C, r * c * r⁻¹ = c⁻¹ := fun c hc =>
      conj_eq_inv_of_not_mem hcfg.quat hcfg.hz hCR hCc hCcard hrR hrC hc
    have hcommC : ∀ c ∈ C, ∀ v ∈ Subgroup.zpowers x, c * v = v * c := fun c hc v hv =>
      hcomm c (hUC ▸ hc) v hv
    obtain ⟨φ, hφ⟩ := hcfg.exists_phi hCR hCcard hCinv hcommC hrR hrC
    have hinj := hcfg.phi_injective hCR hCcard hcommC hUC hrR hrC φ hφ
    set γ : G := r⁻¹ * (x * r * x⁻¹) with hγ
    have hγC : γ ∈ C := htrans x (Subgroup.mem_zpowers x) r hrR hrC
    have hφx : ((φ ⟨x, Subgroup.mem_zpowers x⟩ : ↥C) : G) = γ := hφ _
    have hγord : orderOf γ = 4 := by
      rw [← hφx, Subgroup.orderOf_coe, orderOf_injective φ hinj, Subgroup.orderOf_mk, hxord]
    have hzu : Subgroup.zpowers γ = Subgroup.zpowers u :=
      zpowers_eq_of_cyclic_of_orderOf_eq hCc hγC huC (by rw [hγord, huord])
    have hγmem : γ ∈ Subgroup.zpowers u := hzu ▸ Subgroup.mem_zpowers γ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hγmem
    have hk4 : u ^ (k % 4) = γ := by
      have := zpow_mod_orderOf u k
      rw [huord] at this
      simpa using this.trans hk
    have hγu : γ = u ∨ γ = u⁻¹ := by
      have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases hcases with h0 | h0 | h0 | h0
      · exfalso
        rw [h0] at hk4
        have : γ = 1 := by rw [← hk4]; simp
        rw [this, orderOf_one] at hγord
        omega
      · left
        rw [h0] at hk4
        simpa using hk4.symm
      · exfalso
        rw [h0] at hk4
        have h2 : γ * γ = 1 := by
          rw [← hk4]
          have : u ^ (2 : ℤ) = u * u := by rw [zpow_two]
          rw [this, huu]
          exact h.hz.sq
        have h3 : γ ^ 2 = 1 := by rw [pow_two]; exact h2
        have := orderOf_dvd_of_pow_eq_one h3
        rw [hγord] at this
        omega
      · right
        rw [h0] at hk4
        have h5 : u ^ (3 : ℤ) * u = 1 := by
          have : u ^ (3 : ℤ) * u = u ^ 4 := by
            calc u ^ (3 : ℤ) * u = u ^ (3 : ℤ) * u ^ (1 : ℤ) := by rw [zpow_one]
              _ = u ^ ((3 : ℤ) + 1) := by rw [zpow_add]
              _ = u ^ 4 := by norm_num
          rw [this]
          exact hu4
        rw [← hk4]
        exact eq_inv_of_mul_eq_one_left h5
    have hr1 : r * u * r⁻¹ = u⁻¹ := hrinv u huC
    have hconj : r * x * r⁻¹ = γ * x := by
      have h1 : r⁻¹ * x * r = γ * x := by rw [hγ]; group
      have h2 : r * (γ * x) * r⁻¹ = x := by rw [← h1]; group
      have h3 : r * γ * r⁻¹ = γ⁻¹ := hrinv γ hγC
      have h4 : r * (γ * x) * r⁻¹ = (r * γ * r⁻¹) * (r * x * r⁻¹) := by group
      rw [h4, h3] at h2
      calc r * x * r⁻¹ = γ * (γ⁻¹ * (r * x * r⁻¹)) := by group
        _ = γ * x := by rw [h2]
    refine ⟨r, hr1, ?_⟩
    rcases hγu with h1 | h1
    · left
      rw [hconj, h1]
    · right
      rw [hconj, h1]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
