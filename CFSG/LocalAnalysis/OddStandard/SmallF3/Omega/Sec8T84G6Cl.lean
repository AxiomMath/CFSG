module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec8t84g6_psi_inj {W : Subgroup G} {y : G} (hyfix : ∀ u ∈ W, y * u = u * y → u = 1)
    {u v : G} (hu : u ∈ W) (hv : v ∈ W)
    (h : u⁻¹ * (y * u * y⁻¹) = v⁻¹ * (y * v * y⁻¹)) : u = v := by
  have h1 : u⁻¹ * y * u = v⁻¹ * y * v := by
    have h2 := congrArg (fun x => x * y) h
    simpa [mul_assoc] using h2
  have hw : v * u⁻¹ ∈ W := W.mul_mem hv (W.inv_mem hu)
  have hc : y * (v * u⁻¹) = (v * u⁻¹) * y := by
    calc y * (v * u⁻¹) = v * (v⁻¹ * y * v) * u⁻¹ := by group
      _ = v * (u⁻¹ * y * u) * u⁻¹ := by rw [h1]
      _ = (v * u⁻¹) * y := by group
  have h3 := hyfix _ hw hc
  have h4 : v = u := by
    have := congrArg (fun x => x * u) h3
    simpa using this
  exact h4.symm

theorem sec8t84g6_psi_surj [Finite G] {W : Subgroup G} {y : G}
    (hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W) (hyfix : ∀ u ∈ W, y * u = u * y → u = 1) {u : G}
    (hu : u ∈ W) : ∃ v ∈ W, v⁻¹ * (y * v * y⁻¹) = u := by
  classical
  let f : W → W := fun v => ⟨v⁻¹ * (y * v * y⁻¹), W.mul_mem (W.inv_mem v.2) (hyW v v.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (sec8t84g6_psi_inj hyfix a.2 b.2 (congrArg Subtype.val hab))
  obtain ⟨⟨v, hv⟩, hvu⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨u, hu⟩
  exact ⟨v, hv, congrArg Subtype.val hvu⟩

theorem sec8t84g6_mem_of_psi_mem [Finite G] {U V : Subgroup G} {y : G} (hVU : V ≤ U)
    (hyV : ∀ w ∈ V, y * w * y⁻¹ ∈ V) (hyfix : ∀ u ∈ U, y * u = u * y → u = 1) {u : G}
    (hu : u ∈ U) (h : u⁻¹ * (y * u * y⁻¹) ∈ V) : u ∈ V := by
  obtain ⟨v, hv, hvu⟩ := sec8t84g6_psi_surj hyV (fun w hw => hyfix w (hVU hw)) h
  have : v = u := sec8t84g6_psi_inj hyfix (hVU hv) hu hvu
  exact this ▸ hv

theorem sec8t84g6_U_le_KD [Finite G] {K U : Subgroup G} {γ y k₀ c : G}
    (hKC : K ≤ centralizer ({γ} : Set G))
    (hCN : centralizer ({γ} : Set G) ≤ normalizer (K : Set G))
    (hUC : U ≤ centralizer ({γ} : Set G)) (hyC : y ∈ centralizer ({γ} : Set G))
    (hyU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) (hyfix : ∀ u ∈ U, y * u = u * y → u = 1)
    (hk₀ : k₀ ∈ K) (hc : c ∈ centralizer (K : Set G)) (hy : y = k₀ * c) :
    ∀ u ∈ U, ∃ k ∈ K, ∃ d ∈ centralizer ({γ} : Set G) ⊓ centralizer (K : Set G), u = k * d := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := sec8t84g6_psi_surj hyU hyfix hu
  have hvC : v ∈ centralizer ({γ} : Set G) := hUC hv
  have hcC : c ∈ centralizer ({γ} : Set G) := by
    have : c = k₀⁻¹ * y := by rw [hy]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKC hk₀)) hyC
  have hvN : ∀ x : G, x ∈ K ↔ v⁻¹ * x * v⁻¹⁻¹ ∈ K := fun x =>
    Subgroup.mem_normalizer_iff.mp (hCN (Subgroup.inv_mem _ hvC)) x
  have hvN' : ∀ x : G, x ∈ K ↔ v * x * v⁻¹ ∈ K := fun x =>
    Subgroup.mem_normalizer_iff.mp (hCN hvC) x
  have hk₁ : v⁻¹ * k₀ * v ∈ K := by
    have := (hvN k₀).mp hk₀
    simpa using this
  have hc₁ : v⁻¹ * c * v ∈ centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : v * x * v⁻¹ ∈ K := (hvN' x).mp hx
    have hcx := Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (v⁻¹ * c * v) = v⁻¹ * ((v * x * v⁻¹) * c) * v := by group
      _ = v⁻¹ * (c * (v * x * v⁻¹)) * v := by rw [hcx]
      _ = v⁻¹ * c * v * x := by group
  have hc₁C : v⁻¹ * c * v ∈ centralizer ({γ} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hvC) hcC) hvC
  set d : G := (v⁻¹ * c * v) * c⁻¹ with hd
  have hdD : d ∈ centralizer ({γ} : Set G) ⊓ centralizer (K : Set G) :=
    ⟨Subgroup.mul_mem _ hc₁C (Subgroup.inv_mem _ hcC),
      Subgroup.mul_mem _ hc₁ (Subgroup.inv_mem _ hc)⟩
  have hdK : ∀ x ∈ K, x * d = d * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hdD.2 x hx
  refine ⟨(v⁻¹ * k₀ * v) * k₀⁻¹, Subgroup.mul_mem _ hk₁ (Subgroup.inv_mem _ hk₀), d, hdD, ?_⟩
  have e1 : u = (v⁻¹ * k₀ * v) * d * k₀⁻¹ := by
    rw [← hvu, hy, hd]; group
  rw [e1]
  calc (v⁻¹ * k₀ * v) * d * k₀⁻¹ = (v⁻¹ * k₀ * v) * (d * k₀⁻¹) := by group
    _ = (v⁻¹ * k₀ * v) * (k₀⁻¹ * d) := by
      rw [← hdK k₀⁻¹ (Subgroup.inv_mem _ hk₀)]
    _ = (v⁻¹ * k₀ * v) * k₀⁻¹ * d := by group

theorem sec8t84g6_pow_odd_of_sq {u : G} (hu : u * u = 1) {m : ℕ} (hm : Odd m) : u ^ m = u := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : u ^ 2 = 1 := by rw [pow_two]; exact hu
  rw [pow_succ, pow_mul, h2, one_pow, one_mul]

theorem sec8t84g6_dec_sq {K D : Subgroup G} (hKD : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k)
    (hZ : ∀ z ∈ K ⊓ D, Odd (orderOf z)) {u k d : G} (hk : k ∈ K) (hd : d ∈ D) (hu : u = k * d)
    (hu2 : u * u = 1) : ∃ k' ∈ K, ∃ d' ∈ D, d' * d' = 1 ∧ u = k' * d' := by
  have hkd : Commute k d := hKD k hk d hd
  have h1 : k * k * (d * d) = 1 := by
    calc k * k * (d * d) = k * (k * d) * d := by group
      _ = k * (d * k) * d := by rw [hkd.eq]
      _ = (k * d) * (k * d) := by group
      _ = 1 := by rw [← hu]; exact hu2
  have hdd : d * d = (k * k)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hdK : d * d ∈ K ⊓ D :=
    ⟨hdd ▸ K.inv_mem (K.mul_mem hk hk), D.mul_mem hd hd⟩
  have hm : Odd (orderOf (d * d)) := hZ _ hdK
  set m := orderOf (d * d) with hmdef
  refine ⟨k ^ m, K.pow_mem hk m, d ^ m, D.pow_mem hd m, ?_, ?_⟩
  · have h3 : d ^ m * d ^ m = (d * d) ^ m := by
      rw [← pow_add, ← two_mul, pow_mul, pow_two]
    rw [h3, hmdef, pow_orderOf_eq_one]
  · rw [← hkd.mul_pow, ← hu]
    exact (sec8t84g6_pow_odd_of_sq hu2 hm).symm

theorem sec8t84g6_pair {K D : Subgroup G} (hKD : ∀ k ∈ K, ∀ d ∈ D, k * d = d * k)
    (hZ : ∀ z ∈ K ⊓ D, Odd (orderOf z)) {k₁ k₂ d₁ d₂ : G} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D) (hd₁₁ : d₁ * d₁ = 1) (hd₂₂ : d₂ * d₂ = 1)
    (hu₁ : (k₁ * d₁) * (k₁ * d₁) = 1) (hu₂ : (k₂ * d₂) * (k₂ * d₂) = 1)
    (hcomm : (k₁ * d₁) * (k₂ * d₂) = (k₂ * d₂) * (k₁ * d₁)) : d₁ * d₂ = d₂ * d₁ := by
  have e11 : k₁ * d₁ = d₁ * k₁ := hKD k₁ hk₁ d₁ hd₁
  have e12 : k₁ * d₂ = d₂ * k₁ := hKD k₁ hk₁ d₂ hd₂
  have e21 : k₂ * d₁ = d₁ * k₂ := hKD k₂ hk₂ d₁ hd₁
  have e22 : k₂ * d₂ = d₂ * k₂ := hKD k₂ hk₂ d₂ hd₂
  have hkk₁ : k₁ * k₁ = 1 := by
    have : k₁ * k₁ * (d₁ * d₁) = 1 := by
      calc k₁ * k₁ * (d₁ * d₁) = k₁ * (k₁ * d₁) * d₁ := by group
        _ = k₁ * (d₁ * k₁) * d₁ := by rw [e11]
        _ = (k₁ * d₁) * (k₁ * d₁) := by group
        _ = 1 := hu₁
    rwa [hd₁₁, mul_one] at this
  have hkk₂ : k₂ * k₂ = 1 := by
    have : k₂ * k₂ * (d₂ * d₂) = 1 := by
      calc k₂ * k₂ * (d₂ * d₂) = k₂ * (k₂ * d₂) * d₂ := by group
        _ = k₂ * (d₂ * k₂) * d₂ := by rw [e22]
        _ = (k₂ * d₂) * (k₂ * d₂) := by group
        _ = 1 := hu₂
    rwa [hd₂₂, mul_one] at this
  have hik₁ : k₁⁻¹ = k₁ := inv_eq_of_mul_eq_one_right hkk₁
  have hik₂ : k₂⁻¹ = k₂ := inv_eq_of_mul_eq_one_right hkk₂
  have hid₁ : d₁⁻¹ = d₁ := inv_eq_of_mul_eq_one_right hd₁₁
  have hid₂ : d₂⁻¹ = d₂ := inv_eq_of_mul_eq_one_right hd₂₂
  have h1 : (k₁ * k₂) * (d₁ * d₂) = (k₂ * k₁) * (d₂ * d₁) := by
    calc (k₁ * k₂) * (d₁ * d₂) = k₁ * (k₂ * d₁) * d₂ := by group
      _ = k₁ * (d₁ * k₂) * d₂ := by rw [e21]
      _ = (k₁ * d₁) * (k₂ * d₂) := by group
      _ = (k₂ * d₂) * (k₁ * d₁) := hcomm
      _ = k₂ * (d₂ * k₁) * d₁ := by group
      _ = k₂ * (k₁ * d₂) * d₁ := by rw [e12]
      _ = (k₂ * k₁) * (d₂ * d₁) := by group
  obtain ⟨c, hc⟩ : ∃ c : G, c = (k₁ * k₂) * (k₁ * k₂) := ⟨_, rfl⟩
  have hcK : c ∈ K := by
    rw [hc]; exact K.mul_mem (K.mul_mem hk₁ hk₂) (K.mul_mem hk₁ hk₂)
  have hcq : c * (d₁ * d₂) = d₂ * d₁ := by
    have h2 : (k₂ * k₁)⁻¹ * ((k₁ * k₂) * (d₁ * d₂)) = d₂ * d₁ := by
      rw [h1]; group
    have h3 : (k₂ * k₁)⁻¹ = k₁ * k₂ := by
      rw [mul_inv_rev, hik₁, hik₂]
    rw [h3] at h2
    calc c * (d₁ * d₂) = (k₁ * k₂) * ((k₁ * k₂) * (d₁ * d₂)) := by rw [hc]; group
      _ = d₂ * d₁ := h2
  have hcD : c ∈ D := by
    have : c = (d₂ * d₁) * (d₁ * d₂)⁻¹ := eq_mul_inv_of_mul_eq hcq
    rw [this]
    exact D.mul_mem (D.mul_mem hd₂ hd₁) (D.inv_mem (D.mul_mem hd₁ hd₂))
  have hodd : Odd (orderOf c) := hZ c ⟨hcK, hcD⟩
  have hcinv : k₁ * c * k₁ = c⁻¹ := by
    have h4 : c⁻¹ = (k₂ * k₁) * (k₂ * k₁) := by
      rw [hc, mul_inv_rev, mul_inv_rev, hik₁, hik₂]
    rw [h4, hc]
    calc k₁ * ((k₁ * k₂) * (k₁ * k₂)) * k₁ = (k₁ * k₁) * k₂ * (k₁ * k₂) * k₁ := by group
      _ = k₂ * (k₁ * k₂) * k₁ := by rw [hkk₁, one_mul]
      _ = k₂ * k₁ * (k₂ * k₁) := by group
  have hcc : k₁ * c = c * k₁ := hKD k₁ hk₁ c hcD
  have hc2 : c * c = 1 := by
    have h5 : c = c⁻¹ := by
      calc c = c * (k₁ * k₁) := by rw [hkk₁, mul_one]
        _ = (c * k₁) * k₁ := by rw [mul_assoc]
        _ = (k₁ * c) * k₁ := by rw [hcc]
        _ = c⁻¹ := hcinv
    calc c * c = c * c⁻¹ := by rw [← h5]
      _ = 1 := mul_inv_cancel c
  have hc1 : c = 1 := by
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [hc1, one_mul] at hcq
  exact hcq

end CFSG.OddStandard.SmallF3.Omega
