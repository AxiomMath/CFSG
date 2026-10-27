module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSPerm5

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open Subgroup

theorem zmod5_eq_one_of_pow_three {a : Multiplicative (ZMod 5)} (h : a ^ 3 = 1) : a = 1 := by
  revert a
  decide

theorem zmod5_exists_pow {c b : Multiplicative (ZMod 5)} (hc : c ≠ 1) :
    ∃ k : ℕ, c ^ k = b := by
  have : ∀ c b : Multiplicative (ZMod 5), c ≠ 1 → ∃ k : Fin 5, c ^ (k : ℕ) = b := by decide
  obtain ⟨k, hk⟩ := this c b hc
  exact ⟨k, hk⟩

variable {R : Type*} [Group R]

theorem card_centralizer_le_two_of_five_three {x5 x3 : R} {S : Set R}
    (hx5 : orderOf x5 = 5) (hx3 : orderOf x3 = 3) (hc : x5 * x3 = x3 * x5)
    (h5S : x5 ∈ S) (h3S : x3 ∈ S) (hn5 : x5 ∉ centralizer S) (hn3 : x3 ∉ centralizer S)
    (θ : ↥(centralizer ({x5} : Set R)) ≃* Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :
    Nat.card (centralizer S) ≤ 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C : Subgroup R := centralizer ({x5} : Set R) with hCdef
  set D : Subgroup R := centralizer S with hDdef
  have hDC : D ≤ C := centralizer_le (by simpa using h5S)
  have hx5C : x5 ∈ C := mem_centralizer_singleton_iff.2 rfl
  have hx3C : x3 ∈ C := mem_centralizer_singleton_iff.2 hc.symm
  have hx5p : x5 ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one x5
  have hx3p : x3 ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x3
  have hx5ne : x5 ≠ 1 := by
    rintro rfl
    simp at hx5
  have hx3ne : x3 ≠ 1 := by
    rintro rfl
    simp at hx3
  set g5 : C := ⟨x5, hx5C⟩ with hg5
  set g3 : C := ⟨x3, hx3C⟩ with hg3
  have hg3p : g3 ^ 3 = 1 := Subtype.ext (by simpa using hx3p)
  have hg5p : g5 ^ 5 = 1 := Subtype.ext (by simpa using hx5p)
  have hg3ne : g3 ≠ 1 := fun h => hx3ne (congrArg Subtype.val h)
  have hg5ne : g5 ≠ 1 := fun h => hx5ne (congrArg Subtype.val h)
  have hg53 : g5 * g3 = g3 * g5 := Subtype.ext hc
  obtain ⟨a, σ, hua⟩ : ∃ a σ, θ g3 = (a, σ) := ⟨(θ g3).1, (θ g3).2, rfl⟩
  obtain ⟨b, τ, hvb⟩ : ∃ b τ, θ g5 = (b, τ) := ⟨(θ g5).1, (θ g5).2, rfl⟩
  have hu3 : (a, σ) ^ 3 = 1 := by rw [← hua, ← map_pow, hg3p, map_one]
  have hu1 : (a, σ) ≠ 1 := by
    rw [← hua]
    intro h
    exact hg3ne (θ.injective (h.trans (map_one θ).symm))
  have hv5 : (b, τ) ^ 5 = 1 := by rw [← hvb, ← map_pow, hg5p, map_one]
  have hv1 : (b, τ) ≠ 1 := by
    rw [← hvb]
    intro h
    exact hg5ne (θ.injective (h.trans (map_one θ).symm))
  have hu3' : a ^ 3 = 1 ∧ σ ^ 3 = 1 := by simpa [Prod.ext_iff] using hu3
  have hv5' : b ^ 5 = 1 ∧ τ ^ 5 = 1 := by simpa [Prod.ext_iff] using hv5
  have ha1 : a = 1 := zmod5_eq_one_of_pow_three hu3'.1
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hu1 (by rw [ha1]; rfl)
  have hvu : (b, τ) * (a, σ) = (a, σ) * (b, τ) := by
    rw [← hvb, ← hua, ← map_mul, ← map_mul, hg53]
  have hτσ : τ * σ = σ * τ := (Prod.ext_iff.1 hvu).2
  have hτ1 : τ = 1 := eq_one_of_pow_five_of_comm hu3'.2 hσ1 hv5'.2 hτσ
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hv1 (by rw [hτ1]; rfl)
  set D₁ : Subgroup (Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :=
    (D.subgroupOf C).map θ.toMonoidHom with hD₁
  have hmem : ∀ z, z ∈ D₁ ↔ ((θ.symm z : C) : R) ∈ D := fun z => by
    rw [hD₁, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  have hcard : Nat.card D = Nat.card D₁ := by
    rw [hD₁, ← Nat.card_congr (Subgroup.equivMapOfInjective (D.subgroupOf C) θ.toMonoidHom
      θ.injective).toEquiv, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
  have hcomm : ∀ z ∈ D₁, z * (a, σ) = (a, σ) * z := by
    intro z hz
    have hzD : ((θ.symm z : C) : R) ∈ D := (hmem z).1 hz
    have h1 : x3 * ((θ.symm z : C) : R) = ((θ.symm z : C) : R) * x3 :=
      mem_centralizer_iff.1 hzD x3 h3S
    have h2 : g3 * θ.symm z = θ.symm z * g3 := Subtype.ext h1
    have h3 := congrArg θ h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hua] at h3
    exact h3.symm
  have hd5 : ∀ z ∈ D₁, z ^ 5 = 1 → z = 1 := by
    intro z hz hz5
    obtain ⟨c, s⟩ := z
    have h5 : c ^ 5 = 1 ∧ s ^ 5 = 1 := by simpa [Prod.ext_iff] using hz5
    have hs : s * σ = σ * s := (Prod.ext_iff.1 (hcomm _ hz)).2
    have hs1 : s = 1 := eq_one_of_pow_five_of_comm hu3'.2 hσ1 h5.2 hs
    by_cases hc1 : c = 1
    · rw [hc1, hs1]; rfl
    · exfalso
      obtain ⟨k, hk⟩ := zmod5_exists_pow (b := b) hc1
      have hvD : (b, τ) ∈ D₁ := by
        have : (c, s) ^ k = (b, τ) := by
          rw [Prod.pow_mk, hk, hs1, hτ1, one_pow]
        rw [← this]
        exact pow_mem hz k
      have hx5D : x5 ∈ D := by
        have := (hmem _).1 hvD
        rw [← hvb, MulEquiv.symm_apply_apply] at this
        exact this
      exact hn5 hx5D
  have hd3 : ∀ z ∈ D₁, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    obtain ⟨c, s⟩ := z
    have h3 : c ^ 3 = 1 ∧ s ^ 3 = 1 := by simpa [Prod.ext_iff] using hz3
    have hc1 : c = 1 := zmod5_eq_one_of_pow_three h3.1
    have hs : s * σ = σ * s := (Prod.ext_iff.1 (hcomm _ hz)).2
    by_cases hs1 : s = 1
    · rw [hc1, hs1]; rfl
    · exfalso
      have hux : (a, σ) ∈ D₁ := by
        rcases eq_or_inv_of_pow_three_of_comm hu3'.2 hσ1 h3.2 hs1 hs with h | h
        · have : (c, s) = (a, σ) := by rw [hc1, ha1, h]
          rw [← this]
          exact hz
        · have : (c, s)⁻¹ = (a, σ) := by
            rw [Prod.inv_mk, hc1, ha1, h, inv_one, inv_inv]
          rw [← this]
          exact inv_mem hz
      have hx3D : x3 ∈ D := by
        have := (hmem _).1 hux
        rw [← hua, MulEquiv.symm_apply_apply] at this
        exact this
      exact hn3 hx3D
  set Qp : Subgroup (Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :=
    (⊤ : Subgroup (Multiplicative (ZMod 5))).prod (centralizer ({σ} : Set (Equiv.Perm (Fin 5))))
    with hQp
  have hD₁Q : D₁ ≤ Qp := by
    intro z hz
    obtain ⟨c, s⟩ := z
    refine Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, ?_⟩
    exact mem_centralizer_singleton_iff.2 (Prod.ext_iff.1 (hcomm _ hz)).2
  have hQcard : Nat.card Qp = 30 := by
    rw [hQp, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      card_centralizer_perm5_three hu3'.2 hσ1]
    simp
  have hdvd : Nat.card D₁ ∣ 30 := hQcard ▸ Subgroup.card_dvd_of_le hD₁Q
  have h3nd : ¬ 3 ∣ Nat.card D₁ := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D₁) 3 h3
    have hxo : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hx] at hxo
    have hx3 : (x : Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hxo
    have := hd3 x x.2 hx3
    have hx1 : x = 1 := Subtype.ext this
    rw [hx1, orderOf_one] at hx
    omega
  have h5nd : ¬ 5 ∣ Nat.card D₁ := by
    intro h5
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D₁) 5 h5
    have hxo : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hx] at hxo
    have hx5 : (x : Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) ^ 5 = 1 := by
      simpa using congrArg Subtype.val hxo
    have := hd5 x x.2 hx5
    have hx1 : x = 1 := Subtype.ext this
    rw [hx1, orderOf_one] at hx
    omega
  have hc3 : Nat.Coprime (Nat.card D₁) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3nd).symm
  have hc5 : Nat.Coprime (Nat.card D₁) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5nd).symm
  have hc15 : Nat.Coprime (Nat.card D₁) 15 := by
    have := Nat.Coprime.mul_right hc3 hc5
    simpa using this
  have h2 : Nat.card D₁ ∣ 2 :=
    hc15.dvd_of_dvd_mul_right (by simpa using hdvd : Nat.card D₁ ∣ 2 * 15)
  rw [hcard]
  exact Nat.le_of_dvd (by norm_num) h2

end CFSG.EvenSporadicStandard.HSStd.PumpHS
