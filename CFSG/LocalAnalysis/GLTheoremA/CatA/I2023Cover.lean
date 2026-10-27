module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.LocalAnalysis.GLTheoremA

theorem cover_centralizes {G : Type} [Group G] [Finite G] {p : ℕ} {N T B : Subgroup G}
    (hNp : Nat.Coprime (Nat.card N) p) (hB : IsPGroup p B)
    (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hcov : ∀ b ∈ B, ∃ c ∈ Subgroup.centralizer (T : Set G), ∃ u ∈ N, b = c * u) :
    ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ = t := by
  intro b hb t ht
  obtain ⟨c, hc, u, hu, hbcu⟩ := hcov b hb
  have hcT : ∀ s ∈ T, s * c = c * s := fun s hs => Subgroup.mem_centralizer_iff.1 hc s hs
  have hBn : ∀ g ∈ B, ∀ s ∈ T, g * s * g⁻¹ ∈ T := by
    intro g hg s hs
    exact (Subgroup.mem_normalizer_iff.1 (hBT hg) s).1 hs
  have hu_eq : u = c⁻¹ * b := by
    rw [hbcu]
    group
  have hkey : ∀ s ∈ T, u * s * u⁻¹ = b * s * b⁻¹ := by
    intro s hs
    have hbs : b * s * b⁻¹ ∈ T := hBn b hb s hs
    have h1 : c⁻¹ * (b * s * b⁻¹) * c = b * s * b⁻¹ := by
      have := hcT _ hbs
      calc c⁻¹ * (b * s * b⁻¹) * c = c⁻¹ * ((b * s * b⁻¹) * c) := by group
        _ = c⁻¹ * (c * (b * s * b⁻¹)) := by rw [this]
        _ = b * s * b⁻¹ := by group
    rw [hu_eq]
    calc c⁻¹ * b * s * (c⁻¹ * b)⁻¹ = c⁻¹ * (b * s * b⁻¹) * c := by group
      _ = b * s * b⁻¹ := h1
  have hpow : ∀ j : ℕ, ∀ s ∈ T, u ^ j * s * (u ^ j)⁻¹ = b ^ j * s * (b ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro s _; simp
    | succ j ih =>
      intro s hs
      have hbj : b ^ j * s * (b ^ j)⁻¹ ∈ T := hBn _ (B.pow_mem hb j) s hs
      calc u ^ (j + 1) * s * (u ^ (j + 1))⁻¹
          = u * (u ^ j * s * (u ^ j)⁻¹) * u⁻¹ := by rw [pow_succ]; group
        _ = u * (b ^ j * s * (b ^ j)⁻¹) * u⁻¹ := by rw [ih s hs]
        _ = b * (b ^ j * s * (b ^ j)⁻¹) * b⁻¹ := hkey _ hbj
        _ = b ^ (j + 1) * s * (b ^ (j + 1))⁻¹ := by rw [pow_succ]; group
  obtain ⟨n, hn⟩ := hB ⟨b, hb⟩
  have hbk : b ^ (p ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hcentk : ∀ s ∈ T, s * u ^ (p ^ n) = u ^ (p ^ n) * s := by
    intro s hs
    have h := hpow (p ^ n) s hs
    rw [hbk, inv_one, one_mul, mul_one] at h
    calc s * u ^ (p ^ n) = (u ^ (p ^ n) * s * (u ^ (p ^ n))⁻¹) * u ^ (p ^ n) := by rw [h]
      _ = u ^ (p ^ n) * s := by group
  have hum : u ^ (Nat.card N) = 1 := by
    have h1 : orderOf (⟨u, hu⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    have h2 : (⟨u, hu⟩ : N) ^ (Nat.card N) = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_pow] at h3
    exact h3
  have hcop : Nat.Coprime (p ^ n) (Nat.card N) := Nat.Coprime.pow_left n hNp.symm
  obtain ⟨a, bb, hab⟩ : ∃ a bb : ℤ, ((p ^ n : ℕ) : ℤ) * a + ((Nat.card N : ℕ) : ℤ) * bb = 1 := by
    have h := Nat.gcd_eq_gcd_ab (p ^ n) (Nat.card N)
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact ⟨Nat.gcdA (p ^ n) (Nat.card N), Nat.gcdB (p ^ n) (Nat.card N), by
      exact_mod_cast h.symm⟩
  have hucent : ∀ s ∈ T, s * u = u * s := by
    intro s hs
    have hk : u ^ (p ^ n) ∈ Subgroup.centralizer (T : Set G) :=
      Subgroup.mem_centralizer_iff.2 hcentk
    have hza : (u ^ (p ^ n)) ^ a ∈ Subgroup.centralizer (T : Set G) := Subgroup.zpow_mem _ hk a
    have hu1 : u = (u ^ (p ^ n)) ^ a * (u ^ (Nat.card N)) ^ bb := by
      rw [← zpow_natCast u (p ^ n), ← zpow_natCast u (Nat.card N), ← zpow_mul, ← zpow_mul,
        ← zpow_add, hab, zpow_one]
    have hum' : (u ^ (Nat.card N)) ^ bb = 1 := by rw [hum, one_zpow]
    have hucent' : u ∈ Subgroup.centralizer (T : Set G) := by
      rw [hu1, hum', mul_one]
      exact hza
    exact Subgroup.mem_centralizer_iff.1 hucent' s hs
  have h1 : u * t * u⁻¹ = t := by
    calc u * t * u⁻¹ = (t * u) * u⁻¹ := by rw [hucent t ht]
      _ = t := by group
  calc b * t * b⁻¹ = u * t * u⁻¹ := (hkey t ht).symm
    _ = t := h1

end CFSG.LocalAnalysis.GLTheoremA

end
