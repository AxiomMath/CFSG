module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

private abbrev l28mInn (G : Type) [Group G] : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

private instance l28mInn_normal (G : Type) [Group G] : (l28mInn G).Normal :=
  ⟨by
    rintro _ ⟨g, rfl⟩ ψ
    refine ⟨ψ g, ?_⟩
    ext y
    simp [MulAut.conj_apply]⟩

private theorem l28m_card_quotient {G : Type} [Group G] [Finite G]
    (hZ : ∀ x : G, (∀ y : G, x * y = y * x) → x = 1) (hA : Nat.card (MulAut G) = 3 * Nat.card G) :
    Nat.card (MulAut G ⧸ l28mInn G) = 3 := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hfin : Finite (MulAut G) := Nat.finite_of_card_ne_zero (by omega)
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.mpr (hZ g fun y => ?_)
    have h := congrArg (fun α : MulAut G => α y) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h]
  have hInn : Nat.card (l28mInn G) = Nat.card G := by
    change Nat.card (MulAut.conj : G →* MulAut G).range = Nat.card G
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  have h := (l28mInn G).index_mul_card
  rw [hInn, hA] at h
  rw [← Subgroup.index_eq_card]
  have h3 : 3 * Nat.card G = (l28mInn G).index * Nat.card G := by rw [← h]
  exact (Nat.eq_of_mul_eq_mul_right hpos h3).symm

private theorem l28m_eq_or_eq_inv_of_card_three {Q : Type*} [Group Q] (hQ : Nat.card Q = 3)
    {x y : Q} (hx : x ≠ 1) (hy : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have hord : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := hQ ▸ orderOf_dvd_natCard x
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx
    · exact h
  have hx3 : x ^ 3 = 1 := hord ▸ pow_orderOf_eq_one x
  have htop : Subgroup.zpowers x = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hQ])
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top y)
  have hmod := zpow_mod_orderOf x n
  rw [hord, hn] at hmod
  have hk : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hk with h | h | h
  · rw [show ((3 : ℕ) : ℤ) = 3 from rfl, h, zpow_zero] at hmod
    exact absurd hmod.symm hy
  · rw [show ((3 : ℕ) : ℤ) = 3 from rfl, h, zpow_one] at hmod
    exact Or.inl hmod.symm
  · rw [show ((3 : ℕ) : ℤ) = 3 from rfl, h] at hmod
    refine Or.inr ?_
    rw [← hmod]
    refine eq_inv_of_mul_eq_one_left ?_
    calc x ^ (2 : ℤ) * x = x ^ 3 := by group
      _ = 1 := hx3

theorem l28m_exists_conj_of_pow_eq_one {G : Type} [Group G] [Finite G]
    (hZ : ∀ x : G, (∀ y : G, x * y = y * x) → x = 1) (hA : Nat.card (MulAut G) = 3 * Nat.card G)
    {ψ : MulAut G} {m : ℕ} (hψ : ψ ^ m = 1) (hm : Nat.Coprime m 3) :
    ∃ k : G, MulAut.conj k = ψ := by
  have hQ := l28m_card_quotient hZ hA
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hfin : Finite (MulAut G) := Nat.finite_of_card_ne_zero (by omega)
  let π : MulAut G →* MulAut G ⧸ l28mInn G := QuotientGroup.mk' _
  have h1 : π ψ ^ m = 1 := by rw [← map_pow, hψ, map_one]
  have h2 : π ψ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := MulAut G ⧸ l28mInn G) (x := π ψ)
    rwa [hQ] at this
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hm, pow_one] at h3
  have hmem : ψ ∈ l28mInn G := (QuotientGroup.eq_one_iff ψ).mp h3
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, hk⟩

theorem l28m_exists_conj_mul_of_outer {G : Type} [Group G] [Finite G]
    (hZ : ∀ x : G, (∀ y : G, x * y = y * x) → x = 1) (hA : Nat.card (MulAut G) = 3 * Nat.card G)
    {φ α : MulAut G} (hφ : ∀ g : G, MulAut.conj g ≠ φ) (hα : ∀ g : G, MulAut.conj g ≠ α) :
    (∃ g : G, α = MulAut.conj g * φ) ∨ (∃ g : G, α⁻¹ = MulAut.conj g * φ) := by
  have hQ := l28m_card_quotient hZ hA
  let π : MulAut G →* MulAut G ⧸ l28mInn G := QuotientGroup.mk' _
  have hnot : ∀ β : MulAut G, (∀ g : G, MulAut.conj g ≠ β) → π β ≠ 1 := by
    intro β hβ h
    obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff β).mp h
    exact hβ k hk
  have hmk : ∀ β : MulAut G, π β = π φ → ∃ g : G, β = MulAut.conj g * φ := by
    intro β hβ
    have h1 : β⁻¹ * φ ∈ l28mInn G := QuotientGroup.eq.mp hβ
    have h2 : φ * β⁻¹ ∈ l28mInn G := (l28mInn_normal G).mem_comm h1
    obtain ⟨k, hk⟩ := h2
    refine ⟨k⁻¹, ?_⟩
    have : β⁻¹ = φ⁻¹ * MulAut.conj k := by rw [hk]; group
    calc β = (β⁻¹)⁻¹ := (inv_inv β).symm
      _ = (MulAut.conj k)⁻¹ * φ := by rw [this]; group
      _ = MulAut.conj k⁻¹ * φ := by rw [map_inv]
  rcases l28m_eq_or_eq_inv_of_card_three hQ (hnot φ hφ) (hnot α hα) with h | h
  · exact Or.inl (hmk α h)
  · refine Or.inr (hmk α⁻¹ ?_)
    rw [map_inv, h, inv_inv]

end CFSG.LocalAnalysis.RankThreeTheoremC
