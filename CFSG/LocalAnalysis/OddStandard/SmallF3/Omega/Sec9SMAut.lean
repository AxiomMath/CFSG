module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec9m_mem_autIn {X B : Subgroup G} {φ : MulAut ↥B} :
    φ ∈ autIn X B ↔ ∃ x : G, x ∈ X ∧ x ∈ normalizer (B : Set G) ∧
      ∀ b : ↥B, ((φ b : ↥B) : G) = x * (b : G) * x⁻¹ := by
  constructor
  · intro hφ
    rw [autIn, Subgroup.mem_map] at hφ
    obtain ⟨k, hk, hkφ⟩ := hφ
    refine ⟨(k : G), ?_, k.2, ?_⟩
    · rwa [Subgroup.mem_subgroupOf] at hk
    · intro b
      rw [← hkφ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  · rintro ⟨x, hxX, hxN, hxφ⟩
    rw [autIn, Subgroup.mem_map]
    refine ⟨⟨x, hxN⟩, ?_, ?_⟩
    · rwa [Subgroup.mem_subgroupOf]
    · refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hxφ b).symm

theorem sec9m_autIn_mono {X Y B : Subgroup G} (h : X ≤ Y) : autIn X B ≤ autIn Y B := by
  rw [autIn, autIn]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem sec9m_card_autIn_dvd [Finite G] {X B : Subgroup G} (hX : X ≤ normalizer (B : Set G)) :
    Nat.card (autIn X B) ∣ Nat.card X := by
  rw [autIn]
  refine (Subgroup.card_map_dvd (H := X.subgroupOf (normalizer (B : Set G)))
    B.normalizerMonoidHom).trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

theorem sec9m_autIn_conj {X Y B : Subgroup G} (hXY : X ≤ Y) (hYB : Y ≤ normalizer (B : Set G))
    (hX : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X) :
    ∀ h ∈ autIn Y B, ∀ r ∈ autIn X B, h * r * h⁻¹ ∈ autIn X B := by
  intro h hh r hr
  rw [autIn, Subgroup.mem_map] at hh hr ⊢
  obtain ⟨k, hk, rfl⟩ := hh
  obtain ⟨k', hk', rfl⟩ := hr
  refine ⟨k * k' * k⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hk hk' ⊢
    show (k : G) * (k' : G) * (k : G)⁻¹ ∈ X
    exact hX (k : G) hk (k' : G) hk'
  · rw [map_mul, map_mul, map_inv]

theorem sec9m_autIn_comm {X B : Subgroup G}
    (hcomm : ∀ x ∈ X, ∀ x' ∈ X, ∀ b ∈ B, x * (x' * b * x'⁻¹) * x⁻¹ = x' * (x * b * x⁻¹) * x'⁻¹) :
    ∀ φ ∈ autIn X B, ∀ ψ ∈ autIn X B, φ * ψ = ψ * φ := by
  intro φ hφ ψ hψ
  obtain ⟨x, hxX, _hxN, hx⟩ := sec9m_mem_autIn.mp hφ
  obtain ⟨x', hx'X, _hx'N, hx'⟩ := sec9m_mem_autIn.mp hψ
  refine MulEquiv.ext fun b => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, hx (ψ b), hx' b, hx' (φ b), hx b]
  exact hcomm x hxX x' hx'X (b : G) b.2

end CFSG.OddStandard.SmallF3.Omega
