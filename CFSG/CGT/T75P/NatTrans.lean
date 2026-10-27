module

public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.CGT.Timmesfeld75.SLTransvection
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T : Subgroup G}

theorem units_eq_one_of_card_two {F : Type} [Field F] [Finite F] (h : Nat.card F = 2)
    (u : Fˣ) : u = 1 := by
  have h1 : Nat.card Fˣ = 1 := by rw [Nat.card_units, h]
  have := (Nat.card_eq_one_iff_unique.1 h1).1
  exact Subsingleton.elim _ _

theorem natural_trans {H : Subgroup G} {n : ℕ} (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hnat : NaturalSL T H n 1) :
    ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y := by
  classical
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  intro x hx hx1 y hy hy1
  have hcardF : Nat.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    simpa using this
  have hne : ∀ z (hz : z ∈ T), z ≠ 1 → Multiplicative.toAdd (φ ⟨z, hz⟩) ≠ 0 := by
    intro z hz hz1 h0
    have h1 : φ ⟨z, hz⟩ = 1 := by
      rw [← ofAdd_toAdd (φ ⟨z, hz⟩), h0]
      rfl
    have := φ.injective (h1.trans (map_one φ).symm)
    exact hz1 (congrArg Subtype.val this)
  obtain ⟨σ, hσ⟩ := exists_equiv_apply_eq_of_ne_zero (F := GaloisField 2 1)
    (W := Fin n → GaloisField 2 1) (hne x hx hx1) (hne y hy hy1)
  have hdet : (LinearMap.toMatrix' (σ : (Fin n → GaloisField 2 1) →ₗ[GaloisField 2 1]
      (Fin n → GaloisField 2 1))).det = 1 := by
    rw [LinearMap.det_toMatrix', ← LinearEquiv.coe_det,
      units_eq_one_of_card_two hcardF (LinearEquiv.det σ)]
    rfl
  let g : SL(n, GaloisField 2 1) :=
    ⟨LinearMap.toMatrix' (σ : (Fin n → GaloisField 2 1) →ₗ[GaloisField 2 1]
      (Fin n → GaloisField 2 1)), hdet⟩
  obtain ⟨q, hq⟩ := e.surjective g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨h, h.2, ?_⟩
  have hmem : (h : G) * x * (h : G)⁻¹ ∈ T := conj_mem_of_mem_normalizer (hHN h.2) hx
  have h1 := hcompat h ⟨x, hx⟩ hmem
  rw [hq] at h1
  have h2 : φ ⟨(h : G) * x * (h : G)⁻¹, hmem⟩ = φ ⟨y, hy⟩ := by
    rw [h1]
    show Multiplicative.ofAdd ((LinearMap.toMatrix'
      (σ : (Fin n → GaloisField 2 1) →ₗ[GaloisField 2 1] (Fin n → GaloisField 2 1))) *ᵥ
        Multiplicative.toAdd (φ ⟨x, hx⟩)) = _
    rw [LinearMap.toMatrix'_mulVec]
    show Multiplicative.ofAdd (σ (Multiplicative.toAdd (φ ⟨x, hx⟩))) = _
    rw [hσ, ofAdd_toAdd]
  exact congrArg Subtype.val (φ.injective h2)

end CFSG.CGT.T75P
