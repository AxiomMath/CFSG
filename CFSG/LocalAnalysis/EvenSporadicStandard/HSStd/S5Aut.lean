module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

structure AutModelData {G : Type*} [Group G] (L : Subgroup G) (W X : Type*) [Group W]
    [Group X] where
  ι : X →* W
  ι_injective : Function.Injective ι
  θ : ↥L ≃* X
  e : W ≃* MulAut X
  he : ∀ (w : W) (x : X), ι (e w x) = w * ι x * w⁻¹

namespace AutModelData

variable {G : Type*} [Group G] {L : Subgroup G} {W X : Type*} [Group W] [Group X]
  (D : AutModelData L W X)

@[expose] noncomputable def rho : normalizer (L : Set G) →* W :=
  D.e.symm.toMonoidHom.comp ((MulAut.congr D.θ).toMonoidHom.comp L.normalizerMonoidHom)

theorem e_rho (n : normalizer (L : Set G)) :
    D.e (D.rho n) = MulAut.congr D.θ (L.normalizerMonoidHom n) := by
  simp [rho]

theorem rho_eq_one_iff (n : normalizer (L : Set G)) :
    D.rho n = 1 ↔ (n : G) ∈ centralizer (L : Set G) := by
  have h1 : D.rho n = 1 ↔ L.normalizerMonoidHom n = 1 := by
    constructor
    · intro h
      have := D.e_rho n
      rw [h, map_one] at this
      exact (map_eq_one_iff _ (MulEquiv.injective _)).1 this.symm
    · intro h
      apply D.e.injective
      rw [D.e_rho, h, map_one, map_one]
  rw [h1, ← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]

theorem rho_of_mem (l : L) :
    D.rho ⟨l, le_normalizer l.2⟩ = D.ι (D.θ l) := by
  apply D.e.injective
  rw [D.e_rho]
  ext x
  apply D.ι_injective
  rw [D.he]
  obtain ⟨y, rfl⟩ := D.θ.surjective x
  have h1 : L.normalizerMonoidHom ⟨l, le_normalizer l.2⟩ y = l * y * l⁻¹ := Subtype.ext rfl
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1, map_mul,
    map_inv]

end AutModelData

section Sup

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_iff {B : Subgroup G} {c : G} (h : ∀ β ∈ B, Commute β c) {a : G} :
    a ∈ B ⊔ zpowers c ↔ ∃ β ∈ B, ∃ j : ℤ, a = β * c ^ j := by
  constructor
  · intro ha
    let M : Subgroup G :=
      { carrier := {a | ∃ β ∈ B, ∃ j : ℤ, a = β * c ^ j}
        mul_mem' := by
          rintro _ _ ⟨β₁, h₁, j₁, rfl⟩ ⟨β₂, h₂, j₂, rfl⟩
          refine ⟨β₁ * β₂, B.mul_mem h₁ h₂, j₁ + j₂, ?_⟩
          have : Commute (c ^ j₁) β₂ := ((h β₂ h₂).symm).zpow_left j₁
          calc β₁ * c ^ j₁ * (β₂ * c ^ j₂) = β₁ * (c ^ j₁ * β₂) * c ^ j₂ := by group
            _ = β₁ * (β₂ * c ^ j₁) * c ^ j₂ := by rw [this.eq]
            _ = β₁ * β₂ * c ^ (j₁ + j₂) := by rw [zpow_add]; group
        one_mem' := ⟨1, B.one_mem, 0, by simp⟩
        inv_mem' := by
          rintro _ ⟨β, hβ, j, rfl⟩
          refine ⟨β⁻¹, B.inv_mem hβ, -j, ?_⟩
          have hc : Commute β⁻¹ (c ^ (-j)) := ((h β hβ).inv_left).zpow_right (-j)
          calc (β * c ^ j)⁻¹ = (c ^ j)⁻¹ * β⁻¹ := by group
            _ = c ^ (-j) * β⁻¹ := by rw [zpow_neg]
            _ = β⁻¹ * c ^ (-j) := hc.eq.symm }
    have hle : B ⊔ zpowers c ≤ M :=
      sup_le (fun β hβ => ⟨β, hβ, 0, by simp⟩) (zpowers_le.2 ⟨1, B.one_mem, 1, by simp⟩)
    exact hle ha
  · rintro ⟨β, hβ, j, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hβ)
      (Subgroup.mem_sup_right (zpow_mem (mem_zpowers c) j))

theorem zpow_eq_one_or_self {c : G} (hc : c * c = 1) (j : ℤ) : c ^ j = 1 ∨ c ^ j = c := by
  rcases Int.even_or_odd' j with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hc, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hc, one_zpow, one_mul, zpow_one]

end Sup

end CFSG.EvenSporadicStandard.HSStd
