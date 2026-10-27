module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWPartI

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem inducedStab_subgroupOf_of_le {G : Type} [Group G] {M D E : Subgroup G}
    [hN : (D.subgroupOf M ⊔ E.subgroupOf M).Normal] (hWM : D ⊔ E ≤ M)
    (hΓ0 : ∀ α : MulAut ↥(D ⊔ E),
      (∀ x : ↥(D ⊔ E), (x : G) ∈ D → ((α x : ↥(D ⊔ E)) : G) ∈ D) →
      (∀ x : ↥(D ⊔ E), (x : G) ∈ E → ((α x : ↥(D ⊔ E)) : G) ∈ E) →
      ∃ m ∈ M, ∀ w : ↥(D ⊔ E), ((α w : ↥(D ⊔ E)) : G) = m * w * m⁻¹) :
    W16.InducedStab (D.subgroupOf M) (E.subgroupOf M) := by
  intro α' hD' hE'
  have hDM : D ≤ M := le_sup_left.trans hWM
  have hEM : E ≤ M := le_sup_right.trans hWM
  have hsup : D.subgroupOf M ⊔ E.subgroupOf M = (D ⊔ E).subgroupOf M :=
    (Subgroup.subgroupOf_sup hDM hEM).symm
  let φ : ↥(D.subgroupOf M ⊔ E.subgroupOf M) ≃* ↥(D ⊔ E) :=
    (MulEquiv.subgroupCongr hsup).trans (Subgroup.subgroupOfEquivOfLe hWM)
  have hφ : ∀ y : ↥(D.subgroupOf M ⊔ E.subgroupOf M),
      ((φ y : ↥(D ⊔ E)) : G) = ((y : ↥M) : G) := fun _ => rfl
  let α : MulAut ↥(D ⊔ E) := (φ.symm.trans α').trans φ
  have hαφ : ∀ y : ↥(D.subgroupOf M ⊔ E.subgroupOf M), α (φ y) = φ (α' y) := fun y => by
    show φ (α' (φ.symm (φ y))) = φ (α' y)
    rw [MulEquiv.symm_apply_apply]
  have hyx : ∀ x : ↥(D ⊔ E),
      (((φ.symm x : ↥(D.subgroupOf M ⊔ E.subgroupOf M)) : ↥M) : G) = (x : G) := by
    intro x
    have h1 := hφ (φ.symm x)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hαD : ∀ x : ↥(D ⊔ E), (x : G) ∈ D → ((α x : ↥(D ⊔ E)) : G) ∈ D := by
    intro x hx
    have hy : ((φ.symm x : ↥(D.subgroupOf M ⊔ E.subgroupOf M)) : ↥M) ∈ D.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf, hyx]
      exact hx
    have h3 : ((α x : ↥(D ⊔ E)) : G) = (((α' (φ.symm x)) : ↥M) : G) := hφ (α' (φ.symm x))
    rw [h3]
    exact Subgroup.mem_subgroupOf.1 (hD' (φ.symm x) hy)
  have hαE : ∀ x : ↥(D ⊔ E), (x : G) ∈ E → ((α x : ↥(D ⊔ E)) : G) ∈ E := by
    intro x hx
    have hy : ((φ.symm x : ↥(D.subgroupOf M ⊔ E.subgroupOf M)) : ↥M) ∈ E.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf, hyx]
      exact hx
    have h3 : ((α x : ↥(D ⊔ E)) : G) = (((α' (φ.symm x)) : ↥M) : G) := hφ (α' (φ.symm x))
    rw [h3]
    exact Subgroup.mem_subgroupOf.1 (hE' (φ.symm x) hy)
  obtain ⟨m, hm, hmw⟩ := hΓ0 α hαD hαE
  refine ⟨⟨m, hm⟩, MulEquiv.ext fun y => Subtype.ext (Subtype.ext ?_)⟩
  have e2 : (((α' y : ↥(D.subgroupOf M ⊔ E.subgroupOf M)) : ↥M) : G)
      = m * ((y : ↥M) : G) * m⁻¹ := by
    rw [← hφ (α' y), ← hαφ y, hmw (φ y), hφ y]
  exact e2.symm

theorem inducedStab_subgroupOf {G : Type} [Group G] [Finite G] {D E : Subgroup G}
    [hN : (D.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G)) ⊔
      E.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G))).Normal]
    (hΓ0 : ∀ α : MulAut ↥(D ⊔ E),
      (∀ x : ↥(D ⊔ E), (x : G) ∈ D → ((α x : ↥(D ⊔ E)) : G) ∈ D) →
      (∀ x : ↥(D ⊔ E), (x : G) ∈ E → ((α x : ↥(D ⊔ E)) : G) ∈ E) →
      ∃ m ∈ normalizer ((D ⊔ E : Subgroup G) : Set G),
        ∀ w : ↥(D ⊔ E), ((α w : ↥(D ⊔ E)) : G) = m * w * m⁻¹) :
    W16.InducedStab (D.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G)))
      (E.subgroupOf (normalizer ((D ⊔ E : Subgroup G) : Set G))) :=
  inducedStab_subgroupOf_of_le Subgroup.le_normalizer hΓ0

end CFSG.EvenSporadicStandard.Fin76b
