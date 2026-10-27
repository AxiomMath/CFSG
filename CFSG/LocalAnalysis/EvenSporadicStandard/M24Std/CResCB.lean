module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResSylLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResAct
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideCommutator

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem card_le_card_fixSub_mul_commutator [Finite G] {C : Subgroup G}
    (hCab : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c) {g : G} (hg : g ∈ normalizer (C : Set G)) :
    Nat.card C ≤ Nat.card (fixSub C g) * Nat.card (⁅C, zpowers g⁆ : Subgroup G) := by
  let _ : CommGroup C :=
    { (inferInstance : Group C) with mul_comm := fun a b => Subtype.ext (hCab a a.2 b b.2) }
  let α : MulAut C := CSide.actN C ⟨g, hg⟩
  have hα : ∀ c : C, ((α c : C) : G) = g * c * g⁻¹ := fun c => rfl
  let δ : C →* C := MonoidHom.mk' (fun c => c * (α c)⁻¹) (by
    intro a b
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hδ : ∀ c : C, ((δ c : C) : G) = (c : G) * g * (c : G)⁻¹ * g⁻¹ := by
    intro c
    show ((c * (α c)⁻¹ : C) : G) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα]
    group
  have hker : Nat.card δ.ker ≤ Nat.card (fixSub C g) := by
    have hmem : ∀ c : δ.ker, g * ((c : C) : G) * g⁻¹ = ((c : C) : G) := fun c => by
      have h1 := MonoidHom.mem_ker.1 c.2
      have h2 := hδ c.1
      rw [h1] at h2
      have h3 : ((c : C) : G) * g * ((c : C) : G)⁻¹ * g⁻¹ = 1 := h2.symm
      calc g * ((c : C) : G) * g⁻¹
          = (((c : C) : G) * g * ((c : C) : G)⁻¹ * g⁻¹)⁻¹ * (((c : C) : G) * g⁻¹ * g ) := by
            group
        _ = ((c : C) : G) := by rw [h3]; group
    refine Nat.card_le_card_of_injective (fun c => (⟨(c : C), hmem c⟩ : fixSub C g)) ?_
    intro a b hab
    exact Subtype.ext (Subtype.mk.inj hab)
  have hrange : Nat.card δ.range ≤ Nat.card (⁅C, zpowers g⁆ : Subgroup G) := by
    have hmem : ∀ r : δ.range, ((r : C) : G) ∈ (⁅C, zpowers g⁆ : Subgroup G) := by
      rintro ⟨_, c, rfl⟩
      rw [show ((δ c : C) : G) = ⁅(c : G), g⁆ from by rw [hδ]; rfl]
      exact Subgroup.commutator_mem_commutator c.2 (mem_zpowers g)
    refine Nat.card_le_card_of_injective
      (fun r => (⟨((r : C) : G), hmem r⟩ : (⁅C, zpowers g⁆ : Subgroup G))) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
  calc Nat.card C = Nat.card δ.ker * Nat.card δ.range :=
        (Subgroup.card_ker_mul_card_range δ).symm
    _ ≤ Nat.card (fixSub C g) * Nat.card (⁅C, zpowers g⁆ : Subgroup G) :=
        Nat.mul_le_mul hker hrange

theorem fixSub_eq_of_qdMk_eq {C : Subgroup G} (hCab : ∀ c ∈ C, ∀ c' ∈ C, c * c' = c' * c)
    {d g : G} (hd : d ∈ normalizer (C : Set G)) (hg : g ∈ normalizer (C : Set G))
    (h : qdMk C ⟨d, hd⟩ = qdMk C ⟨g, hg⟩) : fixSub C d = fixSub C g := by
  have h1 : g⁻¹ * d ∈ C := by
    have : qdMk C ⟨g⁻¹ * d, mul_mem (inv_mem hg) hd⟩ = 1 := by
      have e : (⟨g⁻¹ * d, mul_mem (inv_mem hg) hd⟩ : normalizer (C : Set G)) =
          ⟨g, hg⟩⁻¹ * ⟨d, hd⟩ := rfl
      rw [e, map_mul, map_inv, ← h, inv_mul_cancel]
    exact (qdMk_eq_one _).1 this
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ ∈ C, d = g * c₀ := ⟨g⁻¹ * d, h1, by group⟩
  ext c
  show d * (c : G) * d⁻¹ = c ↔ g * (c : G) * g⁻¹ = c
  have hconj : d * (c : G) * d⁻¹ = g * (c : G) * g⁻¹ := by
    obtain ⟨hc₀C, rfl⟩ := hc₀
    have hc : (c₀ : G) * (c : G) = (c : G) * c₀ := hCab _ hc₀C _ c.2
    calc g * c₀ * (c : G) * (g * c₀)⁻¹ = g * (c₀ * (c : G)) * c₀⁻¹ * g⁻¹ := by group
      _ = g * ((c : G) * c₀) * c₀⁻¹ * g⁻¹ := by rw [hc]
      _ = g * (c : G) * g⁻¹ := by group
  rw [hconj]

end CFSG.EvenSporadicStandard.M24Std
