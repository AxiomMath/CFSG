module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFFactor
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveEEnd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Decomposition

variable {G : Type*} [Group G]

theorem mem_centralizer_of_le_sup_sup {t g : G} {W X D : Subgroup G}
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v)
    (hD : D ≤ (X ⊔ X.map (MulAut.conj t).toMonoidHom) ⊔ W) (hgW : g ∈ W)
    (hgX : g ∈ centralizer (X : Set G))
    (hgY : g ∈ centralizer (X.map (MulAut.conj t).toMonoidHom : Set G)) :
    g ∈ centralizer (D : Set G) := by
  have hle : (X ⊔ X.map (MulAut.conj t).toMonoidHom) ⊔ W ≤ centralizer ({g} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hgX x hx
    · intro y hy
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 hgY y hy
    · intro w hw
      rw [mem_centralizer_singleton_iff]
      exact hW w hw g hgW
  rw [mem_centralizer_iff]
  intro d hd
  exact mem_centralizer_singleton_iff.1 (hle (hD hd))

theorem forall_eq_mul_of_card_inf_centralizer [Finite G] {t : G} {W X D : Subgroup G}
    (hW : ∀ v ∈ W, ∀ w ∈ W, v * w = w * v) (htW : t ∈ normalizer (W : Set G))
    (hcard : Nat.card (W ⊓ centralizer (X : Set G) : Subgroup G) ^ 2 = Nat.card W)
    (hD : D ≤ (X ⊔ X.map (MulAut.conj t).toMonoidHom) ⊔ W)
    (hfix : W ⊓ centralizer (D : Set G) = ⊥) :
    ∀ w ∈ W, ∃ w₁ ∈ W ⊓ centralizer (X.map (MulAut.conj t).toMonoidHom : Set G),
      ∃ w₂ ∈ W ⊓ centralizer (X : Set G), w = w₁ * w₂ := by
  set U₁ := W ⊓ centralizer (X.map (MulAut.conj t).toMonoidHom : Set G) with hU₁
  set U₂ := W ⊓ centralizer (X : Set G) with hU₂
  have hmapU : U₂.map (MulAut.conj t).toMonoidHom ≤ U₁ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨huW, huC⟩ := mem_inf.1 hu
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 htW u).1 huW, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hxu : x * u = u * x := mem_centralizer_iff.1 huC x hx
    calc t * x * t⁻¹ * (t * u * t⁻¹) = t * (x * u) * t⁻¹ := by group
      _ = t * (u * x) * t⁻¹ := by rw [hxu]
      _ = t * u * t⁻¹ * (t * x * t⁻¹) := by group
  have hcU : Nat.card U₂ ≤ Nat.card U₁ := by
    calc Nat.card U₂ = Nat.card (U₂.map (MulAut.conj t).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj t).injective).symm
      _ ≤ Nat.card U₁ := Subgroup.card_le_of_le hmapU
  have hinf : U₁ ⊓ U₂ = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    intro g hg
    obtain ⟨hg₁, hg₂⟩ := mem_inf.1 hg
    exact mem_inf.2 ⟨(mem_inf.1 hg₂).1, mem_centralizer_of_le_sup_sup hW hD (mem_inf.1 hg₂).1
      (mem_inf.1 hg₂).2 (mem_inf.1 hg₁).2⟩
  have hcomm : U₂ ≤ centralizer (U₁ : Set G) := by
    intro u hu
    rw [mem_centralizer_iff]
    intro v hv
    exact hW v (mem_inf.1 hv).1 u (mem_inf.1 hu).1
  have hsup : U₁ ⊔ U₂ = W := by
    have hle : U₁ ⊔ U₂ ≤ W := sup_le inf_le_left inf_le_left
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [card_sup_eq_mul_of_le_centralizer_of_inf_eq_bot hcomm hinf, ← hcard, sq]
    exact Nat.mul_le_mul_right _ hcU
  have hN : U₂ ≤ normalizer (U₁ : Set G) := by
    apply le_normalizer_of_mul_mul_inv_mem
    intro u hu v hv
    rw [← mem_centralizer_iff.1 (hcomm hu) v hv, mul_inv_cancel_right]
    exact hv
  intro w hw
  have hw' : w ∈ ((U₁ : Set G) * (U₂ : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U₁ U₂ hN, hsup]
    exact hw
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Set.mem_mul.1 hw'
  exact ⟨w₁, hw₁, w₂, hw₂, rfl⟩

end Decomposition

end CFSG.SeitzReduction.LinearPilot
