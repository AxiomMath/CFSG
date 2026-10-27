module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private def y7nNormCommutator (D A : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ normalizer (D : Set G) ∧ ∀ a ∈ A, ⁅x, a⁆ ∈ D}
  one_mem' := ⟨Subgroup.one_mem _, by intro a _; simp [commutatorElement_def]⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨Subgroup.mul_mem _ hx.1 hy.1, fun a ha => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    refine D.mul_mem ?_ (hx.2 a ha)
    exact (Subgroup.mem_normalizer_iff.mp hx.1 ⁅y, a⁆).1 (hy.2 a ha)
  inv_mem' := by
    intro x hx
    refine ⟨(normalizer (D : Set G)).inv_mem hx.1, fun a ha => ?_⟩
    have hconj : x⁻¹ * ⁅x, a⁆⁻¹ * x ∈ D := by
      have hc :=
        (Subgroup.mem_normalizer_iff.mp ((normalizer (D : Set G)).inv_mem hx.1) ⁅x, a⁆⁻¹).1
          (D.inv_mem (hx.2 a ha))
      simpa using hc
    have hid : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅x, a⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rwa [hid]

theorem y7n_conj_eq_of_unique {Q J : Subgroup G} (hJ : IsElemAbelian 2 J) (hJQ : J ≤ Q)
    (hmax : ∀ E : Subgroup G, E ≤ Q → IsElemAbelian 2 E →
      Nat.card E ≤ Nat.card J ∧ (Nat.card E = Nat.card J → E = J))
    {n : G} (hn : conjSub n Q = Q) : conjSub n J = J := by
  have h1 : conjSub n J ≤ Q := hn ▸ Subgroup.map_mono hJQ
  have h2 : IsElemAbelian 2 (conjSub n J) := hJ.map (MulAut.conj n).toMonoidHom
  have hcard : Nat.card (conjSub n J) = Nat.card J :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  exact (hmax (conjSub n J) h1 h2).2 hcard

theorem y7n_conjSub_commutator (n : G) (H K : Subgroup G) :
    conjSub n ⁅H, K⁆ = ⁅conjSub n H, conjSub n K⁆ :=
  Subgroup.map_commutator H K (MulAut.conj n).toMonoidHom

theorem y7n_commutator_sup_le {D X₁ X₂ A : Subgroup G}
    (hN : X₁ ⊔ X₂ ≤ normalizer (D : Set G)) (h₁ : ⁅X₁, A⁆ ≤ D) (h₂ : ⁅X₂, A⁆ ≤ D) :
    ⁅X₁ ⊔ X₂, A⁆ ≤ D := by
  have hX₁ : X₁ ≤ y7nNormCommutator D A := fun z hz =>
    ⟨hN (Subgroup.mem_sup_left hz), fun a ha => (Subgroup.commutator_le.mp h₁) z hz a ha⟩
  have hX₂ : X₂ ≤ y7nNormCommutator D A := fun z hz =>
    ⟨hN (Subgroup.mem_sup_right hz), fun a ha => (Subgroup.commutator_le.mp h₂) z hz a ha⟩
  exact Subgroup.commutator_le.mpr fun x hx a ha => (sup_le hX₁ hX₂ hx).2 a ha

theorem y7n_commutator_zpowers_le {D A : Subgroup G} {b : G}
    (hb : b ∈ normalizer (D : Set G)) (h : ∀ a ∈ A, ⁅b, a⁆ ∈ D) : ⁅zpowers b, A⁆ ≤ D := by
  have hbT : b ∈ y7nNormCommutator D A := ⟨hb, h⟩
  exact Subgroup.commutator_le.mpr fun x hx a ha =>
    (Subgroup.zpowers_le.mpr hbT hx).2 a ha

end CFSG.OddStandard.HigherRank.YamadaG23
