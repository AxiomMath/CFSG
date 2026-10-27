module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem false_of_pgl_inner {X : Type} [Group X] [Finite X] {L T : Subgroup X} {q : ℕ}
    (hZ : Nat.card ↥(center ↥L) = 2) (hL : Nat.card ↥L = q * (q ^ 2 - 1))
    (hpgl : InducedPGL2 L T q)
    (hT : ∀ t ∈ T, ∃ a ∈ L, a⁻¹ * t ∈ centralizer (L : Set X)) : False := by
  obtain ⟨hNorm, F, hF, hFin, hFq, ⟨e⟩⟩ := hpgl
  have hFq' : Nat.card F = q := hFq
  have hLC : ∀ a ∈ L, ∀ c ∈ centralizer (L : Set X), a * c = c * a := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.mp hc a ha
  have hle : L ⊔ T ≤ L ⊔ centralizer (L : Set X) := by
    refine sup_le le_sup_left fun t ht => ?_
    obtain ⟨a, ha, hc⟩ := hT t ht
    rw [← mul_inv_cancel_left a t]
    exact Subgroup.mul_mem_sup ha hc
  let N : Subgroup ↥(L ⊔ T) := (centralizer (L : Set X)).subgroupOf (L ⊔ T)
  let π : ↥L →* ↥(L ⊔ T) ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion le_sup_left)
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨⟨y₀, hy₀⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha, c, hc, hac⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hLC (hle hy₀)
    refine ⟨⟨a, ha⟩, ?_⟩
    show QuotientGroup.mk (⟨a, Subgroup.mem_sup_left ha⟩ : ↥(L ⊔ T)) =
      QuotientGroup.mk ⟨y₀, hy₀⟩
    rw [QuotientGroup.eq]
    show a⁻¹ * y₀ ∈ centralizer (L : Set X)
    rw [← hac, inv_mul_cancel_left]
    exact hc
  have hker : 2 ≤ Nat.card ↥π.ker := by
    have hZker : center ↥L ≤ π.ker := by
      intro w hw
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk (⟨(w : X), Subgroup.mem_sup_left w.2⟩ : ↥(L ⊔ T)) :
        ↥(L ⊔ T) ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      show (w : X) ∈ centralizer (L : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨a, ha⟩)
    have := Subgroup.card_le_of_le hZker
    omega
  have hcardQ : Nat.card (↥(L ⊔ T) ⧸ N) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F, hFq']
  have hrange : Nat.card ↥π.range = q * (q ^ 2 - 1) := by
    rw [MonoidHom.range_eq_top.mpr hπ, ← hcardQ]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hmul := Subgroup.card_ker_mul_card_range π
  rw [hrange, hL] at hmul
  have hpos : 0 < q * (q ^ 2 - 1) := by
    rw [← hL]
    exact Nat.card_pos
  generalize q * (q ^ 2 - 1) = m at hmul hpos
  nlinarith

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
