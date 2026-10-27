module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)

section Singleton

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin d}

theorem IsHypCoord.centralizer_singleton_of_mem_pairTorusOf (h : IsHypCoord Q a b)
    (hq : 4 ≤ Nat.card K) {x : matrixProjectiveDerived Q} (hx : x ∈ pairTorusOf Q a b)
    (hx1 : x ≠ 1) :
    centralizer ({x} : Set (matrixProjectiveDerived Q)) = pairTorusOf Q a b ⊔ pairPerpOf Q a b := by
  classical
  have hne := h.exists_ne_zero
  have hx' := hx
  rw [pairTorusOf] at hx'
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 hx'
  rw [Subgroup.mem_subgroupOf] at ht
  obtain ⟨c, hc⟩ := ht
  have ht_eq : t = ⟨torusLin a b c, h.torusLin_mem_orthDerived c⟩ := Subtype.ext hc.symm
  have hc1 : c ≠ 1 := by
    intro hc1
    have ht1 : t = 1 := by
      rw [ht_eq, hc1]
      exact Subtype.ext (map_one (torusLin a b))
    exact hx1 (by rw [← htx, ht1, map_one])
  apply le_antisymm
  · intro y hy
    obtain ⟨g, rfl⟩ := projHom_surjective Q y
    have hcomm : g * t = t * g := by
      have h1 : projHom Q (g * t) = projHom Q (t * g) := by
        rw [map_mul, map_mul, htx]
        exact mem_centralizer_singleton_iff.1 hy
      exact projHom_injective hne h1
    have hcomm' : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) * torusLin a b c =
        torusLin a b c * (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
      simpa [ht_eq] using congrArg Subtype.val hcomm
    obtain ⟨α, hα⟩ := h.exists_torusLin_inv_mul_mem_stabSub hc1
      (Subgroup.commutator_le_self _ g.2) hcomm'
    set tα : orthDerived Q := ⟨torusLin a b α, h.torusLin_mem_orthDerived α⟩ with htα
    set g' : orthDerived Q := tα⁻¹ * g with hg'
    have hg'stab : (g' : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ stabSub a b := by
      have hg'val : (g' : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
          (torusLin a b α)⁻¹ * (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) := rfl
      rw [hg'val]
      exact hα
    have hx_mem : projHom Q tα ∈ pairTorusOf Q a b := by
      rw [pairTorusOf]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨α, rfl⟩)
    have hy_mem : projHom Q g' ∈ pairPerpOf Q a b := by
      rw [pairPerpOf]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hg'stab)
    have hg_eq : (g : orthDerived Q) = tα * g' := by
      rw [hg']; group
    rw [hg_eq, map_mul]
    exact Subgroup.mul_mem (pairTorusOf Q a b ⊔ pairPerpOf Q a b)
      (Subgroup.mem_sup_left hx_mem) (Subgroup.mem_sup_right hy_mem)
  · rw [sup_le_iff]
    constructor
    · have : IsMulCommutative ↥(pairTorusOf Q a b) := h.isCyclic_pairTorusOf.isMulCommutative
      refine (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (Subgroup.centralizer_le ?_)
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hx
    · refine (h.pairPerpOf_le_centralizer hq).trans (Subgroup.centralizer_le ?_)
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hx

theorem IsHypCoord.centralizer_singleton_eq_centralizer_pairTorusOf (h : IsHypCoord Q a b)
    (hq : 4 ≤ Nat.card K) {x : matrixProjectiveDerived Q} (hx : x ∈ pairTorusOf Q a b)
    (hx1 : x ≠ 1) :
    centralizer ({x} : Set (matrixProjectiveDerived Q)) =
      centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q)) := by
  rw [h.centralizer_singleton_of_mem_pairTorusOf hq hx hx1, h.centralizer_pairTorusOf hq]

end Singleton

end CFSG.SeitzReduction.OmegaPilot

end
