module

public import CFSG.GH74.QTGen4.Recog.Ku.PolarityB
public import CFSG.GH74.QTGen4.Recog.Ku.NStructB

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem exists_kuPolar_ne_zero [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {y : G} (hy : y ∈ kuA P H)
    (hy1 : y ≠ 1) : ∃ x ∈ kuA P H, kuPolar P H z x y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hAW : kuA P H ≤ kuW P H := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      exact (kuW P H).one_mem
    obtain ⟨d, hd, hde⟩ := h.conj_transitive_kuA he he1
    obtain ⟨c, hc, hcy⟩ := h.conj_transitive_kuA hy hy1
    have hk : d * c⁻¹ ∈ kuN P H := Subgroup.mul_mem _ hd (Subgroup.inv_mem _ hc)
    have hkinv : (d * c⁻¹)⁻¹ ∈ kuN P H := Subgroup.inv_mem _ hk
    have hke : (d * c⁻¹) * y * (d * c⁻¹)⁻¹ = e := by
      rw [← hde, ← hcy]
      group
    have hx : (d * c⁻¹)⁻¹ * z * (d * c⁻¹)⁻¹⁻¹ ∈ kuA P H := by
      rw [inv_inv]
      exact KuHyp.inv_conj_mem_kuA hk h.z_mem_kuA
    have h0 := (hcon _ hx)
    have h1 := (h.kuPolar_conj_eq_zero_iff hkinv y).mp h0
    rw [inv_inv] at h1
    rw [← hke]
    exact h1
  have hcard := Subgroup.card_le_of_le hAW
  rw [h.card_kuA, h.card_kuW] at hcard
  omega

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
