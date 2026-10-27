module

public import CFSG.LocalAnalysis.OddStandard.ThmCL34Aux
public import CFSG.GH74.KGroups.L34Tables

public section

namespace CFSG.OddStandard.ThmC

open CFSG.GH74.KGroups.L34 Subgroup


theorem isConj_of_involutions_P {y z : ↥QP.originalSubgroup} (hy : y * y = 1) (hy1 : y ≠ 1)
    (hz : z * z = 1) (hz1 : z ≠ 1) : IsConj y z := by
  have hy2 : (y : Equiv.Perm (Fin 42)) ^ 2 = 1 := by
    rw [pow_two]; exact congrArg Subtype.val hy
  have hz2 : (z : Equiv.Perm (Fin 42)) ^ 2 = 1 := by
    rw [pow_two]; exact congrArg Subtype.val hz
  obtain ⟨g1, hg1P, hg1⟩ := one_class_P y y.2 hy2 (fun h => hy1 (Subtype.ext h))
  obtain ⟨g2, hg2P, hg2⟩ := one_class_P z z.2 hz2 (fun h => hz1 (Subtype.ext h))
  refine isConj_iff.2 ⟨⟨g2 * g1⁻¹, QP.originalSubgroup.mul_mem hg2P
    (QP.originalSubgroup.inv_mem hg1P)⟩, Subtype.ext ?_⟩
  show g2 * g1⁻¹ * (y : Equiv.Perm (Fin 42)) * (g2 * g1⁻¹)⁻¹ = z
  rw [← hg1, ← hg2]
  group

theorem l34OneClass : L34OneClass := by
  intro X _ _ K hKn hK hidx u v hu hv
  have hodd : ¬ 2 ∣ K.index := fun h => by
    have := h.trans hidx
    omega
  have hu' : u ∈ K := mem_of_orderOf_two_of_odd_index hodd hu
  have hv' : v ∈ K := mem_of_orderOf_two_of_odd_index hodd hv
  obtain ⟨e⟩ := equiv_of_lieModel hK
  have key : ∀ w : K, orderOf w = 2 →
      (e w * e w = 1 ∧ e w ≠ 1) := by
    intro w hw
    have hw' : orderOf (e w) = 2 := by rw [MulEquiv.orderOf_eq]; exact hw
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨h1, h2⟩ := orderOf_eq_prime_iff.1 hw'
    exact ⟨by rw [← pow_two]; exact h1, h2⟩
  have hu2 : orderOf (⟨u, hu'⟩ : K) = 2 := by rw [← hu]; exact (Subgroup.orderOf_mk _ _)
  have hv2 : orderOf (⟨v, hv'⟩ : K) = 2 := by rw [← hv]; exact (Subgroup.orderOf_mk _ _)
  obtain ⟨hu3, hu4⟩ := key _ hu2
  obtain ⟨hv3, hv4⟩ := key _ hv2
  have hc := isConj_of_involutions_P hu3 hu4 hv3 hv4
  have hc' : IsConj (⟨u, hu'⟩ : K) ⟨v, hv'⟩ := by
    have := e.symm.toMonoidHom.map_isConj hc
    simpa using this
  have := K.subtype.map_isConj hc'
  simpa using this

end CFSG.OddStandard.ThmC
