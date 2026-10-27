module

public import CFSG.LargeExtraspecial.S14SMEFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SME

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem four_gen (hLoc : SmithU62LocalInput) (h34a : SmithE34a) (hLine : SmithE24Line)
    [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {x u w y : G}
    (hx : IsConj S.z x) (hu : IsConj S.z u) (hwc : IsConj S.z w) (hy : IsConj S.z y)
    (hxu : Commute x u) (huw : Commute u w) (hwy : Commute w y) (hxw : ¬ Commute x w)
    (h4 : orderOf (x * w) = 4) : ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hu
  have h1 := (SmithGraph.commute_conj_iff c x (c * S.z * c⁻¹)).mpr hxu
  have h2 := (SmithGraph.commute_conj_iff c (c * S.z * c⁻¹) w).mpr huw
  rw [conj_conj_inv] at h1 h2
  obtain ⟨v, hv, hxv, hvy⟩ := four_base hLoc h34a hLine S hw hU (SmithGraph.isConj_conj hx c)
    (SmithGraph.isConj_conj hwc c) (SmithGraph.isConj_conj hy c) h1 h2
    ((SmithGraph.commute_conj_iff c w y).mpr hwy)
    (fun h => hxw ((SmithGraph.commute_conj_iff c x w).mp h))
    (by rw [show c⁻¹ * x * c * (c⁻¹ * w * c) = c⁻¹ * (x * w) * c by group, orderOf_conj_inv]
        exact h4)
  have hvv : c⁻¹ * (c * v * c⁻¹) * c = v := by group
  refine ⟨c * v * c⁻¹, hv.trans (isConj_iff.mpr ⟨c, rfl⟩), ?_, ?_⟩
  · rw [← SmithGraph.commute_conj_iff c, hvv]
    exact hxv
  · rw [← SmithGraph.commute_conj_iff c, hvv]
    exact hvy

end SME

theorem smithU62PathInput_of (h34a : SmithE34a) (h34b : SmithE34b) (h23 : SmithE23)
    (h24 : SmithE24) (h25 : SmithE25) (hLine : SmithE24Line) (h421 : SmithE421Three) :
    SmithU62PathInput := by
  have hLoc := smithU62LocalInput_of h34a h34b h23 h24 h25
  intro G _ _ _ S hw hU x w y hx hwc hy hxz hzw hwy hxw hzy hxy
  have hloc := SmithGraph.local_of_input hLoc S hw hU
  have hxM : x ∈ S.M := Subgroup.mem_centralizer_singleton_iff.mpr hxz.eq
  have hwM : w ∈ S.M := Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm.eq
  have hz : IsConj S.z S.z := IsConj.refl _
  have hxw34 := SME.orderOf_eq_three_or_four S hx hwc hxw (hloc x w hx hwc hxM hwM).1
  obtain ⟨k, hk⟩ := isConj_iff.mp hwc
  have hzy34 : orderOf (S.z * y) = 3 ∨ orderOf (S.z * y) = 4 := by
    have hzM : k⁻¹ * S.z * k ∈ S.M := (SME.mem_M_conj_iff S k S.z).mpr (by rw [hk]; exact hzw)
    have hyM : k⁻¹ * y * k ∈ S.M :=
      (SME.mem_M_conj_iff S k y).mpr (by rw [hk]; exact hwy.symm)
    have h := (hloc _ _ (SmithGraph.isConj_conj hz k) (SmithGraph.isConj_conj hy k) hzM hyM).1
    rw [show k⁻¹ * S.z * k * (k⁻¹ * y * k) = k⁻¹ * (S.z * y) * k by group,
      SME.orderOf_conj_inv] at h
    exact SME.orderOf_eq_three_or_four S hz hy hzy h
  rcases hxw34 with h3 | h4
  · rcases hzy34 with h3' | h4'
    · exact h421 G S hw hU x w y hx hwc hy hxz hzw hwy hxw hzy hxy h3 h3'
    · have hyz : orderOf (y * S.z) = 4 := by
        rw [show y * S.z = S.z⁻¹ * (S.z * y) * S.z by group, SME.orderOf_conj_inv]
        exact h4'
      obtain ⟨v, hv, hyv, hvx⟩ := SME.four_gen hLoc h34a hLine S hw hU hy hwc hz hx hwy.symm
        hzw.symm hxz.symm (fun h => hzy h.symm) hyz
      exact ⟨v, hv, hvx.symm, hyv.symm⟩
  · exact SME.four_base hLoc h34a hLine S hw hU hx hwc hy hxz hzw hwy hxw h4

end CFSG.LargeExtraspecial.S14
