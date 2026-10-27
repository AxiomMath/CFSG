module

public import CFSG.GF2Type.SmithTypeE.E7.Local
public import CFSG.LargeExtraspecial.S14SMEFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SME (inv_eq_of_isConj ne_one_of_isConj mem_Qa_iff mem_Qa_symm
  commutator_mem
  mem_M_conj_iff commute_mul_of_not_commute isConj_mul_of_mem_Qa conj_pow_inv orderOf_conj_inv
  conj_conj_inv dihedral_facts commute_of_sq_eq_one orderOf_eq_three_or_four
  orderOf_eq_four_of_pow isConj_of_conj_inv)
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem local_of_input (hLoc : SmithE7LocalInput) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) (x y : G)
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  by_cases hxQ : x ∈ S.QG
  · by_cases hyQ : y ∈ S.QG
    · exact SmithQ.orderOf_mul_mem_of_mem_QG S hxQ hyQ
    · obtain ⟨h1, h2⟩ := hLoc G S hw hU y x hy hx hyM hxM hyQ
      have hord : orderOf (y * x) = orderOf (x * y) := by
        rw [show y * x = MulAut.conj y (x * y) by rw [MulAut.conj_apply]; group,
          MulEquiv.orderOf_eq]
      rw [hord] at h1 h2
      refine ⟨h1, fun h4 => ?_⟩
      rw [show (x * y) ^ 2 = x * (y * x) ^ 2 * x⁻¹ by rw [_root_.sq, _root_.sq]; group]
      exact (h2 h4).trans (isConj_iff.mpr ⟨x, rfl⟩)
  · exact hLoc G S hw hU x y hx hy hxM hyM hxQ


theorem mem_Qa_of_isConj_mul (h34a : SmithE7E34a) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {g x : G}
    (hx : IsConj S.z x) (hxa : Commute x (g * S.z * g⁻¹))
    (hxa' : IsConj S.z (x * (g * S.z * g⁻¹))) : g⁻¹ * x * g ∈ S.QG := by
  by_contra hQ
  apply h34a G S hw hU _ (SmithGraph.isConj_conj hx g) ((mem_M_conj_iff S g x).mpr hxa) hQ
  have h : g⁻¹ * x * g * S.z = g⁻¹ * (x * (g * S.z * g⁻¹)) * g := by group
  rw [h]
  exact SmithGraph.isConj_conj hxa' g

theorem pow_four_of_mem_Qa (h34a : SmithE7E34a) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 16) (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {k a y : G}
    (ha : IsConj S.z a) (hy : IsConj S.z y) (haQ : k⁻¹ * a * k ∈ S.QG)
    (hyw : Commute (k * S.z * k⁻¹) y) : (a * y) ^ 4 = 1 := by
  have hyM : k⁻¹ * y * k ∈ S.M := (mem_M_conj_iff S k y).mpr hyw.symm
  have hc : (k⁻¹ * a * k * (k⁻¹ * y * k)) ^ 4 = 1 := by
    by_cases hyQ : k⁻¹ * y * k ∈ S.QG
    · exact S.pow_four_eq_one (S.QG.mul_mem haQ hyQ)
    · have hai := inv_eq_of_isConj S (SmithGraph.isConj_conj ha k)
      have hyi := inv_eq_of_isConj S (SmithGraph.isConj_conj hy k)
      set a' := k⁻¹ * a * k
      set y' := k⁻¹ * y * k
      have hsq : ((y' * a') ^ 2) ^ 2 = 1 := by
        have he : (y' * a') ^ 2 = y' * a' * y'⁻¹ * a'⁻¹ := by
          rw [hai, hyi, sq]
          simp only [mul_assoc]
        rw [he]
        exact sq_eq_one_of_mem_commutator h34a S hw hU (SmithGraph.isConj_conj hy k) hyM hyQ
          (commutator_mem S y' haQ)
      have h4 : (y' * a') ^ 4 = 1 := by rw [← hsq, ← pow_mul]
      have hconj : a' * y' = a' * (y' * a') * a'⁻¹ := by group
      rw [hconj, conj_pow, h4, mul_one, mul_inv_cancel]
  rw [show k⁻¹ * a * k * (k⁻¹ * y * k) = k⁻¹ * (a * y) * k by group, conj_pow_inv] at hc
  calc (a * y) ^ 4 = k * (k⁻¹ * (a * y) ^ 4 * k) * k⁻¹ := by group
    _ = 1 := by rw [hc]; group

theorem four_base (hLoc : SmithE7LocalInput) (h34a : SmithE7E34a) (hLine : SmithE7E24Line)
    [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {x w y : G}
    (hx : IsConj S.z x) (hwc : IsConj S.z w) (hy : IsConj S.z y)
    (hxz : Commute x S.z) (hzw : Commute S.z w) (hwy : Commute w y)
    (hxw : ¬ Commute x w) (h4 : orderOf (x * w) = 4) :
    ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y := by
  have hloc := local_of_input hLoc S hw hU
  have hxM : x ∈ S.M := mem_centralizer_singleton_iff.mpr hxz.eq
  have hwM : w ∈ S.M := mem_centralizer_singleton_iff.mpr hzw.symm.eq
  have ha : IsConj S.z ((x * w) ^ 2) := (hloc x w hx hwc hxM hwM).2 h4
  obtain ⟨hxa, hwa, hxw', hwx'⟩ := dihedral_facts S hx hwc ha
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  rw [← hg] at hxa hwa hxw' hwx' ha
  have hxQa := mem_Qa_of_isConj_mul h34a S hw hU hx hxa
    (by rw [← hxw']; exact SmithGraph.isConj_conj hx w)
  have hwQa := mem_Qa_of_isConj_mul h34a S hw hU hwc hwa
    (by rw [← hwx']; exact SmithGraph.isConj_conj hwc x)
  obtain ⟨k, hk⟩ := isConj_iff.mp hwc
  have hwne : w ≠ g * S.z * g⁻¹ := fun he => hxw (by rw [he]; exact hxa)
  have haQw : k⁻¹ * (g * S.z * g⁻¹) * k ∈ S.QG :=
    mem_Qa_symm S (by rw [hk]; exact hwQa) (by rw [hk]; exact hwne)
  by_cases hay : Commute (g * S.z * g⁻¹) y
  · exact ⟨g * S.z * g⁻¹, ha, hxa, hay⟩
  have h4' : (g * S.z * g⁻¹ * y) ^ 4 = 1 :=
    pow_four_of_mem_Qa h34a S hw hU ha hy haQw (by rw [hk]; exact hwy)
  have hord := orderOf_eq_four_of_pow S ha hy hay h4'
  have hb : IsConj S.z ((g * S.z * g⁻¹ * y) ^ 2) := by
    have hyM' : k⁻¹ * y * k ∈ S.M := (mem_M_conj_iff S k y).mpr (by rw [hk]; exact hwy.symm)
    have he : k⁻¹ * (g * S.z * g⁻¹) * k * (k⁻¹ * y * k) = k⁻¹ * (g * S.z * g⁻¹ * y) * k := by
      group
    have h := (hloc _ _ (SmithGraph.isConj_conj ha k) (SmithGraph.isConj_conj hy k)
      (S.QG_le_M haQw) hyM').2 (by rw [he, orderOf_conj_inv]; exact hord)
    rw [he, conj_pow_inv] at h
    exact isConj_of_conj_inv k h
  obtain ⟨hab, hyb, hay', hya'⟩ := dihedral_facts S ha hy hb
  obtain ⟨l, hl⟩ := isConj_iff.mp hb
  rw [← hl] at hab hyb hay' hya' hb
  have haQb := mem_Qa_of_isConj_mul h34a S hw hU ha hab
    (by rw [← hay']; exact SmithGraph.isConj_conj ha y)
  have hyQb := mem_Qa_of_isConj_mul h34a S hw hU hy hyb
    (by rw [← hya']; exact SmithGraph.isConj_conj hy _)
  have hbne : l * S.z * l⁻¹ ≠ g * S.z * g⁻¹ := fun he => hay (by rw [← he]; exact hyb.symm)
  have hbQa : g⁻¹ * (l * S.z * l⁻¹) * g ∈ S.QG := mem_Qa_symm S haQb (Ne.symm hbne)
  by_cases hbx : Commute (l * S.z * l⁻¹) x
  · exact ⟨l * S.z * l⁻¹, hb, hbx.symm, hyb.symm⟩
  have hbz : g⁻¹ * (l * S.z * l⁻¹) * g ≠ S.z := fun he => hbne (by
    calc l * S.z * l⁻¹ = g * (g⁻¹ * (l * S.z * l⁻¹) * g) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by rw [he])
  have hgl : (g⁻¹ * l) * S.z * (g⁻¹ * l)⁻¹ = g⁻¹ * (l * S.z * l⁻¹) * g := by group
  obtain ⟨c', hc', hc'Q, hc'Qb, hc'z, hc'b, hc'zb⟩ :=
    hLine G S hw hU (g⁻¹ * l) (by rw [hgl]; exact hbQa) (by rw [hgl]; exact hbz)
  rw [hgl] at hc'b hc'zb
  rw [mem_Qa_iff] at hc'Qb
  obtain ⟨c, hc_def⟩ : ∃ c, c = g * c' * g⁻¹ := ⟨_, rfl⟩
  have hc : IsConj S.z c := hc'.trans (isConj_iff.mpr ⟨g, hc_def.symm⟩)
  have hcc' : g⁻¹ * c * g = c' := by rw [hc_def]; group
  have hcQa : g⁻¹ * c * g ∈ S.QG := by rw [hcc']; exact hc'Q
  have hcQb : l⁻¹ * c * l ∈ S.QG := by
    rw [hc_def, show l⁻¹ * (g * c' * g⁻¹) * l = (g⁻¹ * l)⁻¹ * c' * (g⁻¹ * l) by group]
    exact hc'Qb
  have hc1 : c ≠ 1 := ne_one_of_isConj S hc
  have hca : c ≠ g * S.z * g⁻¹ := fun he => hc'z (by rw [← hcc', he]; group)
  have hcb : c ≠ l * S.z * l⁻¹ := fun he => hc'b (by rw [← hcc', he])
  have hbi := inv_eq_of_isConj S (SmithGraph.isConj_conj hb g)
  have hcab : c * (l * S.z * l⁻¹) ≠ g * S.z * g⁻¹ := fun he => hc'zb (by
    calc c' = g⁻¹ * (c * (l * S.z * l⁻¹)) * g * (g⁻¹ * (l * S.z * l⁻¹) * g)⁻¹ := by
          rw [← hcc']; group
      _ = g⁻¹ * (g * S.z * g⁻¹) * g * (g⁻¹ * (l * S.z * l⁻¹) * g)⁻¹ := by rw [he]
      _ = S.z * (g⁻¹ * (l * S.z * l⁻¹) * g) := by rw [hbi]; group)
  have hcaC : IsConj S.z (c * (g * S.z * g⁻¹)) :=
    hc.trans (isConj_mul_of_mem_Qa S hcQa hc1 hca)
  have hcbC : IsConj S.z (c * (l * S.z * l⁻¹)) :=
    hc.trans (isConj_mul_of_mem_Qa S hcQb hc1 hcb)
  have hcbQa : g⁻¹ * (c * (l * S.z * l⁻¹)) * g ∈ S.QG := by
    rw [show g⁻¹ * (c * (l * S.z * l⁻¹)) * g = (g⁻¹ * c * g) * (g⁻¹ * (l * S.z * l⁻¹) * g) by
      group]
    exact S.QG.mul_mem hcQa hbQa
  have hcb1 : c * (l * S.z * l⁻¹) ≠ 1 := fun he => hcb (by
    calc c = (c * (l * S.z * l⁻¹)) * (l * S.z * l⁻¹)⁻¹ := by group
      _ = l * S.z * l⁻¹ := by rw [he, one_mul, inv_eq_of_isConj S hb])
  have hcbaC : IsConj S.z (c * (l * S.z * l⁻¹) * (g * S.z * g⁻¹)) :=
    hcbC.trans (isConj_mul_of_mem_Qa S hcbQa hcb1 hcab)
  by_cases hcx : Commute c x <;> by_cases hcy : Commute c y
  · exact ⟨c, hc, hcx.symm, hcy⟩
  · exact ⟨c * (g * S.z * g⁻¹), hcaC, hcx.symm.mul_right hxa,
      commute_mul_of_not_commute S hcQb haQb hyQb hcy hay⟩
  · exact ⟨c * (l * S.z * l⁻¹), hcbC,
      (commute_mul_of_not_commute S hcQa hbQa hxQa hcx hbx).symm, hcy.mul_left hyb.symm⟩
  · refine ⟨c * (l * S.z * l⁻¹) * (g * S.z * g⁻¹), hcbaC,
      ((commute_mul_of_not_commute S hcQa hbQa hxQa hcx hbx).mul_left hxa.symm).symm, ?_⟩
    have hcay := commute_mul_of_not_commute S hcQb haQb hyQb hcy hay
    rw [mul_assoc, ← hab.eq, ← mul_assoc]
    exact hcay.mul_left hyb.symm

theorem four_gen (hLoc : SmithE7LocalInput) (h34a : SmithE7E34a) (hLine : SmithE7E24Line)
    [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {x u w y : G}
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


theorem smithE7PathInput_of (h34a : SmithE7E34a) (h34b : SmithE7E34b) (h23 : SmithE7E23)
    (h24 : SmithE7E24) (h25 : SmithE7E25) (h23f : SmithE7E23Four) (hLine : SmithE7E24Line)
    (h421 : SmithE7E421Three) :
    SmithE7PathInput := by
  have hLoc := smithE7LocalInput_of h34a h34b h23 h24 h25 h23f
  intro G _ _ _ S hw hU x w y hx hwc hy hxz hzw hwy hxw hzy hxy
  have hloc := local_of_input hLoc S hw hU
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
      obtain ⟨v, hv, hyv, hvx⟩ := four_gen hLoc h34a hLine S hw hU hy hwc hz hx hwy.symm
        hzw.symm hxz.symm (fun h => hzy h.symm) hyz
      exact ⟨v, hv, hvx.symm, hyv.symm⟩
  · exact four_base hLoc h34a hLine S hw hU hx hwc hy hxz hzw hwy hxw h4


end CFSG.GF2Type.SmithTypeE.E7
