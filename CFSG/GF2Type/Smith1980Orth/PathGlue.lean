module

public import CFSG.GF2Type.Smith1980Orth.LocalGlue
public import CFSG.LargeExtraspecial.S14SMEFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G] [Finite G]

@[expose] def OLocal (S : Setting G) : Prop :=
  ∀ x y : G, IsConj S.z x → IsConj S.z y → x ∈ S.M → y ∈ S.M → x ∉ S.QG →
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧ (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2))

@[expose] def OE24Line (S : Setting G) : Prop :=
  ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
    ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ S.Qa h ∧ c ≠ S.z ∧ c ≠ h * S.z * h⁻¹ ∧
      c ≠ S.z * (h * S.z * h⁻¹)

@[expose] def OE421Three (S : Setting G) : Prop :=
  ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
    Commute x S.z → Commute S.z w → Commute w y →
      ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
        orderOf (x * w) = 3 → orderOf (S.z * y) = 3 →
          ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

@[expose] def OPath (S : Setting G) : Prop :=
  ∀ x w y : G, IsConj S.z x → IsConj S.z w → IsConj S.z y →
    Commute x S.z → Commute S.z w → Commute w y →
      ¬ Commute x w → ¬ Commute S.z y → ¬ Commute x y →
        ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y

theorem local_of_OLocal (S : Setting G) (hLoc : OLocal S) (x y : G)
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  by_cases hxQ : x ∈ S.QG
  · by_cases hyQ : y ∈ S.QG
    · exact SmithQ.orderOf_mul_mem_of_mem_QG S hxQ hyQ
    · obtain ⟨h1, h2⟩ := hLoc y x hy hx hyM hxM hyQ
      have hord : orderOf (y * x) = orderOf (x * y) := by
        rw [show y * x = MulAut.conj y (x * y) by rw [MulAut.conj_apply]; group,
          MulEquiv.orderOf_eq]
      rw [hord] at h1 h2
      refine ⟨h1, fun h4 => ?_⟩
      rw [show (x * y) ^ 2 = x * (y * x) ^ 2 * x⁻¹ by rw [_root_.sq, _root_.sq]; group]
      exact (h2 h4).trans (isConj_iff.mpr ⟨x, rfl⟩)
  · exact hLoc x y hx hy hxM hyM hxQ

theorem mem_Qa_of_isConj_mul' (S : Setting G) (h34a : OE34a S) {g x : G}
    (hx : IsConj S.z x) (hxa : Commute x (g * S.z * g⁻¹))
    (hxa' : IsConj S.z (x * (g * S.z * g⁻¹))) : g⁻¹ * x * g ∈ S.QG := by
  by_contra hQ
  apply h34a _ (SmithGraph.isConj_conj hx g) ((SME.mem_M_conj_iff S g x).mpr hxa) hQ
  have h : g⁻¹ * x * g * S.z = g⁻¹ * (x * (g * S.z * g⁻¹)) * g := by group
  rw [h]
  exact SmithGraph.isConj_conj hxa' g

theorem pow_four_of_mem_Qa' (S : Setting G) (h34a : OE34a S) {k a y : G}
    (ha : IsConj S.z a) (hy : IsConj S.z y) (haQ : k⁻¹ * a * k ∈ S.QG)
    (hyw : Commute (k * S.z * k⁻¹) y) : (a * y) ^ 4 = 1 := by
  have hyM : k⁻¹ * y * k ∈ S.M := (SME.mem_M_conj_iff S k y).mpr hyw.symm
  have hc : (k⁻¹ * a * k * (k⁻¹ * y * k)) ^ 4 = 1 := by
    by_cases hyQ : k⁻¹ * y * k ∈ S.QG
    · exact S.pow_four_eq_one (S.QG.mul_mem haQ hyQ)
    · have hai := SME.inv_eq_of_isConj S (SmithGraph.isConj_conj ha k)
      have hyi := SME.inv_eq_of_isConj S (SmithGraph.isConj_conj hy k)
      set a' := k⁻¹ * a * k
      set y' := k⁻¹ * y * k
      have hsq : ((y' * a') ^ 2) ^ 2 = 1 := by
        have he : (y' * a') ^ 2 = y' * a' * y'⁻¹ * a'⁻¹ := by
          rw [hai, hyi, sq]
          simp only [mul_assoc]
        rw [he]
        exact sq_eq_one_of_mem_commutator' S h34a (SmithGraph.isConj_conj hy k) hyM hyQ
          (SME.commutator_mem S y' haQ)
      have h4 : (y' * a') ^ 4 = 1 := by rw [← hsq, ← pow_mul]
      have hconj : a' * y' = a' * (y' * a') * a'⁻¹ := by group
      rw [hconj, conj_pow, h4, mul_one, mul_inv_cancel]
  rw [show k⁻¹ * a * k * (k⁻¹ * y * k) = k⁻¹ * (a * y) * k by group, SME.conj_pow_inv] at hc
  calc (a * y) ^ 4 = k * (k⁻¹ * (a * y) ^ 4 * k) * k⁻¹ := by group
    _ = 1 := by rw [hc]; group

theorem four_base' (S : Setting G) (hLoc : OLocal S) (h34a : OE34a S) (hLine : OE24Line S)
    {x w y : G} (hx : IsConj S.z x) (hwc : IsConj S.z w) (hy : IsConj S.z y)
    (hxz : Commute x S.z) (hzw : Commute S.z w) (hwy : Commute w y)
    (hxw : ¬ Commute x w) (h4 : orderOf (x * w) = 4) :
    ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y := by
  have hloc := local_of_OLocal S hLoc
  have hxM : x ∈ S.M := Subgroup.mem_centralizer_singleton_iff.mpr hxz.eq
  have hwM : w ∈ S.M := Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm.eq
  have ha : IsConj S.z ((x * w) ^ 2) := (hloc x w hx hwc hxM hwM).2 h4
  obtain ⟨hxa, hwa, hxw', hwx'⟩ := SME.dihedral_facts S hx hwc ha
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  rw [← hg] at hxa hwa hxw' hwx' ha
  have hxQa := mem_Qa_of_isConj_mul' S h34a hx hxa
    (by rw [← hxw']; exact SmithGraph.isConj_conj hx w)
  have hwQa := mem_Qa_of_isConj_mul' S h34a hwc hwa
    (by rw [← hwx']; exact SmithGraph.isConj_conj hwc x)
  obtain ⟨k, hk⟩ := isConj_iff.mp hwc
  have hwne : w ≠ g * S.z * g⁻¹ := fun he => hxw (by rw [he]; exact hxa)
  have haQw : k⁻¹ * (g * S.z * g⁻¹) * k ∈ S.QG :=
    SME.mem_Qa_symm S (by rw [hk]; exact hwQa) (by rw [hk]; exact hwne)
  by_cases hay : Commute (g * S.z * g⁻¹) y
  · exact ⟨g * S.z * g⁻¹, ha, hxa, hay⟩
  have h4' : (g * S.z * g⁻¹ * y) ^ 4 = 1 :=
    pow_four_of_mem_Qa' S h34a ha hy haQw (by rw [hk]; exact hwy)
  have hord := SME.orderOf_eq_four_of_pow S ha hy hay h4'
  have hb : IsConj S.z ((g * S.z * g⁻¹ * y) ^ 2) := by
    have hyM' : k⁻¹ * y * k ∈ S.M :=
      (SME.mem_M_conj_iff S k y).mpr (by rw [hk]; exact hwy.symm)
    have he : k⁻¹ * (g * S.z * g⁻¹) * k * (k⁻¹ * y * k) = k⁻¹ * (g * S.z * g⁻¹ * y) * k := by
      group
    have h := (hloc _ _ (SmithGraph.isConj_conj ha k) (SmithGraph.isConj_conj hy k)
      (S.QG_le_M haQw) hyM').2 (by rw [he, SME.orderOf_conj_inv]; exact hord)
    rw [he, SME.conj_pow_inv] at h
    exact SME.isConj_of_conj_inv k h
  obtain ⟨hab, hyb, hay', hya'⟩ := SME.dihedral_facts S ha hy hb
  obtain ⟨l, hl⟩ := isConj_iff.mp hb
  rw [← hl] at hab hyb hay' hya' hb
  have haQb := mem_Qa_of_isConj_mul' S h34a ha hab
    (by rw [← hay']; exact SmithGraph.isConj_conj ha y)
  have hyQb := mem_Qa_of_isConj_mul' S h34a hy hyb
    (by rw [← hya']; exact SmithGraph.isConj_conj hy _)
  have hbne : l * S.z * l⁻¹ ≠ g * S.z * g⁻¹ := fun he => hay (by rw [← he]; exact hyb.symm)
  have hbQa : g⁻¹ * (l * S.z * l⁻¹) * g ∈ S.QG := SME.mem_Qa_symm S haQb (Ne.symm hbne)
  by_cases hbx : Commute (l * S.z * l⁻¹) x
  · exact ⟨l * S.z * l⁻¹, hb, hbx.symm, hyb.symm⟩
  have hbz : g⁻¹ * (l * S.z * l⁻¹) * g ≠ S.z := fun he => hbne (by
    calc l * S.z * l⁻¹ = g * (g⁻¹ * (l * S.z * l⁻¹) * g) * g⁻¹ := by group
      _ = g * S.z * g⁻¹ := by rw [he])
  have hgl : (g⁻¹ * l) * S.z * (g⁻¹ * l)⁻¹ = g⁻¹ * (l * S.z * l⁻¹) * g := by group
  obtain ⟨c', hc', hc'Q, hc'Qb, hc'z, hc'b, hc'zb⟩ :=
    hLine (g⁻¹ * l) (by rw [hgl]; exact hbQa) (by rw [hgl]; exact hbz)
  rw [hgl] at hc'b hc'zb
  rw [SME.mem_Qa_iff] at hc'Qb
  obtain ⟨c, hc_def⟩ : ∃ c, c = g * c' * g⁻¹ := ⟨_, rfl⟩
  have hc : IsConj S.z c := hc'.trans (isConj_iff.mpr ⟨g, hc_def.symm⟩)
  have hcc' : g⁻¹ * c * g = c' := by rw [hc_def]; group
  have hcQa : g⁻¹ * c * g ∈ S.QG := by rw [hcc']; exact hc'Q
  have hcQb : l⁻¹ * c * l ∈ S.QG := by
    rw [hc_def, show l⁻¹ * (g * c' * g⁻¹) * l = (g⁻¹ * l)⁻¹ * c' * (g⁻¹ * l) by group]
    exact hc'Qb
  have hc1 : c ≠ 1 := SME.ne_one_of_isConj S hc
  have hca : c ≠ g * S.z * g⁻¹ := fun he => hc'z (by rw [← hcc', he]; group)
  have hcb : c ≠ l * S.z * l⁻¹ := fun he => hc'b (by rw [← hcc', he])
  have hbi := SME.inv_eq_of_isConj S (SmithGraph.isConj_conj hb g)
  have hcab : c * (l * S.z * l⁻¹) ≠ g * S.z * g⁻¹ := fun he => hc'zb (by
    calc c' = g⁻¹ * (c * (l * S.z * l⁻¹)) * g * (g⁻¹ * (l * S.z * l⁻¹) * g)⁻¹ := by
          rw [← hcc']; group
      _ = g⁻¹ * (g * S.z * g⁻¹) * g * (g⁻¹ * (l * S.z * l⁻¹) * g)⁻¹ := by rw [he]
      _ = S.z * (g⁻¹ * (l * S.z * l⁻¹) * g) := by rw [hbi]; group)
  have hcaC : IsConj S.z (c * (g * S.z * g⁻¹)) :=
    hc.trans (SME.isConj_mul_of_mem_Qa S hcQa hc1 hca)
  have hcbC : IsConj S.z (c * (l * S.z * l⁻¹)) :=
    hc.trans (SME.isConj_mul_of_mem_Qa S hcQb hc1 hcb)
  have hcbQa : g⁻¹ * (c * (l * S.z * l⁻¹)) * g ∈ S.QG := by
    rw [show g⁻¹ * (c * (l * S.z * l⁻¹)) * g = (g⁻¹ * c * g) * (g⁻¹ * (l * S.z * l⁻¹) * g) by
      group]
    exact S.QG.mul_mem hcQa hbQa
  have hcb1 : c * (l * S.z * l⁻¹) ≠ 1 := fun he => hcb (by
    calc c = (c * (l * S.z * l⁻¹)) * (l * S.z * l⁻¹)⁻¹ := by group
      _ = l * S.z * l⁻¹ := by rw [he, one_mul, SME.inv_eq_of_isConj S hb])
  have hcbaC : IsConj S.z (c * (l * S.z * l⁻¹) * (g * S.z * g⁻¹)) :=
    hcbC.trans (SME.isConj_mul_of_mem_Qa S hcbQa hcb1 hcab)
  by_cases hcx : Commute c x <;> by_cases hcy : Commute c y
  · exact ⟨c, hc, hcx.symm, hcy⟩
  · exact ⟨c * (g * S.z * g⁻¹), hcaC, hcx.symm.mul_right hxa,
      SME.commute_mul_of_not_commute S hcQb haQb hyQb hcy hay⟩
  · exact ⟨c * (l * S.z * l⁻¹), hcbC,
      (SME.commute_mul_of_not_commute S hcQa hbQa hxQa hcx hbx).symm, hcy.mul_left hyb.symm⟩
  · refine ⟨c * (l * S.z * l⁻¹) * (g * S.z * g⁻¹), hcbaC,
      ((SME.commute_mul_of_not_commute S hcQa hbQa hxQa hcx hbx).mul_left hxa.symm).symm, ?_⟩
    have hcay := SME.commute_mul_of_not_commute S hcQb haQb hyQb hcy hay
    rw [mul_assoc, ← hab.eq, ← mul_assoc]
    exact hcay.mul_left hyb.symm

theorem four_gen' (S : Setting G) (hLoc : OLocal S) (h34a : OE34a S) (hLine : OE24Line S)
    {x u w y : G} (hx : IsConj S.z x) (hu : IsConj S.z u) (hwc : IsConj S.z w)
    (hy : IsConj S.z y) (hxu : Commute x u) (huw : Commute u w) (hwy : Commute w y)
    (hxw : ¬ Commute x w) (h4 : orderOf (x * w) = 4) :
    ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hu
  have h1 := (SmithGraph.commute_conj_iff c x (c * S.z * c⁻¹)).mpr hxu
  have h2 := (SmithGraph.commute_conj_iff c (c * S.z * c⁻¹) w).mpr huw
  rw [SME.conj_conj_inv] at h1 h2
  obtain ⟨v, hv, hxv, hvy⟩ := four_base' S hLoc h34a hLine (SmithGraph.isConj_conj hx c)
    (SmithGraph.isConj_conj hwc c) (SmithGraph.isConj_conj hy c) h1 h2
    ((SmithGraph.commute_conj_iff c w y).mpr hwy)
    (fun h => hxw ((SmithGraph.commute_conj_iff c x w).mp h))
    (by rw [show c⁻¹ * x * c * (c⁻¹ * w * c) = c⁻¹ * (x * w) * c by group,
        SME.orderOf_conj_inv]
        exact h4)
  have hvv : c⁻¹ * (c * v * c⁻¹) * c = v := by group
  refine ⟨c * v * c⁻¹, hv.trans (isConj_iff.mpr ⟨c, rfl⟩), ?_, ?_⟩
  · rw [← SmithGraph.commute_conj_iff c, hvv]
    exact hxv
  · rw [← SmithGraph.commute_conj_iff c, hvv]
    exact hvy

theorem oPath_of (S : Setting G) (hLoc : OLocal S) (h34a : OE34a S) (hLine : OE24Line S)
    (h421 : OE421Three S) : OPath S := by
  intro x w y hx hwc hy hxz hzw hwy hxw hzy hxy
  have hloc := local_of_OLocal S hLoc
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
    · exact h421 x w y hx hwc hy hxz hzw hwy hxw hzy hxy h3 h3'
    · have hyz : orderOf (y * S.z) = 4 := by
        rw [show y * S.z = S.z⁻¹ * (S.z * y) * S.z by group, SME.orderOf_conj_inv]
        exact h4'
      obtain ⟨v, hv, hyv, hvx⟩ := four_gen' S hLoc h34a hLine hy hwc hz hx hwy.symm
        hzw.symm hxz.symm (fun h => hzy h.symm) hyz
      exact ⟨v, hv, hvx.symm, hyv.symm⟩
  · exact four_base' S hLoc h34a hLine hx hwc hy hxz hzw hwy hxw h4

end CFSG.GF2Type.Smith1980Orth
