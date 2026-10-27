module

public import CFSG.LargeExtraspecial.S14SMEConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SME

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem dihedral_facts (S : Setting G) {x w : G} (hx : IsConj S.z x) (hw : IsConj S.z w)
    (ha : IsConj S.z ((x * w) ^ 2)) :
    Commute x ((x * w) ^ 2) ∧ Commute w ((x * w) ^ 2) ∧
      w⁻¹ * x * w = x * (x * w) ^ 2 ∧ x⁻¹ * w * x = w * (x * w) ^ 2 := by
  have xi := inv_eq_of_isConj S hx
  have wi := inv_eq_of_isConj S hw
  have ai := inv_eq_of_isConj S ha
  have hxx := SmithQ.mul_self_eq_one_of_isConj S hx
  have hww := SmithQ.mul_self_eq_one_of_isConj S hw
  have hxx' : ∀ t, x * (x * t) = t := fun t => by rw [← mul_assoc, hxx, one_mul]
  have hww' : ∀ t, w * (w * t) = t := fun t => by rw [← mul_assoc, hww, one_mul]
  have e1 : x * (x * w) ^ 2 = ((x * w) ^ 2)⁻¹ * x := by
    rw [sq, mul_inv_rev, mul_inv_rev, xi, wi]
    simp only [mul_assoc, hxx, hxx', mul_one]
  have e2 : w * (x * w) ^ 2 = ((x * w) ^ 2)⁻¹ * w := by
    rw [sq, mul_inv_rev, mul_inv_rev, xi, wi]
    simp only [mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Commute, SemiconjBy, e1, ai]
  · rw [Commute, SemiconjBy, e2, ai]
  · rw [wi, sq]
    simp only [mul_assoc, hxx']
  · rw [← ai, sq, mul_inv_rev, mul_inv_rev, xi, wi]
    simp only [mul_assoc, hww']

theorem commute_of_sq_eq_one (S : Setting G) {x w : G} (hx : IsConj S.z x) (hw : IsConj S.z w)
    (h : (x * w) ^ 2 = 1) : Commute x w := by
  have xi := inv_eq_of_isConj S hx
  have wi := inv_eq_of_isConj S hw
  have h1 : x * w = (x * w)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← sq]; exact h)
  rw [mul_inv_rev, xi, wi] at h1
  exact h1

theorem orderOf_eq_three_or_four (S : Setting G) {x w : G} (hx : IsConj S.z x)
    (hw : IsConj S.z w) (hxw : ¬ Commute x w) (h : orderOf (x * w) ∈ ({1, 2, 3, 4} : Set ℕ)) :
    orderOf (x * w) = 3 ∨ orderOf (x * w) = 4 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h
  · exfalso
    apply hxw (commute_of_sq_eq_one S hx hw _)
    rw [orderOf_eq_one_iff.mp h, one_pow]
  · exfalso
    apply hxw (commute_of_sq_eq_one S hx hw _)
    rw [← h, pow_orderOf_eq_one]
  · exact Or.inl h
  · exact Or.inr h

theorem orderOf_eq_four_of_pow (S : Setting G) {a y : G} (ha : IsConj S.z a)
    (hy : IsConj S.z y) (hay : ¬ Commute a y) (h4 : (a * y) ^ 4 = 1) : orderOf (a * y) = 4 := by
  have hd : orderOf (a * y) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hle : orderOf (a * y) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have h2 : ¬ orderOf (a * y) ∣ 2 := fun h2 =>
    hay (commute_of_sq_eq_one S ha hy (orderOf_dvd_iff_pow_eq_one.mp h2))
  interval_cases h : orderOf (a * y) <;> simp_all

theorem isConj_of_conj_inv {z t : G} (c : G) (h : IsConj z (c⁻¹ * t * c)) : IsConj z t :=
  h.trans (isConj_iff.mpr ⟨c, by group⟩)

theorem four_base (hLoc : SmithU62LocalInput) (h34a : SmithE34a) (hLine : SmithE24Line)
    [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {x w y : G}
    (hx : IsConj S.z x) (hwc : IsConj S.z w) (hy : IsConj S.z y)
    (hxz : Commute x S.z) (hzw : Commute S.z w) (hwy : Commute w y)
    (hxw : ¬ Commute x w) (h4 : orderOf (x * w) = 4) :
    ∃ v : G, IsConj S.z v ∧ Commute x v ∧ Commute v y := by
  have hloc := SmithGraph.local_of_input hLoc S hw hU
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

end SME

end CFSG.LargeExtraspecial.S14
