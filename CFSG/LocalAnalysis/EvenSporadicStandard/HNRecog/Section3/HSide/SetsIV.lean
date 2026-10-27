module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Dict

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {b z : G} {z₀ b₀ u₀ : ↥(Gx b)}

private theorem image_setOf_of_base {S' : Set ↥(Gx b)} {S : Set G}
    (hS : S = Subtype.val '' S') {P : G → Prop} {Q : ↥(Gx b) → Prop}
    (hPQ : ∀ c' ∈ S', P (c' : G) ↔ Q c') :
    {c | c ∈ S ∧ P c} = Subtype.val '' {c' | c' ∈ S' ∧ Q c'} := by
  ext c
  constructor
  · rintro ⟨hcS, hP⟩
    rw [hS] at hcS
    rcases hcS with ⟨c', hc', rfl⟩
    exact ⟨c', ⟨hc', (hPQ c' hc').1 hP⟩, rfl⟩
  · rintro ⟨c', ⟨hc', hQ⟩, rfl⟩
    exact ⟨by rw [hS]; exact ⟨c', hc', rfl⟩, (hPQ c' hc').2 hQ⟩

private theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (MulEquiv.orderOf_eq (MulAut.conj c) x).symm.trans
    (congrArg orderOf (MulAut.conj_apply c x))

theorem sBase_eq (L : HLab b z z₀ b₀ u₀) {y : ↥(Gx b)} (hy : IsConj b₀ y) :
    sBase (y : G) b = Subtype.val '' tab4Base (GxSelf b) b₀ y := by
  have hbord : orderOf b = 2 := by
    simpa [GxSelf] using (Subgroup.orderOf_coe (GxSelf b)).trans L.facts.orderOf_a
  have hb2 : b ^ 2 = 1 := by
    have h := pow_orderOf_eq_one b
    rwa [hbord] at h
  have hyA : IsConj b (y : G) := ((L.isConj_b₀_iff y).1 hy).1
  have hyb : b * (y : G) = (y : G) * b := mem_Gx.1 y.2
  have hy2 : (y : G) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (y : G)
    have h2 : orderOf (y : G) = 2 := (orderOf_eq_of_isConj hyA).symm.trans hbord
    rwa [h2] at h
  ext c
  constructor
  · intro hc
    obtain ⟨hcA, hcB, hcne1, hcne2⟩ := hc
    have hcGx : c ∈ Gx b :=
      mem_Gx_of_isConj_mul hy2 hb2 hyA.symm hcA (Or.inl hcB)
    refine ⟨⟨c, hcGx⟩, ⟨?_, ?_, ?_⟩, rfl⟩
    · rw [L.isConj_b₀_iff]
      exact ⟨hyA.trans hcA, hyA.trans hcB⟩
    · intro h
      exact hcne1 (congrArg Subtype.val h)
    · intro h
      apply hcne2
      have h' := congrArg Subtype.val h
      change c = b * (y : G) at h'
      rw [hyb] at h'
      exact h'
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨hc'conj, hc'ne1, hc'ne2⟩ := hc'
    obtain ⟨hc'A, hc'B⟩ := (L.isConj_b₀_iff c').1 hc'conj
    refine ⟨hyA.symm.trans hc'A, hyA.symm.trans hc'B, ?_, ?_⟩
    · intro h
      exact hc'ne1 (Subtype.ext h)
    · intro h
      apply hc'ne2
      apply Subtype.ext
      change (c' : G) = b * (y : G)
      rw [hyb]
      exact h

theorem sSet_eq (L : HLab b z z₀ b₀ u₀) {y : ↥(Gx b)} (hy : IsConj b₀ y) (i : Fin 6) :
    sSet (y : G) z b i = Subtype.val '' tab4Set (GxSelf b) z₀ b₀ u₀ y i := by
  have hbase := sBase_eq L hy
  have hyA : IsConj b (y : G) := ((L.isConj_b₀_iff y).1 hy).1
  fin_cases i <;> simp [sSet, tab4Set]
  · exact image_setOf_of_base hbase (by
      intro c' _
      rw [← isConj_iff, L.isA_iff (y * c'), Subgroup.coe_mul]
      exact ⟨fun h => hyA.trans h, fun h => hyA.symm.trans h⟩)
  · exact image_setOf_of_base hbase (by
      intro c' _
      rw [← isConj_iff, L.isB_iff (y * c'), Subgroup.coe_mul])
  · exact image_setOf_of_base hbase (by
      intro c' _
      rw [Subtype.ext_iff]
      exact Iff.rfl)
  · exact image_setOf_of_base hbase (by
      intro c' _
      rw [← isConj_iff, L.isB_iff ((y * c') ^ 2)]
      simp only [Subgroup.coe_pow, Subgroup.coe_mul])
  · exact image_setOf_of_base hbase (by
      intro c' _
      constructor
      · intro h
        rwa [← Subgroup.orderOf_coe (y * c')]
      · intro h
        rwa [← Subgroup.orderOf_coe (y * c')] at h)
  · exact image_setOf_of_base hbase (by
      intro c' _
      rw [Subtype.ext_iff]
      exact Iff.rfl)

end CFSG.EvenSporadicStandard.HNRecog.Section3
