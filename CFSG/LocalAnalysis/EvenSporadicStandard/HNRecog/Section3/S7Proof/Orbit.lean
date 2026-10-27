module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem s7o_mul_conj_eq {a c k : G} (hk : k ∈ Gx a) :
    a * (k * c * k⁻¹) = k * (a * c) * k⁻¹ := by
  have hak : a * k = k * a := mem_Gx.mp hk
  calc a * (k * c * k⁻¹) = (a * k) * c * k⁻¹ := by group
    _ = (k * a) * c * k⁻¹ := by rw [hak]
    _ = k * (a * c) * k⁻¹ := by group

private theorem s7o_orderOf_conj (k x : G) : orderOf (k * x * k⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj k) x)

private theorem s7o_conj_mem_orb3A {a c k : G} (hk : k ∈ Gx a) (hcA : IsConj a c)
    (hco : orderOf (a * c) = 3) (hne : (orb2A a a ∩ orb2A a c).Nonempty) :
    k * c * k⁻¹ ∈ orb3A a a := by
  obtain ⟨t, ht⟩ := hne
  simp only [orb3A, Set.mem_setOf_eq]
  exact ⟨IsConj.trans hcA (isConj_iff.mpr ⟨k, rfl⟩),
    by rw [s7o_mul_conj_eq hk, s7o_orderOf_conj, hco],
    ⟨k * t * k⁻¹, perp_conj_mem_orb2A hk ht.1, s7_conj_orb2A k ht.2⟩⟩

theorem s7_orbit {a z : G} (H : S7Hyps a z) : IsConjOrbit (Gx a) (orb3A a a) := by
  have hT4 := H.tableIV.self
  have hT5 := H.tableV.self
  have hF5 := H.isF5
  refine ⟨?_, ?_, ?_⟩
  · intro k hk c hc
    simp only [orb3A, Set.mem_setOf_eq] at hc
    obtain ⟨hcA, hco, hne⟩ := hc
    exact s7o_conj_mem_orb3A hk hcA hco hne
  · obtain ⟨b, hb0⟩ := (hT5.partition.orbit 0).nonempty
    have hb : b ∈ orb2A a a := by simpa [tab5Set] using hb0
    obtain ⟨c, hc⟩ := ((hT4.partition b hb).orbit 4).nonempty
    have hc4 : c ∈ sBase a b ∧ orderOf (a * c) = 3 := by simpa [sSet] using hc
    refine ⟨c, ?_⟩
    simp only [orb3A, Set.mem_setOf_eq]
    exact ⟨hc4.1.1, hc4.2, ⟨b, perp_self_mem_inter hF5 hb hc4.1⟩⟩
  · intro c hc c' hc'
    simp only [orb3A, Set.mem_setOf_eq] at hc hc'
    obtain ⟨hcA, hco, hne⟩ := hc
    obtain ⟨hc'A, hc'o, hne'⟩ := hc'
    obtain ⟨t, ht⟩ := hne
    obtain ⟨t', ht'⟩ := hne'
    obtain ⟨k₁, hk₁Gx, hk₁t⟩ :=
      (hT5.partition.orbit 0).transitive t (by simpa [tab5Set] using ht.1) t'
        (by simpa [tab5Set] using ht'.1)
    set c'' : G := k₁ * c * k₁⁻¹ with hc''def
    have hc''3 : c'' ∈ orb3A a a := by
      rw [hc''def]
      exact s7o_conj_mem_orb3A hk₁Gx hcA hco ⟨t, ht⟩
    have hc''u : IsConj a c'' ∧ orderOf (a * c'') = 3 ∧
        (orb2A a a ∩ orb2A a c'').Nonempty := by
      simpa only [orb3A, Set.mem_setOf_eq] using hc''3
    obtain ⟨hc''A, hc''o, _⟩ := hc''u
    have ht'c'' : t' ∈ orb2A a a ∩ orb2A a c'' := by
      refine ⟨ht'.1, ?_⟩
      rw [← hk₁t]
      exact s7_conj_orb2A k₁ ht.2
    have hc''s : c'' ∈ sSet a z t' 4 := s7_mem_sSet_four H hc''A hc''o ht'c''
    have hc's : c' ∈ sSet a z t' 4 := s7_mem_sSet_four H hc'A hc'o ht'
    obtain ⟨k₂, hk₂Gxy, hk₂c⟩ :=
      ((hT4.partition t' ht'.1).orbit 4).transitive c'' hc''s c' hc's
    refine ⟨k₂ * k₁, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (mem_Gxy.mp hk₂Gxy).1 hk₁Gx
    · calc (k₂ * k₁) * c * (k₂ * k₁)⁻¹
          = k₂ * (k₁ * c * k₁⁻¹) * k₂⁻¹ := by group
        _ = k₂ * c'' * k₂⁻¹ := by rw [hc''def]
        _ = c' := hk₂c

end CFSG.EvenSporadicStandard.HNRecog.Section3
