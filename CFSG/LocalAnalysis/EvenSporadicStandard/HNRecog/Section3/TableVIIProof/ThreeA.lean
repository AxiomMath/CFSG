module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.Orders

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

theorem tableVII_orb3A_subset (h : IsF5Type a z) : orb3A a a ⊆ oddSet a a := by
  intro c hc
  obtain ⟨hca, h3, t, ht⟩ := hc
  have haa : a * a = 1 := by
    rw [← pow_two]
    exact tableVII_sq_of_isConj_a h (IsConj.refl a)
  refine ⟨hca, ?_, by rw [h3]; exact ⟨1, rfl⟩, t, ht.1.1, ?_⟩
  · intro he
    rw [he, haa, orderOf_one] at h3
    exact absurd h3 (by decide)
  · exact mem_Gxy.2 ⟨tableVII_mem_Gx_of_orb2A h (IsConj.refl a) ht.1,
      tableVII_mem_Gx_of_orb2A h hca ht.2⟩

private theorem tableVII_threeA_isConj_conj {x y : G} (g : G) (hy : IsConj x y) :
    IsConj x (g * y * g⁻¹) :=
  hy.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem tableVII_mem_orb3A_of_tSet (h : IsF5Type a z) (hT5 : TableVFacts a z)
    (hS7 : S7Facts a z) (hT6 : TableVIFacts a z) {c t : G} (ht : t ∈ orb2B a z a)
    (hc : c ∈ tSet a z t 2) : c ∈ orb3A a a := by
  obtain ⟨c₀, hc₀⟩ := hS7.orbit.nonempty
  obtain ⟨t₀, ht₀⟩ := ((hS7.classes c₀ hc₀).orbit 1).nonempty
  have ht₀' : t₀ ∈ orb2B a z a ∩ orb2B a z c₀ := ht₀
  obtain ⟨hc₀a, hc₀3, -⟩ := id hc₀
  have hcomm₀ : c₀ * t₀ = t₀ * c₀ := mem_Gx.1 (tableVII_mem_Gx_of_orb2B h hc₀a ht₀'.2)
  have hc₀ne : c₀ ≠ a := (tableVII_orb3A_subset h hc₀).2.1
  have hc₀T : c₀ ∈ tSet a z t₀ 2 := ⟨⟨hc₀a, by rw [← hcomm₀]; exact ht₀'.2.2, hc₀ne⟩, hc₀3⟩
  obtain ⟨g, hg, hgt⟩ := (hT5.partition.orbit 1).transitive t ht t₀ ht₀'.1
  have hga : g * a * g⁻¹ = a := by
    rw [← mem_Gx.1 hg]
    group
  have hc' : c ∈ tBase a z t ∧ orderOf (a * c) = 3 := hc
  obtain ⟨⟨hca, hctz, hcne⟩, hc3⟩ := hc'
  have hgc : g * c * g⁻¹ ∈ tSet a z t₀ 2 := by
    refine ⟨⟨tableVII_threeA_isConj_conj g hca, ?_, ?_⟩, ?_⟩
    · rw [← hgt, show g * t * g⁻¹ * (g * c * g⁻¹) = g * (t * c) * g⁻¹ by group]
      exact tableVII_threeA_isConj_conj g hctz
    · intro he
      apply hcne
      have he' : g * c * g⁻¹ = g * a * g⁻¹ := by rw [he, hga]
      exact mul_left_cancel (mul_right_cancel he')
    · have hord := MulEquiv.orderOf_eq (MulAut.conj g) (a * c)
      rw [MulAut.conj_apply] at hord
      rw [mul_conj_of_fix hga, hord, hc3]
  obtain ⟨k, hk, hkc⟩ := ((hT6.partition t₀ ht₀'.1).orbit 2).transitive _ hgc c₀ hc₀T
  have hka : k ∈ Gx a := (mem_Gxy.1 hk).1
  have hkg : (k * g)⁻¹ ∈ Gx a := inv_mem (mul_mem hka hg)
  have hc_eq : c = (k * g)⁻¹ * c₀ * ((k * g)⁻¹)⁻¹ := by
    rw [← hkc]
    group
  rw [hc_eq]
  exact hS7.orbit.conj_mem _ hkg c₀ hc₀

theorem tableVII_mem_orb3A (h : IsF5Type a z) (hPar : ParityFacts a z) (hT5 : TableVFacts a z)
    (hS7 : S7Facts a z) (hT6 : TableVIFacts a z) {c : G} (hc : c ∈ oddSet a a)
    (h3 : orderOf (a * c) = 3) : c ∈ orb3A a a := by
  rcases tableVII_three_cases h hPar hT5 hT6 hc h3 with hne | ⟨t, ht, htc⟩
  · obtain ⟨hca, -⟩ := id hc
    exact ⟨hca, h3, hne⟩
  · exact tableVII_mem_orb3A_of_tSet h hT5 hS7 hT6 ht htc

theorem tableVII_card_3A (hS7 : S7Facts a z) :
    ∀ c ∈ orb3A a a, Nat.card ↥(Gx a ⊓ Gx c) = 5040 := by
  intro c hc
  obtain ⟨e⟩ := hS7.shape c hc
  rw [← Gxy_eq_inf, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  rfl

end CFSG.EvenSporadicStandard.HNRecog.Section3
