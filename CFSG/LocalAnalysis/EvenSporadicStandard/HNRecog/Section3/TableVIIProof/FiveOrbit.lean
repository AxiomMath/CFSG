module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.FiveRows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.OrbConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem tableVII_fiveOrbit_conj_a {g : G} (hg : g ∈ Gx a) : g * a * g⁻¹ = a := by
  rw [← mem_Gx.1 hg]
  group

private theorem tableVII_fiveOrbit_mem_Gx {g x : G} (hg : g * x * g⁻¹ = x) : g ∈ Gx x :=
  mem_Gx.2 (mul_inv_eq_iff_eq_mul.1 hg).symm

private theorem tableVII_fiveOrbit_conj_mem_Gxy {g c t : G} (hg : g ∈ Gx a) (ht : t ∈ Gxy a c) :
    g * t * g⁻¹ ∈ Gxy a (g * c * g⁻¹) := by
  obtain ⟨hta, htc⟩ := mem_Gxy.1 ht
  refine mem_Gxy.2 ⟨mul_mem (mul_mem hg hta) (inv_mem hg), mem_Gx.2 ?_⟩
  rw [show g * c * g⁻¹ * (g * t * g⁻¹) = g * (c * t) * g⁻¹ by group, mem_Gx.1 htc]
  group

private theorem tableVII_fiveOrbit_conj_5A {g c : G} (hg : g ∈ Gx a) (hc : c ∈ orb5A a a) :
    g * c * g⁻¹ ∈ orb5A a a := by
  have h := (AutGamma.conj_mem_orb5A (a := a) g (x := a) (c := c)).2 hc
  rwa [tableVII_fiveOrbit_conj_a hg] at h

private theorem tableVII_fiveOrbit_conj_5E {g c : G} (hg : g ∈ Gx a) (hc : c ∈ orb5E a a) :
    g * c * g⁻¹ ∈ orb5E a a := by
  have h := (AutGamma.conj_mem_orb5E (a := a) g (x := a) (c := c)).2 hc
  rwa [tableVII_fiveOrbit_conj_a hg] at h

private theorem tableVII_fiveOrbit_odd (h : IsF5Type a z) {b c : G} (hb : b ∈ orb2B a z a)
    (hc : c ∈ tBase a z b) (h5 : orderOf (a * c) = 5) : c ∈ oddSet a a ∧ b ∈ Gxy a c := by
  obtain ⟨hca, hbc, hcne⟩ := hc
  have hcb : IsConj z (c * b) := hbc.trans (isConj_iff.2 ⟨c, by group⟩)
  have hbac : b ∈ Gxy a c := mem_Gxy.2 ⟨tableVII_mem_Gx_of_orb2B h (IsConj.refl a) hb,
    tableVII_mem_Gx_of_orb2B h hca ⟨hb.1, hcb⟩⟩
  exact ⟨⟨hca, hcne, by rw [h5]; exact ⟨2, rfl⟩, b, hb.1, hbac⟩, hbac⟩

theorem tableVII_orbit_5A (h : IsF5Type a z) (hPar : ParityFacts a z) (hT4 : TableIVFacts a z)
    (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) : IsConjOrbit (Gx a) (orb5A a a) := by
  refine ⟨fun g hg c hc => tableVII_fiveOrbit_conj_5A hg hc, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hT5.partition.orbit 1).nonempty
    have hb' : b ∈ orb2B a z a := hb
    obtain ⟨c, hc⟩ := ((hT6.partition b hb').orbit 5).nonempty
    have hc' : c ∈ tBase a z b ∧ orderOf (a * c) = 5 ∧
        IsShapeCentralizerFiveC ↥(Gxy b (a * c)) := hc
    obtain ⟨hodd, hbc⟩ := tableVII_fiveOrbit_odd h hb' hc'.1 hc'.2.1
    refine ⟨c, ?_⟩
    rcases tableVII_mem_orb5A_or_orb5E h hPar hT4 hT5 hT6 hodd hc'.2.1 with hA | hE
    · exact hA
    · have h6 := (tableVII_row6_of_orb5E h hPar hT4 hT5 hT6 hE hb'.1 hbc).2
      exact absurd h6 (Set.disjoint_left.1 ((hT6.partition b hb').disjoint 5 6 (by decide)) hc)
  · intro c hc c' hc'
    obtain ⟨t, ht, htc⟩ := hc.1.2.2.2
    obtain ⟨t', ht', ht'c'⟩ := hc'.1.2.2.2
    obtain ⟨htB, -⟩ := tableVII_row5_of_orb5A h hPar hT4 hT5 hT6 hc ht htc
    obtain ⟨ht'B, hc'5⟩ := tableVII_row5_of_orb5A h hPar hT4 hT5 hT6 hc' ht' ht'c'
    obtain ⟨g, hg, hgt⟩ := (hT5.partition.orbit 1).transitive t htB t' ht'B
    have hgc := tableVII_fiveOrbit_conj_5A hg hc
    have ht'gc : t' ∈ Gxy a (g * c * g⁻¹) := by
      rw [← hgt]
      exact tableVII_fiveOrbit_conj_mem_Gxy hg htc
    have hgc5 := (tableVII_row5_of_orb5A h hPar hT4 hT5 hT6 hgc ht' ht'gc).2
    obtain ⟨k, hk, hkc⟩ := ((hT6.partition t' ht'B).orbit 5).transitive _ hgc5 c' hc'5
    exact ⟨k * g, mul_mem (mem_Gxy.1 hk).1 hg,
      (by group : k * g * c * (k * g)⁻¹ = k * (g * c * g⁻¹) * k⁻¹).trans hkc⟩

theorem tableVII_orbit_5E (h : IsF5Type a z) (hPar : ParityFacts a z) (hT4 : TableIVFacts a z)
    (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) : IsConjOrbit (Gx a) (orb5E a a) := by
  refine ⟨fun g hg c hc => tableVII_fiveOrbit_conj_5E hg hc, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hT5.partition.orbit 1).nonempty
    have hb' : b ∈ orb2B a z a := hb
    obtain ⟨c, hc⟩ := ((hT6.partition b hb').orbit 6).nonempty
    have hc' : c ∈ tBase a z b ∧ orderOf (a * c) = 5 ∧
        IsShapeCentralizerFiveB ↥(Gxy b (a * c)) := hc
    obtain ⟨hodd, hbc⟩ := tableVII_fiveOrbit_odd h hb' hc'.1 hc'.2.1
    refine ⟨c, ?_⟩
    rcases tableVII_mem_orb5A_or_orb5E h hPar hT4 hT5 hT6 hodd hc'.2.1 with hA | hE
    · have h5 := (tableVII_row5_of_orb5A h hPar hT4 hT5 hT6 hA hb'.1 hbc).2
      exact absurd hc (Set.disjoint_left.1 ((hT6.partition b hb').disjoint 5 6 (by decide)) h5)
    · exact hE
  · intro c hc c' hc'
    obtain ⟨t, ht, htc⟩ := hc.1.2.2.2
    obtain ⟨t', ht', ht'c'⟩ := hc'.1.2.2.2
    obtain ⟨htB, -⟩ := tableVII_row6_of_orb5E h hPar hT4 hT5 hT6 hc ht htc
    obtain ⟨ht'B, hc'6⟩ := tableVII_row6_of_orb5E h hPar hT4 hT5 hT6 hc' ht' ht'c'
    obtain ⟨g, hg, hgt⟩ := (hT5.partition.orbit 1).transitive t htB t' ht'B
    have hgc := tableVII_fiveOrbit_conj_5E hg hc
    have ht'gc : t' ∈ Gxy a (g * c * g⁻¹) := by
      rw [← hgt]
      exact tableVII_fiveOrbit_conj_mem_Gxy hg htc
    have hgc6 := (tableVII_row6_of_orb5E h hPar hT4 hT5 hT6 hgc ht' ht'gc).2
    obtain ⟨k, hk, hkc⟩ := ((hT6.partition t' ht'B).orbit 6).transitive _ hgc6 c' hc'6
    exact ⟨k * g, mul_mem (mem_Gxy.1 hk).1 hg,
      (by group : k * g * c * (k * g)⁻¹ = k * (g * c * g⁻¹) * k⁻¹).trans hkc⟩

theorem tableVII_conj_in_Gxy (h : IsF5Type a z) (hPar : ParityFacts a z)
    (hT4 : TableIVFacts a z) (hT5 : TableVFacts a z) (hT6 : TableVIFacts a z) {c t t₁ : G}
    (hc : c ∈ orb5A a a) (ht : IsConj a t) (htc : t ∈ Gxy a c) (ht₁ : IsConj a t₁)
    (ht₁c : t₁ ∈ Gxy a c) : ∃ k ∈ Gxy a c, k * t * k⁻¹ = t₁ := by
  obtain ⟨htB, -⟩ := tableVII_row5_of_orb5A h hPar hT4 hT5 hT6 hc ht htc
  obtain ⟨ht₁B, hc₁⟩ := tableVII_row5_of_orb5A h hPar hT4 hT5 hT6 hc ht₁ ht₁c
  obtain ⟨g, hg, hgt⟩ := (hT5.partition.orbit 1).transitive t htB t₁ ht₁B
  have hgc := tableVII_fiveOrbit_conj_5A hg hc
  have ht₁gc : t₁ ∈ Gxy a (g * c * g⁻¹) := by
    rw [← hgt]
    exact tableVII_fiveOrbit_conj_mem_Gxy hg htc
  have hgc5 := (tableVII_row5_of_orb5A h hPar hT4 hT5 hT6 hgc ht₁ ht₁gc).2
  obtain ⟨k, hk, hkc⟩ := ((hT6.partition t₁ ht₁B).orbit 5).transitive _ hgc5 c hc₁
  obtain ⟨hka, hkt₁⟩ := mem_Gxy.1 hk
  have hkg : k * g * c * (k * g)⁻¹ = c :=
    (by group : k * g * c * (k * g)⁻¹ = k * (g * c * g⁻¹) * k⁻¹).trans hkc
  refine ⟨k * g, mem_Gxy.2 ⟨mul_mem hka hg, tableVII_fiveOrbit_mem_Gx hkg⟩, ?_⟩
  calc k * g * t * (k * g)⁻¹ = k * (g * t * g⁻¹) * k⁻¹ := by group
    _ = k * t₁ * k⁻¹ := by rw [hgt]
    _ = t₁ := by rw [← mem_Gx.1 hkt₁]; group

end CFSG.EvenSporadicStandard.HNRecog.Section3
