module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Orb2A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVSets

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableV_orbit_4B (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) (hT4 : TableIVFacts a z) :
    IsConjOrbit (Gx a) (orb4B a a) := by
  obtain ⟨z₀, b₀, u₀, hF, hz₀, -⟩ := hF1.rep_z
  obtain ⟨⟨hb₀A, hab₀A, -, -⟩, -⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  have hb₀ : (b₀ : G) ∈ orb2A a a := ⟨hb₀A, hab₀A⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk c hc
    exact tableV_conj_mem (z := z) hk 3 hc
  · obtain ⟨c, hc⟩ := ((hT4.partition b₀ hb₀).orbit 2).nonempty
    have hc' : c ∈ sBase a b₀ ∧ (a * c) ^ 2 = b₀ := hc
    obtain ⟨hbase, hp⟩ := hc'
    exact ⟨c, hbase.1, by rw [hp]; exact hb₀A⟩
  · intro c hc c' hc'
    obtain ⟨hb, hcrow⟩ := tableV_orb4B_row h hc
    obtain ⟨hb', hcrow'⟩ := tableV_orb4B_row h hc'
    obtain ⟨k, hkGx, hk⟩ := exists_conj_of_mem_orb2A hI h hF1 hF2 hb' hb
    have hc'1 : k * c' * k⁻¹ ∈ sSet a z ((a * c) ^ 2) 2 := by
      have hmem := perp_conj_mem_sSet h hkGx 2 hcrow'
      rwa [hk] at hmem
    obtain ⟨g, hgGxy, hg⟩ :=
      ((hT4.partition ((a * c) ^ 2) hb).orbit 2).transitive (k * c' * k⁻¹) hc'1 c hcrow
    refine ⟨(g * k)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (mem_Gxy.mp hgGxy).1 hkGx)
    · rw [← hg]
      group

theorem tableV_orbit_6A (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) (hT4 : TableIVFacts a z) :
    IsConjOrbit (Gx a) (orb6A a a) := by
  obtain ⟨z₀, b₀, u₀, hF, hz₀, -⟩ := hF1.rep_z
  obtain ⟨⟨hb₀A, hab₀A, -, -⟩, -⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  have hb₀ : (b₀ : G) ∈ orb2A a a := ⟨hb₀A, hab₀A⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk c hc
    exact tableV_conj_mem (z := z) hk 4 hc
  · obtain ⟨c, hc⟩ := ((hT4.partition b₀ hb₀).orbit 5).nonempty
    have hc' : c ∈ sBase a b₀ ∧ (a * c) ^ 3 = b₀ := hc
    obtain ⟨hbase, hcube⟩ := hc'
    obtain ⟨hord, -⟩ := perp_orderOf_row_five h hb₀A hc
    exact ⟨c, hbase.1, hord, by rw [hcube]; exact hb₀A⟩
  · intro c hc c' hc'
    obtain ⟨hb, hcrow⟩ := tableV_orb6A_row h hc
    obtain ⟨hb', hcrow'⟩ := tableV_orb6A_row h hc'
    obtain ⟨k, hkGx, hk⟩ := exists_conj_of_mem_orb2A hI h hF1 hF2 hb' hb
    have hc'1 : k * c' * k⁻¹ ∈ sSet a z ((a * c) ^ 3) 5 := by
      have hmem := perp_conj_mem_sSet h hkGx 5 hcrow'
      rwa [hk] at hmem
    obtain ⟨g, hgGxy, hg⟩ :=
      ((hT4.partition ((a * c) ^ 3) hb).orbit 5).transitive (k * c' * k⁻¹) hc'1 c hcrow
    refine ⟨(g * k)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (mem_Gxy.mp hgGxy).1 hkGx)
    · rw [← hg]
      group

end CFSG.EvenSporadicStandard.HNRecog.Section3
