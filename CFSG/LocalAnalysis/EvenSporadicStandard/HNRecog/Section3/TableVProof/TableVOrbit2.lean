module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Orb2A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVSets
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVTrans

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableV_orbit_2A (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) : IsConjOrbit (Gx a) (orb2A a a) := by
  obtain ⟨z₀, b₀, u₀, hF, hz₀, _⟩ := hF1.rep_z
  obtain ⟨⟨hb₀A, hab₀A, -, -⟩, _⟩ := hF2.reps_bu z₀ b₀ u₀ hF hz₀
  exact ⟨fun k hk c hc => perp_conj_mem_orb2A hk hc,
    ⟨(b₀ : G), hb₀A, hab₀A⟩,
    fun c hc c' hc' => exists_conj_of_mem_orb2A hI h hF1 hF2 hc hc'⟩

theorem tableV_orbit_2B (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) : IsConjOrbit (Gx a) (orb2B a z a) := by
  obtain ⟨z₀, b₀, u₀, hF, hz₀, haz₀, -, -, -, -⟩ := hF1.rep_z
  have ha2 : a * a = 1 := by
    have hpow : a ^ orderOf a = 1 := pow_orderOf_eq_one a
    rw [h.orderOf_a] at hpow
    simpa [pow_two] using hpow
  have haz : a * (a * (z₀ : G)) = (z₀ : G) := by rw [← mul_assoc, ha2, one_mul]
  refine ⟨fun k hk c hc => ?_, ⟨a * (z₀ : G), haz₀, by rw [haz]; exact hz₀⟩,
    fun c hc c' hc' => tableV_exists_conj_orb2B hI h hF1 hF2 hc hc'⟩
  simpa [tab5Set] using tableV_conj_mem (z := z) hk 1 hc

end CFSG.EvenSporadicStandard.HNRecog.Section3
