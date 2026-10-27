module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpOrb4A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVSets
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVTrans

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableV_orb4A_mem_orb2AB {a z c : G} (h : IsF5Type a z) (hc : c ∈ orb4A a z a) :
    (a * c) ^ 2 ∈ orb2AB a z a := by
  obtain ⟨hcA, hcz⟩ := hc
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hc2 : c ^ 2 = 1 := by
    have hco : orderOf c = 2 := perp_orderOf_of_isConj_a h hcA
    rw [← hco]
    exact pow_orderOf_eq_one c
  have hcc : c * c = 1 := by simpa [pow_two] using hc2
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  refine ⟨hcz, ?_⟩
  have hkey : a * (a * c) ^ 2 = c * a * c := by
    calc a * (a * c) ^ 2 = a * ((a * c) * (a * c)) := by rw [pow_two]
      _ = (a * (a * c)) * (a * c) := (mul_assoc _ _ _).symm
      _ = ((a * a) * c) * (a * c) := by rw [← mul_assoc a a c]
      _ = (1 * c) * (a * c) := by rw [haa]
      _ = c * (a * c) := by rw [one_mul]
      _ = c * a * c := (mul_assoc c a c).symm
  rw [hkey]
  have hconj : IsConj a (c * a * c⁻¹) := isConj_iff.mpr ⟨c, rfl⟩
  rwa [hc_inv] at hconj

theorem tableV_mem_tab3Set (hI : TwoHSInterface) {a z c : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hc : c ∈ orb4A a z a) :
    c ∈ tab3Set a ((a * c) ^ 2) a 2 := by
  have hcA : IsConj a c := hc.1
  have hcz : IsConj z ((a * c) ^ 2) := hc.2
  obtain ⟨_, hQc⟩ := perp_mem_Qz_of_orb4A hI h hF1 hc
  have hz2 : orderOf ((a * c) ^ 2) = 2 := perp_orderOf_of_isConj_z h hcz
  have hzsq : ((a * c) ^ 2) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one ((a * c) ^ 2)
    rw [hz2] at h
    exact h
  have hz_ne : (a * c) ^ 2 ≠ 1 := by
    intro h1
    have : orderOf ((a * c) ^ 2) = 1 := by rw [h1, orderOf_one]
    omega
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hcne_a : c ≠ a := by
    intro hca
    apply hz_ne
    rw [hca, haa]
    simp
  have hcne_at : c ≠ a * (a * c) ^ 2 := by
    intro hca'
    apply hz_ne
    set t : G := (a * c) ^ 2 with ht
    have h1 : a * c = t := by
      rw [hca', ← mul_assoc, haa, one_mul]
    have ht2 : t ^ 2 = 1 := by rw [ht]; exact hzsq
    calc t = (a * c) ^ 2 := ht
      _ = (a * c) * (a * c) := pow_two _
      _ = t * t := by rw [h1]
      _ = t ^ 2 := (pow_two t).symm
      _ = 1 := ht2
  show c ∈ tab3Base a ((a * c) ^ 2) a ∧ (a * c) ^ 2 = (a * c) ^ 2
  exact ⟨⟨hQc, hcA, hcne_a, hcne_at⟩, rfl⟩

theorem tableV_orbit_4A (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hT3 : Vert TableIIIFacts a z) :
    IsConjOrbit (Gx a) (orb4A a z a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk c hc
    exact tableV_conj_mem (i := 2) hk hc
  · obtain ⟨z₀, b₀, u₀, hF, hz₀, -, -, haQ, -, -⟩ := hF1.self.rep_z
    have hT3' : TableIIIFacts a z₀ := hT3 a z₀ (IsConj.refl a) hz₀
    obtain ⟨c, hc⟩ := ((hT3'.partition a haQ (IsConj.refl a)).orbit 2).nonempty
    exact ⟨c, hc.1.2.1, by rw [hc.2]; exact hz₀⟩
  · intro c hc c' hc'
    have ht : (a * c) ^ 2 ∈ orb2AB a z a := tableV_orb4A_mem_orb2AB h hc
    have ht' : (a * c') ^ 2 ∈ orb2AB a z a := tableV_orb4A_mem_orb2AB h hc'
    obtain ⟨k, hk, hkt⟩ := tableV_exists_conj_orb2AB hI h hF1.self hF2.self ht ht'
    have hkA : a * k = k * a := mem_Gx.mp hk
    have hc1 : k * c * k⁻¹ ∈ orb4A a z a := tableV_conj_mem (i := 2) hk hc
    have hsq : (a * (k * c * k⁻¹)) ^ 2 = (a * c') ^ 2 := by
      have hstep : a * (k * c * k⁻¹) = k * (a * c) * k⁻¹ := by
        rw [show a * (k * c * k⁻¹) = (a * k) * c * k⁻¹ from by group, hkA]
        group
      calc (a * (k * c * k⁻¹)) ^ 2 = (k * (a * c) * k⁻¹) ^ 2 := by rw [hstep]
        _ = k * (a * c) ^ 2 * k⁻¹ := by rw [pow_two, pow_two]; group
        _ = (a * c') ^ 2 := hkt
    have hcT : c' ∈ tab3Set a ((a * c') ^ 2) a 2 := tableV_mem_tab3Set hI h hF1 hc'
    have hc1_3 : k * c * k⁻¹ ∈ tab3Set a ((a * (k * c * k⁻¹)) ^ 2) a 2 :=
      tableV_mem_tab3Set hI h hF1 hc1
    rw [hsq] at hc1_3
    obtain ⟨hat', -⟩ := perp_mem_Qz_of_orb4A hI h hF1 hc'
    have hpart := (hT3 a ((a * c') ^ 2) (IsConj.refl a) ht'.1).partition a hat' (IsConj.refl a)
    obtain ⟨g, hg, hgck⟩ := (hpart.orbit 2).transitive (k * c * k⁻¹) hc1_3 c' hcT
    refine ⟨g * k, (Gx a).mul_mem (mem_Gxy.mp hg).1 hk, ?_⟩
    calc (g * k) * c * (g * k)⁻¹ = g * (k * c * k⁻¹) * g⁻¹ := by group
      _ = c' := hgck

end CFSG.EvenSporadicStandard.HNRecog.Section3
