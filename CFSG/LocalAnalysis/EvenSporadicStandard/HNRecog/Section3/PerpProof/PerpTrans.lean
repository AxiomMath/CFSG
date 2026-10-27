module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Orb2A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpCover

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem perp_isConjOrbit_of_row (hI : TwoHSInterface) {a z b c : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z)
    (hT4 : TableIVFacts a z) (hb : b ∈ orb2A a a) {i : Fin 6}
    (hrow : ∀ {x : G}, x ∈ orb2A a a ∩ orb2A a c → c ∈ sSet a z x i)
    (hcb : c ∈ sBase a b) :
    IsConjOrbit (Gxy a c) (orb2A a a ∩ orb2A a c) := by
  refine ⟨fun k hk y hy => perp_conj_mem_inter hk hy,
    ⟨b, perp_self_mem_inter h hb hcb⟩, ?_⟩
  intro x hx x' hx'
  have hcx : c ∈ sSet a z x i := hrow hx
  have hcx' : c ∈ sSet a z x' i := hrow hx'
  obtain ⟨k, hkGx, hkx⟩ := exists_conj_of_mem_orb2A hI h hF1 hF2 hx.1 hx'.1
  have hc1 : k * c * k⁻¹ ∈ sSet a z x' i := by
    have h := perp_conj_mem_sSet h hkGx i hcx
    rwa [hkx] at h
  obtain ⟨k', hk'Gxy, hk'⟩ :=
    ((hT4.partition x' hx'.1).orbit i).transitive (k * c * k⁻¹) hc1 c hcx'
  have hk'Gxa : k' ∈ Gx a := (mem_Gxy.mp hk'Gxy).1
  have hk'Gxx' : k' ∈ Gx x' := (mem_Gxy.mp hk'Gxy).2
  have hx'k' : x' * k' = k' * x' := mem_Gx.mp hk'Gxx'
  have hgc : (k' * k) * c * (k' * k)⁻¹ = c := by
    calc (k' * k) * c * (k' * k)⁻¹
        = k' * (k * c * k⁻¹) * k'⁻¹ := by group
      _ = c := hk'
  refine ⟨k' * k, ?_, ?_⟩
  · refine mem_Gxy.mpr ⟨Subgroup.mul_mem _ hk'Gxa hkGx, mem_Gx.mpr ?_⟩
    exact (mul_inv_eq_iff_eq_mul.mp hgc).symm
  · calc (k' * k) * x * (k' * k)⁻¹
        = k' * (k * x * k⁻¹) * k'⁻¹ := by group
      _ = k' * x' * k'⁻¹ := by rw [hkx]
      _ = x' := by rw [← hx'k']; group

theorem perp_isConjOrbit (hI : TwoHSInterface) {a z b c : G} (h : IsF5Type a z)
    (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) (hT4 : TableIVFacts a z)
    (hb : b ∈ orb2A a a) {i : Fin 6} (hi : i = 3 ∨ i = 4) (hc : c ∈ sSet a z b i) :
    IsConjOrbit (Gxy a c) (orb2A a a ∩ orb2A a c) := by
  rcases hi with rfl | rfl
  · have hcb : c ∈ sBase a b := by
      have hc' : c ∈ sBase a b ∧ IsConj z ((a * c) ^ 2) := hc
      exact hc'.1
    exact perp_isConjOrbit_of_row hI h hF1 hF2 hT4 hb (i := 3)
      (fun hx => perp_mem_sSet_three hI h hT4 hc hx) hcb
  · have hcb : c ∈ sBase a b := by
      have hc' : c ∈ sBase a b ∧ orderOf (a * c) = 3 := hc
      exact hc'.1
    exact perp_isConjOrbit_of_row hI h hF1 hF2 hT4 hb (i := 4)
      (fun hx => perp_mem_sSet_four hI h hT4 hc hx) hcb

end CFSG.EvenSporadicStandard.HNRecog.Section3
