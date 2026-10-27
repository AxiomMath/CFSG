module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Hyp
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.SolomonRed

variable {G B : Type*} [Group G] [Group B] {B₀ : Subgroup B}

theorem conj_mem_map_embA {t : G}
    (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B) (hB₀ : B₀.Normal)
    {d : G} (hd : d ∈ centralizer ({t} : Set G)) {b : G} (hb : b ∈ B₀.map (embA ζ)) :
    d * b * d⁻¹ ∈ B₀.map (embA ζ) := by
  rcases hb with ⟨a, ha, rfl⟩
  refine ⟨(ζ ⟨d, hd⟩).2 * a * (ζ ⟨d, hd⟩).2⁻¹, hB₀.conj_mem a ha _, ?_⟩
  exact (conj_embA ζ ⟨d, hd⟩ a).symm

theorem setting_of_RHyp (hR : RHyp B B₀) (hO : fusionOddCore G = ⊥) {t : G}
    (ht : orderOf t = 2) (ζ : ↥(centralizer ({t} : Set G)) ≃* Multiplicative (ZMod 2) × B)
    (htc : t ∉ Subgroup.center G) : Setting G t (B₀.map (embA ζ)) := by
  have htsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, sq] at h
    exact h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  refine ⟨htsq, ht1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro b ⟨a, ha, rfl⟩
    exact embA_mem_cent ζ a
  · intro d hd b hb
    exact conj_mem_map_embA ζ hR.normal hd hb
  · haveI := hR.simple
    exact (Subgroup.equivMapOfInjective B₀ (embA ζ) (embA_injective ζ)).symm.isSimpleGroup
  · obtain ⟨a, ha, b, hb, hab⟩ := hR.nonab
    refine ⟨embA ζ a, ⟨a, ha, rfl⟩, embA ζ b, ⟨b, hb, rfl⟩, ?_⟩
    intro h
    exact hab (embA_injective ζ (by rw [map_mul, map_mul]; exact h))
  · intro d hd hcomm
    have hd1 : (ζ ⟨d, hd⟩).2 = 1 := by
      refine RHyp.eq_one_of_commute hR fun a ha => ?_
      have h1 : d * embA ζ a = embA ζ a * d := hcomm _ ⟨a, ha, rfl⟩
      have h2 : embA ζ ((ζ ⟨d, hd⟩).2 * a * (ζ ⟨d, hd⟩).2⁻¹) = embA ζ a := by
        rw [← conj_embA ζ ⟨d, hd⟩ a, h1]
        group
      have h3 := embA_injective ζ h2
      calc (ζ ⟨d, hd⟩).2 * a
          = ((ζ ⟨d, hd⟩).2 * a * (ζ ⟨d, hd⟩).2⁻¹) * (ζ ⟨d, hd⟩).2 := by group
        _ = a * (ζ ⟨d, hd⟩).2 := by rw [h3]
    exact mem_zpowers_of_snd_eq_one ht1 hR.center ζ hd hd1
  · intro N hN hodd
    have h1 : N ≤ fusionOddCore G := le_sSup ⟨hN, hodd⟩
    rw [hO] at h1
    exact le_bot_iff.1 h1
  · intro x hx
    have hxmem : x ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 (hx t).symm
    have hc : ∀ y ∈ centralizer ({t} : Set G), y * x = x * y := fun y _ => hx y
    have h2 : (ζ ⟨x, hxmem⟩).2 = 1 := snd_eq_one_of_central hR.center ζ hxmem hc
    have h3 : x ∈ zpowers t := mem_zpowers_of_snd_eq_one ht1 hR.center ζ hxmem h2
    rcases (mem_zpowers_iff_of_mul_self_eq_one htsq).1 h3 with h1 | h1
    · exact h1
    · exfalso
      apply htc
      rw [Subgroup.mem_center_iff]
      intro y
      simpa [h1] using hx y

end CFSG.EvenSporadicStandard.HSStd.InvCent
