module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.Layer

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Reduction

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.HSStd.InvCent
open CFSG.EvenSporadicStandard.SolomonRed

theorem layer_equiv_of_central {Y B : Type} [Group Y] [Finite Y] [Group B] {B₀ : Subgroup B}
    (hR : RHyp B B₀) {t : Y} (ht : orderOf t = 2) (htc : t ∈ Subgroup.center Y)
    (ζ : ↥(centralizer ({t} : Set Y)) ≃* Multiplicative (ZMod 2) × B) :
    Nonempty (egaLayer Y ≃* ↥B₀) := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hnormal : (B₀.map (embA ζ)).Normal := by
    refine ⟨fun b hb d => ?_⟩
    exact conj_mem_map_embA ζ hR.normal
      (Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 htc d)) hb
  have hsimple : IsSimpleGroup ↥(B₀.map (embA ζ)) := by
    haveI := hR.simple
    exact (Subgroup.equivMapOfInjective B₀ (embA ζ) (embA_injective ζ)).symm.isSimpleGroup
  have hnab : ∃ a ∈ B₀.map (embA ζ), ∃ b ∈ B₀.map (embA ζ), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hR.nonab
    refine ⟨embA ζ a, ⟨a, ha, rfl⟩, embA ζ b, ⟨b, hb, rfl⟩, ?_⟩
    intro h
    exact hab (embA_injective ζ (by rw [map_mul, map_mul]; exact h))
  have hC : ∀ x ∈ centralizer ((B₀.map (embA ζ)) : Set Y),
      ∀ y ∈ centralizer ((B₀.map (embA ζ)) : Set Y), x * y = y * x := by
    intro x hx y hy
    have hxt : x ∈ centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 htc x)
    have hx1 : (ζ ⟨x, hxt⟩).2 = 1 := by
      refine RHyp.eq_one_of_commute hR fun a ha => ?_
      have h1 : x * embA ζ a = embA ζ a * x :=
        (Subgroup.mem_centralizer_iff.1 hx (embA ζ a) ⟨a, ha, rfl⟩).symm
      have h2 : embA ζ ((ζ ⟨x, hxt⟩).2 * a * (ζ ⟨x, hxt⟩).2⁻¹) = embA ζ a := by
        rw [← conj_embA ζ ⟨x, hxt⟩ a, h1]
        group
      have h3 := embA_injective ζ h2
      calc (ζ ⟨x, hxt⟩).2 * a
          = ((ζ ⟨x, hxt⟩).2 * a * (ζ ⟨x, hxt⟩).2⁻¹) * (ζ ⟨x, hxt⟩).2 := by group
        _ = a * (ζ ⟨x, hxt⟩).2 := by rw [h3]
    have hx' : x ∈ zpowers t := mem_zpowers_of_snd_eq_one ht1 hR.center ζ hxt hx1
    have hyt : y ∈ centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 htc y)
    have hy1 : (ζ ⟨y, hyt⟩).2 = 1 := by
      refine RHyp.eq_one_of_commute hR fun a ha => ?_
      have h1 : y * embA ζ a = embA ζ a * y :=
        (Subgroup.mem_centralizer_iff.1 hy (embA ζ a) ⟨a, ha, rfl⟩).symm
      have h2 : embA ζ ((ζ ⟨y, hyt⟩).2 * a * (ζ ⟨y, hyt⟩).2⁻¹) = embA ζ a := by
        rw [← conj_embA ζ ⟨y, hyt⟩ a, h1]
        group
      have h3 := embA_injective ζ h2
      calc (ζ ⟨y, hyt⟩).2 * a
          = ((ζ ⟨y, hyt⟩).2 * a * (ζ ⟨y, hyt⟩).2⁻¹) * (ζ ⟨y, hyt⟩).2 := by group
        _ = a * (ζ ⟨y, hyt⟩).2 := by rw [h3]
    have hy' : y ∈ zpowers t := mem_zpowers_of_snd_eq_one ht1 hR.center ζ hyt hy1
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact Commute.zpow_zpow_self t m n
  have h : egaLayer Y = B₀.map (embA ζ) := by
    haveI := hnormal
    exact egaLayer_eq_of_simple_normal (B₀.map (embA ζ)) hsimple hnab hC
  exact ⟨(MulEquiv.subgroupCongr h).trans
    (Subgroup.equivMapOfInjective B₀ (embA ζ) (embA_injective ζ)).symm⟩

theorem layer_cases {Y B : Type} [Group Y] [Finite Y] [Group B] {B₀ : Subgroup B}
    (hR : RHyp B B₀) (hO : fusionOddCore Y = ⊥) {t : Y} (ht : orderOf t = 2)
    (ζ : ↥(centralizer ({t} : Set Y)) ≃* Multiplicative (ZMod 2) × B) :
    Nonempty (egaLayer Y ≃* ↥B₀) ∨ Nonempty (egaLayer Y ≃* ↥B₀ × ↥B₀) ∨
      ∃ S : Subgroup Y, S.Normal ∧ IsSimpleGroup ↥S ∧ centralizer (S : Set Y) = ⊥ ∧
        egaLayer Y = S := by
  rcases lemmaR hR hO ht ζ with htc | ⟨hS, hswap | ⟨S, hF, -⟩⟩
  · exact Or.inl (layer_equiv_of_central hR ht htc ζ)
  · obtain ⟨S₁, S₂, hs⟩ := hswap
    obtain ⟨φ⟩ := swapData_layer_equiv hS hs
    let ψ : ↥S₁ ≃* ↥B₀ := hs.iso.some.trans
      (Subgroup.equivMapOfInjective B₀ (embA ζ) (embA_injective ζ)).symm
    exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr (egaLayer_eq_layer Y)).trans
      (φ.trans (MulEquiv.prodCongr ψ ψ))⟩)
  · haveI := hF.normal
    refine Or.inr (Or.inr ⟨S, hF.normal, hF.simple, hF.cent, ?_⟩)
    refine egaLayer_eq_of_simple_normal S hF.simple hF.nonab fun x hx y hy => ?_
    rw [hF.cent, Subgroup.mem_bot] at hx hy
    simp [hx, hy]

end CFSG.EvenSporadicStandard.M24Std.KForm.Reduction
