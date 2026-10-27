module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.LemmaRMod
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.Cases

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.HSStd.InvCent
open CFSG.EvenSporadicStandard.SolomonRed

theorem ModSwapData.layer_equiv {Y B : Type} [Group Y] [Finite Y] [Group B] {B₀ : Subgroup B}
    {t : Y} {S₁ S₂ : Subgroup Y} (hs : ModSwapData Y t B₀ S₁ S₂) :
    Nonempty (↥(CFSG.layer Y) ≃* ↥B₀ × ↥B₀) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sup_prod hs.commute hs.disjoint
  obtain ⟨iso⟩ := hs.iso
  have hconj : Nonempty (↥S₁ ≃* ↥S₂) :=
    ⟨(Subgroup.equivMapOfInjective S₁ (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).trans (MulEquiv.subgroupCongr hs.conj_eq.symm)⟩
  exact ⟨(MulEquiv.subgroupCongr hs.layer_eq).trans
    (e.trans (MulEquiv.prodCongr iso (hconj.some.symm.trans iso)))⟩

theorem layer_cases_mod {Y B : Type} [Group Y] [Finite Y] [Group B] {B₀ : Subgroup B}
    (hR : RHyp B B₀) (hO : fusionOddCore Y = ⊥) {t : Y} (ht : orderOf t = 2)
    (ψ : ↥(centralizer ({t} : Set Y)) →* Multiplicative (ZMod 2) × B)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) :
    Nonempty (egaLayer Y ≃* ↥B₀) ∨ Nonempty (egaLayer Y ≃* ↥B₀ × ↥B₀) ∨
      ∃ S : Subgroup Y, S.Normal ∧ IsSimpleGroup ↥S ∧ centralizer (S : Set Y) = ⊥ ∧
        egaLayer Y = S := by
  have htsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have h : ModData t B₀ ψ := ⟨htsq, ht1, hψ, hodd, hR⟩
  rcases lemmaRMod h hO with htc | ⟨S₁, S₂, hs⟩ | ⟨S, hF, -⟩
  · have hker : ψ.ker = ⊥ := h.ker_eq_bot_of_central hO htc
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
    exact Or.inl (Reduction.layer_equiv_of_central hR ht htc
      (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩))
  · exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr (Reduction.egaLayer_eq_layer Y)).trans
      (ModSwapData.layer_equiv hs).some⟩)
  · haveI : S.Normal := hF.normal
    refine Or.inr (Or.inr ⟨S, hF.normal, hF.simple, hF.cent, ?_⟩)
    refine Reduction.egaLayer_eq_of_simple_normal S hF.simple hF.nonab fun x hx y hy => ?_
    rw [hF.cent, Subgroup.mem_bot] at hx hy
    simp [hx, hy]

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
