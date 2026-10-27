module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutCrit
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MinusStmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldDef
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPolar

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Transport

variable {Y Y₄ : Type} [Group Y] [Group Y₄]

theorem un_fixSub_equiv (φ : MulAut Y) (φ₄ τ : MulAut Y₄) (ψ : Y →* Y₄)
    (hinj : Function.Injective ψ) (hint : ∀ y, ψ (φ y) = φ₄ (ψ y))
    (hfix : ∀ y₄, τ y₄ = y₄ ↔ y₄ ∈ Set.range ψ) :
    ∃ e : ↥(fixSub φ) ≃* ↥(foldFix (φ₄ : Y₄ ≃* Y₄) ⊓ foldFix (τ : Y₄ ≃* Y₄)),
      ∀ y : ↥(fixSub φ), ((e y : ↥(foldFix (φ₄ : Y₄ ≃* Y₄) ⊓ foldFix (τ : Y₄ ≃* Y₄))) : Y₄) =
        ψ (y : Y) := by
  have hmem : ∀ y : ↥(fixSub φ), ψ (y : Y) ∈ foldFix (φ₄ : Y₄ ≃* Y₄) ⊓ foldFix (τ : Y₄ ≃* Y₄) := by
    intro y
    refine Subgroup.mem_inf.2 ⟨mem_foldFix.2 ?_, mem_foldFix.2 ?_⟩
    · rw [← hint, mem_fixSub.1 y.2]
    · exact (hfix _).2 ⟨y, rfl⟩
  let f : ↥(fixSub φ) →* ↥(foldFix (φ₄ : Y₄ ≃* Y₄) ⊓ foldFix (τ : Y₄ ≃* Y₄)) :=
    (ψ.comp (fixSub φ).subtype).codRestrict _ hmem
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩, fun y => rfl⟩
  · intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (hinj this)
  · rintro ⟨z, hz⟩
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨y, rfl⟩ := (hfix z).1 (mem_foldFix.1 hz2)
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [mem_fixSub]
    apply hinj
    rw [hint]
    exact mem_foldFix.1 hz1

end Transport

section Main


theorem d4OuterThreeA2Minus_thm : D4OuterThreeA2Minus := by
  intro p f hp hp2 hp3 hf hq K _ _ hK σ hσ s hs
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  obtain ⟨hNoAbel, U₀, hU₀le, hU₀p, hU₀card⟩ :=
    un_polarity hp2 hf hq hK₄ σ₄ ε hσ₄ hε b hb3 hb1 s₄ hs₄
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  have hA : D4NoAbel (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := fun F₀ hF hc =>
    un_noAbel_of_equiv e.symm hNoAbel F₀ hF (fun a ha b hb =>
      congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩))
  refine ⟨hA, ?_⟩
  refine d4PtKer_of_noAbel_pgroup hp hp2 hf K hK σ hσ _ hA (U₀.comap ψ₄) ?_ ?_ ?_
  · intro y hy
    have h1 := Subgroup.mem_inf.1 (hU₀le hy)
    rw [mem_fixSub]
    apply hinj
    rw [hint]
    exact mem_foldFix.1 h1.1
  · exact hU₀p.of_injective (ψ₄.subgroupComap U₀) (fun a b hab =>
      Subtype.ext (hinj (congrArg Subtype.val hab)))
  · have hbij : Function.Bijective (ψ₄.subgroupComap U₀) := by
      refine ⟨fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab)), ?_⟩
      rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := (hfix z).1 (mem_foldFix.1 (Subgroup.mem_inf.1 (hU₀le hz)).2)
      exact ⟨⟨y, hz⟩, rfl⟩
    rw [Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact hU₀card

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm1
