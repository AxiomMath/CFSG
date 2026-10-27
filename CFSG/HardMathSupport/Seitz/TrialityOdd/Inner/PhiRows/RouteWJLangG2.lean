module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.D4G2All
public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartTwo.KFacts

set_option linter.unusedSectionVars false

section LangG2

variable {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [IsAlgClosed L] [CharP L ℓ]

theorem exists_lang_g2_D4 (hf : 1 ≤ f)
    (n₂ : ModGL TwistTag.D4.tag L) (hn₂ : n₂ ∈ adjointGroup TwistTag.D4.tag L)
    (hn₂P : diagramMap TwistTag.D4 L * n₂ = n₂ * diagramMap TwistTag.D4 L) :
    ∃ g₂ ∈ adjointGroup TwistTag.D4.tag L,
      diagramMap TwistTag.D4 L * g₂ = g₂ * diagramMap TwistTag.D4 L ∧
        twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g₂ = g₂ * n₂ := by
  classical
  have hK3 : (3 : ℕ∞) ≤ ENat.card L := by
    rw [ENat.card_eq_top_of_infinite]
    exact le_top
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFr
  let e := d4FixedG2EquivAll L hK3
  have hnΓ : n₂ ∈ twistedFixedGroup TwistTag.D4 L (RingHom.id L) :=
    d4_mem_twistedFixedGroup_id_iff.2 ⟨hn₂, hn₂P⟩
  obtain ⟨S, hS, hLang⟩ := (exceptional_all_characteristic_field_Lang_surjectivity ℓ L f hf).1
    Tag.G2
  obtain ⟨h, hh⟩ := hLang (e ⟨n₂, hnΓ⟩)
  set g : twistedFixedGroup TwistTag.D4 L (RingHom.id L) := e.symm h with hgdef
  have hg' : baseChangeGL Fr (g : ModGL TwistTag.D4.tag L) ∈
      twistedFixedGroup TwistTag.D4 L (RingHom.id L) :=
    d4_baseChangeGL_mem_twistedFixedGroup Fr g.2
  have key : (⟨baseChangeGL Fr (g : ModGL TwistTag.D4.tag L), hg'⟩ :
      twistedFixedGroup TwistTag.D4 L (RingHom.id L)) = g * ⟨n₂, hnΓ⟩ := by
    apply e.injective
    rw [map_mul]
    have h1 : e g = h := e.apply_symm_apply h
    rw [h1]
    refine Subtype.ext ?_
    change d4FixedToG2 L ⟨baseChangeGL Fr (g : ModGL TwistTag.D4.tag L), hg'⟩ = _
    rw [d4FixedToG2_baseChangeGL Fr g]
    have h2 : (d4FixedToG2 L g) = (h : ModGL Tag.G2 L) := by
      have := congrArg Subtype.val h1
      exact this
    rw [h2, hh, mul_inv_cancel_left]
    exact (hS h).symm
  have key' : baseChangeGL Fr (g : ModGL TwistTag.D4.tag L) = (g : ModGL TwistTag.D4.tag L) * n₂ :=
    congrArg Subtype.val key
  have hgC : (g : ModGL TwistTag.D4.tag L) ∈ adjointGroup TwistTag.D4.tag L := g.2.1
  have hgP := d4_diagramMap_mul_of_mem_twistedFixedGroup g.2
  refine ⟨(g : ModGL TwistTag.D4.tag L), hgC, hgP, ?_⟩
  rw [twistHom_apply]
  change diagramMap TwistTag.D4 L * baseChangeGL Fr (g : ModGL TwistTag.D4.tag L) *
    (diagramMap TwistTag.D4 L)⁻¹ = _
  rw [key']
  calc diagramMap TwistTag.D4 L * ((g : ModGL TwistTag.D4.tag L) * n₂) *
        (diagramMap TwistTag.D4 L)⁻¹
      = (diagramMap TwistTag.D4 L * (g : ModGL TwistTag.D4.tag L)) * n₂ *
          (diagramMap TwistTag.D4 L)⁻¹ := by group
    _ = (g : ModGL TwistTag.D4.tag L) * (diagramMap TwistTag.D4 L * n₂) *
          (diagramMap TwistTag.D4 L)⁻¹ := by rw [hgP]; group
    _ = (g : ModGL TwistTag.D4.tag L) * (n₂ * diagramMap TwistTag.D4 L) *
          (diagramMap TwistTag.D4 L)⁻¹ := by rw [hn₂P]
    _ = (g : ModGL TwistTag.D4.tag L) * n₂ := by group

end LangG2

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
