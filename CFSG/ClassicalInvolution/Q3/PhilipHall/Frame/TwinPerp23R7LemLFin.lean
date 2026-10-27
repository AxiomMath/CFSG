module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLSecV
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLT237
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTrans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTri
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTwin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin

section Fin

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y} {f₁ f₂ : Y}

theorem section_data (hT : Thm4RTwinBelow 3 n) (ctx : LemLCtx n Y R S t K' W u e g Z V f₁ f₂)
    (hL : SecCoresTwoGroup (Om R) V) (hY1 : ModS3O ↥(rLayer (Om R) e)) :
    Nat.card (SecQuot (rLayerSub (Om R) V)) < n ∧
      Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V) ∧
      ∃ Kb Kb' : Subgroup (SecQuot (rLayerSub (Om R) V)), Kb ∈ p23SecFamV R V ∧
        Kb' ∈ twinSet (p23SecFamV R V) Kb ∧ Kb' ≠ Kb ∧
        (∀ J ∈ p23SecFamV R V, J ≠ Kb →
          J ≤ Subgroup.normalizer (Kb : Set (SecQuot (rLayerSub (Om R) V))) → J = Kb') ∧
        ∃ a : SecQuot (rLayerSub (Om R) V), a * a = 1 ∧ HasS3Quot ↥(Ea (p23SecFamV R V) a) := by
  obtain ⟨hc, hno, hE, hZ, hZd, hVZ, hV1, hf₁, hf₂, hne, h₁, h₂⟩ := ctx
  obtain ⟨hfX, ha⟩ := p23_type237 hc hZd hVZ hY1 hf₁ h₁
  have hlt := card_secQuot_lt hc hV1
  obtain ⟨P₀, P₀', hP₀, hP₀', hP₀C, hP₀'C, hKb, hKb', hne', ⟨zb, hzb, hzb'⟩, hperp, hperp'⟩ :=
    p23_twin_pair hc hZd hVZ hL
  have F : Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V) :=
    { hyp := p23SecFamV_hypOmegaGen hc hZd hVZ hL
      two := p23SecFamV_isPGroup hL
      q8 := p23SecFamV_q8 hc hL
      aEmpty := p23SecFamV_aEmpty hc hZd hVZ hL
      gen := p23SecFamV_pSpan R V
      trans := trans_of_twin hT hlt (p23SecFamV_hypOmegaGen hc hZd hVZ hL)
        (p23SecFamV_isPGroup hL) (p23SecFamV_q8 hc hL) (p23SecFamV_aEmpty hc hZd hVZ hL)
        (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V)) hKb
        ⟨hKb', zb, hzb, hzb'⟩ hne' hperp hperp' ha
      oddFree := CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V) }
  refine ⟨hlt, F, _, _, hKb, ⟨hKb', zb, hzb, hzb'⟩, hne', hperp, _, ?_, ha⟩
  have hf2 : f₁ * f₁ = 1 := hZd.sq f₁ (hZd.orb_le hf₁)
  have h1 : (⟨f₁, hfX⟩ : ↥(rLayerSub (Om R) V)) * ⟨f₁, hfX⟩ = 1 := Subtype.ext hf2
  rw [← map_mul, h1, map_one]

end Fin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
