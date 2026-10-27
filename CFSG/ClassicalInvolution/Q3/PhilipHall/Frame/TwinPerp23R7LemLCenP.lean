module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLT237
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLSecV

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin

section CenGen

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem hasS3Quot_e64_of (hgen : pSpan Φ = ⊤) (hO : classicalInvolutionOddCore G = ⊥)
    (I : AEIdentOn Φ 7 AE.e64Sets AE.e64Sub) (h : HasS3Quot G) : HasS3Quot ↥AE.e64Sub := by
  let ρ0 : G →* AE.AEQ 7 := I.φ.comp (toPSpan hgen)
  have hρ0 : ∀ x, ρ0 x ∈ AE.e64Sub := fun x => I.range_eq ▸ ⟨toPSpan hgen x, rfl⟩
  let ρ : G →* ↥AE.e64Sub := ρ0.codRestrict _ hρ0
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    rw [← I.range_eq] at hy
    obtain ⟨p, rfl⟩ := hy
    refine ⟨(p : G), Subtype.ext ?_⟩
    show I.φ (toPSpan hgen (p : G)) = I.φ p
    have : toPSpan hgen (p : G) = p := Subtype.ext rfl
    rw [this]
  have h2 : ∀ x ∈ ρ.ker, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x hx
    have hx1 : ρ0 x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxc : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : (toPSpan hgen x : ↥(pSpan Φ)) ∈ I.φ.ker := hx1
      have h2 := Subgroup.mem_center_iff.mp (I.ker_le h1) (toPSpan hgen y)
      exact congrArg Subtype.val h2
    exact center_pow_two hO hxc
  exact HasS3Quot.of_surjective ρ hρs h2 h

end CenGen


section CenP

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem p23_central (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) (hVZ : V ≤ Z)
    (hY1 : ModS3O ↥(rLayer (Om R) e)) (hY3 : OmegaOneCenter (rLayer (Om R) e) e)
    (hno : ¬ HasS3Quot ↥AE.e64Sub)
    (I : AEIdentOn (p23SecFamV R V) 7 AE.e64Sets AE.e64Sub)
    {f : Y} (hf : f ∈ p23Orb Z t e) (hVf : V ≤ aSub R Z f) :
    secImage (rLayerSub (Om R) V) (rLayer (Om R) f ⊓ rLayerSub (Om R) V) ⊓
      Subgroup.center (SecQuot (rLayerSub (Om R) V)) = ⊥ := by
  obtain ⟨hfX, hE₀E, hE₀X, hcov₀⟩ := p23_cover_V hc hZ hVZ hf hVf
  have hcovV : rLayer (Om R) f ≤ oddCoreOf (rLayer (Om R) f) ⊔
      (rLayer (Om R) f ⊓ rLayerSub (Om R) V) :=
    hcov₀.trans (sup_le_sup_left (le_inf hE₀E hE₀X) _)
  have hf2 : f * f = 1 := hZ.sq f (hZ.orb_le hf)
  have hY3f : OmegaOneCenter (rLayer (Om R) f) f := by
    obtain ⟨m, -, rfl⟩ := hf
    rw [rLayer_conj]
    exact hY3.conj m
  obtain ⟨hfX', hS3⟩ := p23_type237 hc hZ hVZ hY1 hf hVf
  refine central_inf_eq_bot hfX hf2 hcovV hY3f fun hcen => ?_
  have hgen : omegaGen (p23SecFamV R V) = ⊤ := p23SecFamV_pSpan R V
  have h1 := hasS3Quot_of_central hgen hcen hS3
  exact hno (hasS3Quot_e64_of (p23SecFamV_pSpan R V)
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V)) I h1)

end CenP

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
