module

public import CFSG.LocalAnalysis.ABGTheoremB.V4Prop1
public import CFSG.LocalAnalysis.ABGTheoremB.IVNFacts
import CFSG.LocalAnalysis.ABGTheoremB.V56Bridges
import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.InputsFourFusion

public section

namespace CFSG.ABGTheoremB.V4

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {J : Subgroup G}

theorem lemmaV31Input_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.IVNFacts)
    (hJ : σ.IsV21Layer J) : LemmaV31Input σ J := by
  have h := σ.lemmaV31_of hσ hII hN J hJ
  refine ⟨h.coprime, fun a ha b hb => ?_, h.covers⟩
  have hab := hN.C_inf_L₀_commutator (Subgroup.commutator_mem_commutator
    (Subgroup.mem_inf.mpr ⟨ha.1, hJ.le ha.2⟩) (Subgroup.mem_inf.mpr ⟨hb.1, hJ.le hb.2⟩))
  rw [commutatorElement_def] at hab
  rw [← hJ.inf_eq]
  exact Subgroup.mem_inf.mpr
    ⟨J.mul_mem (J.mul_mem (J.mul_mem ha.2 hb.2) (J.inv_mem ha.2)) (J.inv_mem hb.2), hab⟩

theorem commutatorInput_of (hT : σ.TIFacts) : CommutatorInput σ :=
  hT.commutator_le

omit [Finite G] in
theorem dGroupSignalizerInput_of_height_ne_one (hh : σ.height ≠ 1) : DGroupSignalizerInput σ :=
  fun h => absurd h hh

theorem lemmaV45_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (hN : σ.IVNFacts) (hT : σ.TIFacts) (h42 : LemmaII42Input σ J) (h46 : LemmaII46Input σ J)
    (h49 : LemmaII49Input σ J) (h21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p) : σ.LemmaV45 J :=
  lemmaV45 hσ hII hJ (lemmaV31Input_of hσ hII hN hJ) (commutatorInput_of hT) h42 h46 h49 h21
    (TotallyInverted.Inputs.qGroupFourFusion G)

theorem propV41_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hJ : σ.IsV21Layer J)
    (hN : σ.IVNFacts) (hT : σ.TIFacts) (h42 : LemmaII42Input σ J) (h46 : LemmaII46Input σ J)
    (h49 : LemmaII49Input σ J) (h21 : ∀ r : ℕ, σ.HypIV7 r → r = σ.p)
    (hQS : QGroupSignalizerInput σ) (hDS : DGroupSignalizerInput σ) : σ.PropV41 J :=
  propV41 hσ hII hJ (lemmaV31Input_of hσ hII hN hJ) (commutatorInput_of hT) h42 h46 h49 h21
    (TotallyInverted.Inputs.qGroupFourFusion G) hQS hDS

end CFSG.ABGTheoremB.V4
