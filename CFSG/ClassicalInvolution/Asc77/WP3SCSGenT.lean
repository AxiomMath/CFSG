module

public import CFSG.ClassicalInvolution.Asc77.WP3SCSVertex
public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinMain
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSL4
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSp4
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSu4
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSmall
public import CFSG.ClassicalInvolution.Asc77.WP3SCSD4Gen
import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3SCSGen
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY

section GenT

variable {p f : ℕ} [Fact p.Prime]

theorem twinFrameGenT_of_plus
    (hPlus : ∀ (_ : p ≠ 2) (_ : 5 ≤ p ^ f), TwinMFGeneration p f .POmegaPlus 4) :
    TwinFrameGenT p f := by
  intro G _ _ _ Ω K K' J z u t hs ⟨D, hD⟩
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hd := hs.frame
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  have hK'cl : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hd.hK'.1 hzK'
  obtain ⟨g₀, V, hgz, hag, hug, hu1, huz, hua, hauz⟩ := exists_twinVertex hs
  let X : XCtx p f Ω z :=
    { K := K, hK := hd.mem, hKz := hd.hz, hΩ := hΩ, hp := hp, hq := hq, D := D }
  obtain ⟨a₁, hlist, hna, hothers⟩ := (show TwinShapeData X.D from hD).exists_big
  have hzA1 := X.A1_contains_zbar (show TwinShapeData X.D from hD) hd.hK'.1 hK'cl hd.hne
  have hD4 : X.D.tag a₁ ≠ .trialityD4 := by
    rcases hlist with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hexp : X.D.exp a₁ = f := X.exp_eq a₁ hD4
  have hMF : TwinMFGeneration p (X.D.exp a₁) (X.D.tag a₁) (X.D.rank a₁) := by
    rw [hexp]
    rcases hlist with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact twinMFGeneration_psp2 hp (by omega)
    · rw [h1, h2]
      exact twinMFGeneration_psl4 hp f
    · rw [h1, h2]
      exact twinMFGeneration_psu4 hp hq
    · rw [h1, h2]
      exact twinMFGeneration_odd hp hq (by norm_num)
    · rw [h1, h2]
      exact hPlus hp hq
    · rw [h1, h2]
      exact twinMFGeneration_minus hp hq (by norm_num)
  have hgen := X.generation_of_vertex a₁ hD4 hothers hzA1 V hMF hu1 huz hua hauz
  have hconj := centralizerGenerationStar_conj hΩ.conjInvariant g₀ hgen
  rw [conjSub_closure_three, hag, hug, hgz] at hconj
  exact hconj

theorem twinFrameGenT_proved : TwinFrameGenT p f :=
  twinFrameGenT_of_plus fun hp2 hq => twinMFGeneration_plus4 hp2 hq

end GenT

end CFSG.ClassicalInvolution.Asc77
