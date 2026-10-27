module

import CFSG.ClassicalInvolution.SmallCases.NDBG3Gen
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.WP3SCSGen
public import CFSG.ClassicalInvolution.Asc77.WP3SCSVertex
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.RouteD.TwinY

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem genT_of_g2 {K K' J : Subgroup G} {z u t : G}
    (hs : TwinFrameSettingCore p f Ω K K' J z u t) (X : XCtx p f Ω z) {a₁ : Fin X.D.card}
    (hG2 : X.D.tag a₁ = .G2) (hothers : ∀ j, j ≠ a₁ → X.D.tag j = .PSL ∧ X.D.rank j = 2)
    (hzA1 : ∀ j, (X.D.tag j = .PSL ∧ X.D.rank j = 2) →
      Balance.oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (X.psi j).range) :
    CentralizerGenerationStar Ω (Subgroup.closure ({z, u, t} : Set G)) t := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  obtain ⟨g₀, V, hgz, hag, hug, hu1, huz, hua, hauz⟩ := hs.exists_twinVertex
  have hD4 : X.D.tag a₁ ≠ .trialityD4 := by
    rw [hG2]
    decide
  have hexp : X.D.exp a₁ = f := X.exp_eq a₁ hD4
  have hr : X.D.rank a₁ = 0 := by
    have h := X.D.admissible a₁
    rw [hG2] at h
    exact h.2.2.1
  have hMF : TwinMFGeneration p (X.D.exp a₁) (X.D.tag a₁) (X.D.rank a₁) := by
    rw [hexp, hG2, hr]
    exact twinMFGeneration_g2 hp hq
  have hgen := X.generation_of_vertex a₁ hD4 hothers hzA1 V hMF hu1 huz hua hauz
  have hconj := centralizerGenerationStar_conj hΩ.conjInvariant g₀ hgen
  rw [conjSub_closure_three, hag, hug, hgz] at hconj
  exact hconj

end CFSG.ClassicalInvolution.NDB.NDBG3
