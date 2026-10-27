module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SH
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SJ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4ST3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SU5

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem Z4Good.ctx4Z
    (hglob : Sec4Glob G)
    (hg : Z4Good t L S x₁ x₂ lam rho tau) : Ctx4Z t L S x₁ x₂ lam rho tau := by
  obtain ⟨V', v₁, v₂, hV⟩ := hg.toZ4Pre.exists_VBase
  have htau := hg.tau_inv_Q hV
  exact
    { toCtx4Q := hg.toCtx4Q
      q_iso := hg.q_iso
      CQ_t := hg.CQ_t
      tQ := hg.tQ_eq
      tauQ := hg.tauQ_eq htau
      ttauQ := hg.ttauQ_eq
      data_V := ⟨V', v₁, v₂, hg.ctx4ZV htau hV⟩
      tau_cent_Y := hg.tau_cent
      cent_M_Y := hg.cent_M_Y
      tau_inv_Q := htau
      center_Qtau := hg.center_Qtau htau
      tG_Qtau := hg.tG_Qtau htau
      U_not_sylow_L := hg.U_not_sylow_L hglob htau hV
      tt_sylow := hg.tt_sylow }

theorem l411_zsetup_holds : L411ZSetupStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hglob _ hc hc' hiso
  have hp : Z4Pre t L S x₁ x₂ lam rho tau := ⟨hc, hiso⟩
  rcases hp.dichotomy with h | h
  · exact Or.inl (Z4Good.ctx4Z hglob ⟨hp, h⟩)
  · exact Or.inr (Z4Good.ctx4Z hglob (hp.good_of_cent_ttau hc' h))

end CFSG.OddStandard.SmallF3.HarrisU33
