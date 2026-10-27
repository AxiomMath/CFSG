module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Idx

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzL26 CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

@[expose] def fzDataOf (d : FzAutD) : AutI :=
  (pctx ()).mkA (fzIdx d.g1) (fzIdx d.g2) (fzIdx d.g3) (fzIdx d.g4)

theorem fzDataOf_ap (d : FzAutD) (x : FzUT) : (fzDataOf d).ap (fzIdx x) = fzIdx (fzEv d x) := by
  unfold fzDataOf PCtx.mkA AutI.ap PCtx.evTab
  simp only []
  rw [tabulate_getElem! _ _ (fzIdx_lt x)]
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := fzIdx_bits x
  rw [h0, h1, h2, h3, h4, h5]
  simp only [fzIdx_bit, fzIdx_c, fzIdx_m]
  rfl

@[expose] def fzAutI (σ : MulAut FzUT) : AutI := fzDataOf (fzGens σ)

theorem fzAutI_ap (σ : MulAut FzUT) (x : FzUT) : (fzAutI σ).ap (fzIdx x) = fzIdx (σ x) := by
  unfold fzAutI
  rw [fzDataOf_ap, fzEv_gens]

end CFSG.OddStandard.SmallF3.FritzII
