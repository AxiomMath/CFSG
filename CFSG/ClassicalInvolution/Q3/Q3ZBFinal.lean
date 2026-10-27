module

public import CFSG.ClassicalInvolution.Q3.Q3ZBStruct
public import CFSG.ClassicalInvolution.Q3.Q3ZBAct
public import CFSG.ClassicalInvolution.Q3.Q3ZAFinal
public import CFSG.ClassicalInvolution.Q3.Q3ZACross
public import CFSG.ClassicalInvolution.Q3.Q3ZATri
public import CFSG.ClassicalInvolution.Q3.Q3VRowSp2
public import CFSG.ClassicalInvolution.Q3.Q3TSetup
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZTop
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.Q3.Q3ZA CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane longBlock
  planeGroup_stdPlane)
open scoped MatrixGroups

theorem heisAtTheorem : HeisAtTheorem := by
  intro G _ _ _ K z hctx A B X hL
  obtain ⟨Kp, Kh, Kr, hT⟩ := LayerTriple.exists_tripleMem hL
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hctx.setup.ih
  obtain ⟨e0e1, f0f1, e0f1, e1f0, hnorm⟩ := hT.heis_inputs hctx hO
  have hmem : ∀ (Λ : StatedSp 2 F3 →* G) (k : Fin 2) (y : SL(2, F3)),
      Λ (longBlock F3 2 k y) ∈ (planeGroup (stdPlane F3 2 k)).map Λ := fun Λ k y =>
    ⟨longBlock F3 2 k y, by rw [planeGroup_stdPlane]; exact ⟨y, rfl⟩, rfl⟩
  refine heisAt_or_of_normalizes hT.injA hT.hub hT.end_p hT.end_r
    (fun s y => hT.cA (A s) ⟨s, rfl⟩ _ (hT.B1 ▸ hmem B 1 y))
    (fun s y => hT.cB (B s) ⟨s, rfl⟩ _ (hT.A0 ▸ hmem A 0 y))
    (fun s y => hT.cX (X s) ⟨s, rfl⟩ _ (hT.A1 ▸ hmem A 1 y))
    (hT.negOne_layers hctx).1 e0e1 f0f1 e0f1 e1f0 hnorm

theorem c3ChainInput_proved : C3ChainInput :=
  c3ChainInput_of_pieces triangleExists heisAtTheorem

end CFSG.ClassicalInvolution.Q3.Q3ZB
