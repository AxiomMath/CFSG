module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBE7E8
public import CFSG.LocalAnalysis.StandardType.GGExcFrameLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.RootTuples

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoTB
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8 (e8Finset)

local instance e8DataNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def e8SingerWord : List (Fin Tag.E8.rank) :=
  [3, 5, 4, 3, 2, 6, 4, 5, 1, 3, 0, 2, 3, 1, 4, 3, 2, 0]

@[expose] def e8SingerPerm : Fin 8 → Fin 8 := ![0, 3, 1, 4, 5, 6, 7, 2]

@[expose] def e8FrameLambda (v : Fin 8 → ZMod 3) : Fin Tag.E8.rank → ZMod 3 :=
  fun k => ∑ i, v i * ((frameE8Root i k : ℤ) : ZMod 3)

@[expose] def e8FrameLineRep : Fin 8 → ZMod 3 := ![0, 1, 1, 0, 1, 0, 0, 0]

@[expose] def e8FrameTrickData :
    List ((Fin 8 → ZMod 3) × List (Fin Tag.E8.rank) × (Fin 8 → ZMod 3)) :=
  [(![0, 1, 0, 0, 0, 0, 0, 0],
    [5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3,
     4, 5, 1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2,
     1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1],
    ![0, 0, 2, 0, 0, 0, 0, 0]),
   (![0, 1, 1, 0, 0, 0, 0, 0],
    [2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3,
     4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1,
     3, 4, 5, 6, 0, 2, 3, 4, 1, 3, 2, 0],
    ![0, 1, 2, 1, 0, 0, 1, 0]),
   (![0, 1, 0, 0, 1, 0, 0, 0],
    [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1, 5, 4, 3, 1,
     2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1,
     3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5],
    ![0, 1, 0, 1, 2, 0, 0, 1]),
   (![0, 1, 0, 0, 0, 1, 0, 0],
    [1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2,
     3, 4, 5, 1, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7,
     6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    ![0, 1, 1, 0, 0, 2, 0, 1]),
   (![0, 1, 1, 1, 0, 0, 0, 0],
    [1, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 1,
     0, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4,
     5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 0],
    ![0, 1, 0, 2, 1, 0, 0, 1]),
   (![0, 1, 1, 0, 0, 1, 0, 0],
    [2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 1, 2, 0,
     3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4,
     5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3],
    ![0, 1, 0, 0, 1, 2, 1, 0]),
   (![0, 1, 1, 0, 0, 0, 1, 0],
    [4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4,
     0, 1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1,
     3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0],
    ![0, 1, 0, 0, 1, 1, 2, 0]),
   (![0, 1, 0, 0, 1, 0, 1, 0],
    [3, 1, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2,
     3, 4, 1, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5,
     6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5],
    ![0, 1, 1, 1, 0, 0, 2, 0]),
   (![0, 1, 1, 1, 1, 0, 0, 0],
    [2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3,
     4, 1, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4,
     5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    ![0, 1, 1, 1, 0, 0, 1, 0]),
   (![0, 1, 1, 1, 0, 1, 0, 0],
    [2, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6,
     0, 2, 3, 4, 5, 1, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2,
     3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4],
    ![0, 1, 1, 1, 0, 0, 1, 0]),
   (![0, 1, 1, 1, 0, 0, 1, 0],
    [5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3,
     4, 5, 0, 1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3,
     2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0],
    ![0, 1, 1, 2, 0, 0, 2, 0]),
   (![0, 1, 1, 0, 1, 1, 0, 0],
    [1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1,
     6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6,
     5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    ![0, 1, 1, 0, 0, 1, 0, 1]),
   (![0, 1, 1, 0, 1, 0, 1, 0],
    [2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3,
     4, 1, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4,
     5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    ![0, 1, 1, 1, 0, 0, 1, 0]),
   (![0, 1, 1, 1, 1, 1, 0, 0],
    [2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3,
     4, 1, 3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4,
     5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    ![0, 1, 1, 1, 0, 0, 1, 0]),
   (![0, 1, 1, 1, 1, 0, 1, 0],
    [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1, 6, 5, 4, 3,
     1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2,
     1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    ![0, 1, 0, 1, 1, 0, 0, 1]),
   (![0, 1, 1, 1, 0, 1, 1, 0],
    [1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2,
     3, 4, 5, 1, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6,
     7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4],
    ![0, 1, 1, 0, 0, 1, 0, 1]),
   (![0, 1, 1, 1, 1, 1, 1, 0],
    [1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1,
     6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6,
     5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    ![0, 1, 1, 0, 0, 1, 0, 1]),
   (![0, 1, 1, 1, 1, 1, 1, 1],
    [3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 6, 5, 4, 3,
     1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2,
     1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6],
    ![0, 1, 1, 0, 0, 2, 0, 2])]

@[expose] def e8FrameReps : List (Fin 8 → ZMod 3) :=
  e8FrameLineRep :: e8FrameTrickData.map Prod.fst

theorem e8SingerPerm_root : ∀ a : Fin 8, wAct Tag.E8 e8SingerWord (frameE8Root a) =
    frameE8Root (e8SingerPerm a) ∨
      wAct Tag.E8 e8SingerWord (frameE8Root a) = -frameE8Root (e8SingerPerm a) := by
  decide +kernel

theorem e8SingerWord_le : ∀ i ∈ e8SingerWord, i.val ≤ 6 := by decide +kernel

theorem e8SingerPerm_iterate_seven : ∀ j, e8SingerPerm^[7] j = j := by decide +kernel

theorem e8FrameTrickData_spec : ∀ x ∈ e8FrameTrickData,
    TableBExc.torusWord Tag.E8 3 x.2.1 (e8FrameLambda x.1) = e8FrameLambda x.1 ∧
      TableBExc.torusWord Tag.E8 3 x.2.1 (e8FrameLambda (Pi.single 0 1)) = e8FrameLambda x.2.2 ∧
      x.1 0 = 0 ∧ x.2.2 0 = 0 ∧ ∀ k : ZMod 3, x.2.2 ≠ k • x.1 := by
  decide +kernel

theorem exists_e8SingerPerm_iterate_reps : ∀ u : Fin 8 → Bool, u 0 = false →
    u ≠ (fun _ => false) → ∃ k < 7, ∃ r ∈ e8FrameReps, r 0 = 0 ∧ (∀ j, r j = 0 ∨ r j = 1) ∧
      ∀ j, (u j = true ↔ r (e8SingerPerm^[k] j) ≠ 0) := by
  decide +kernel

section LineRootKernel

open Matrix

theorem frameCoord_e8FrameLambda_lineRep :
    ExcFrames.frameCoord Tag.E8 3 (e8FrameLambda e8FrameLineRep) =
      Pi.single (6 : Fin Tag.E8.rank) 2 := by
  decide +kernel

theorem e8LineKernel_count : ∀ α ∈ e8Finset, α 6 % 3 = 0 →
    ((α 6 = 0 ∧ α 7 = 0) ↔
      ((e8Finset).filter fun β => β 6 % 3 = 0 ∧ iform α β = 0).card = 36) := by
  decide +kernel

theorem e8LineKernel_orth : ∀ α ∈ e8Finset, α 6 % 3 = 0 → ¬(α 6 = 0 ∧ α 7 = 0) →
    ∀ β ∈ e8Finset, β 6 = 0 → β 7 = 0 →
      α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0 := by
  decide +kernel

end LineRootKernel

theorem e8FrameReps_cases : ∀ r ∈ e8FrameReps,
    r = e8FrameLineRep ∨ ∃ w c, (r, w, c) ∈ e8FrameTrickData := by
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr
  · exact Or.inl rfl
  · obtain ⟨⟨r', w, c⟩, hx, rfl⟩ := List.mem_map.1 hr
    exact Or.inr ⟨w, c, hx⟩

section FrameCoord


theorem frameCoordHom_frameE8_eq (v : Fin 8 → ZMod 3) :
    ExcFrameIso.frameCoordHom frameE8 v = e8FrameLambda v :=
  rfl

end FrameCoord

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
