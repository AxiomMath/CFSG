module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCSpFull

variable {r : ℕ} {K : Type} [Field K]

theorem spEnd_injective : Function.Injective (spEnd (r := r) (K := K)) := by
  intro a b h
  apply spLin_injective
  apply Units.ext
  exact h

theorem spEnd_mem_commutant_iff {x y : StatedSp r K} :
    spEnd y ∈ commutant (spEnd x) ↔ Commute y x := by
  rw [mem_commutant, commute_iff_eq, commute_iff_eq]
  constructor
  · intro h
    apply spEnd_injective
    calc spEnd (y * x) = spEnd y * spEnd x := spEnd_mul y x
      _ = spEnd x * spEnd y := h
      _ = spEnd (x * y) := (spEnd_mul x y).symm
  · intro h
    calc spEnd y * spEnd x = spEnd (y * x) := (spEnd_mul y x).symm
      _ = spEnd (x * y) := congrArg spEnd h
      _ = spEnd x * spEnd y := spEnd_mul x y

theorem spEnd_mapsTo_primaryComponent {x y : StatedSp r K} (h : Commute y x) (a : K[X]) :
    Set.MapsTo (spEnd y) (primaryComponent (spEnd x) a) (primaryComponent (spEnd x) a) :=
  fun _ hv => apply_mem_primaryComponent ((mem_commutant (spEnd x)).mp
    (spEnd_mem_commutant_iff.mpr h)) hv

@[expose] noncomputable def spBlockRestrict {x y : StatedSp r K} (h : Commute y x) (a : K[X]) :
    Module.End (AdjoinRoot a) (primaryComponent (spEnd x) a) :=
  commutantRestrict a ⟨spEnd y, spEnd_mem_commutant_iff.mpr h⟩

@[simp] theorem coe_spBlockRestrict {x y : StatedSp r K} (h : Commute y x) (a : K[X])
    (v : primaryComponent (spEnd x) a) :
    ((spBlockRestrict h a v : primaryComponent (spEnd x) a) : Fin r ⊕ Fin r → K) =
      spEnd y (v : Fin r ⊕ Fin r → K) :=
  coe_commutantRestrict a ⟨spEnd y, spEnd_mem_commutant_iff.mpr h⟩ v

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
