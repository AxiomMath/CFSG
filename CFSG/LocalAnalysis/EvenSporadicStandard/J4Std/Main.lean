module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Data11
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataSplitJ4
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Squares
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Provenance
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModTriple

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem j4_not_standard
    (hA : M24Std.Ega81HypAZ2A8K) (hE : Ega81M24Section) (h : StdHyp G L) :
    ¬ IsSporadic L .J4 := by
  intro hL
  have := h.simple
  obtain ⟨z, -, -, hS⟩ := h.exists_setting_j4 hL
  obtain ⟨f⟩ := nonempty_mulEquiv_J hL
  let ι : J →* G := (L.subtype : L →* G).comp (f.symm : J →* L)
  have hι : Function.Injective ι := L.subtype_injective.comp f.symm.injective
  have hrange : ι.range = L := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact (f.symm j).2
    · intro hx
      exact ⟨f ⟨x, hx⟩, by simp [ι]⟩
  have hD := localData_J4 ι hι
  obtain ⟨p, q, u0, hD11⟩ := localData11_J4 ι hι
  have hM : ModData ι.range ((Eg uJ 11).map ι) :=
    ⟨fixData_J4 ι hι, tripleData_J4 ι hι, invConj_J4 ι hι, liftData_J4 ι hι,
      splitData_J4 ι hι, quotData_J4 ι hι⟩
  rw [hrange] at hD hD11 hM
  exact false_of_localData h.nonabelian hA hE h.kLocalSections hS hD hD11 hM

end CFSG.EvenSporadicStandard.J4Std
