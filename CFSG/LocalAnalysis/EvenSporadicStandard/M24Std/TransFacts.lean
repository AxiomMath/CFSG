module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransPure

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {G : Type} [Group G]

theorem translationData_of_sextetFacts [Finite G]
    {L A : Subgroup G} {z : G} (hs : LocalSetting G L z) (hAL : A ≤ L) (hF : SextetFacts L A)
    (hcase : ¬ egM A z ≤ centralizer ({z} : Set G)) : TranslationData A z :=
  Trans.translationData_of_facts hs hAL hF hcase fun _ _ hrA hr hfix hS hSA hSr =>
    card_le_eight_mul_of_normalizer hF.elem hF.card_A hrA hr hfix hS hSA hSr

end CFSG.EvenSporadicStandard.M24Std
