module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S2Odd

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section XhatMap

variable {T : Type} [Group T] [Finite T]

@[expose] def xhatMap (F : Subgroup T) [F.Normal] :
    T →* (T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F) :=
  (QuotientGroup.mk' (Open.fusionOddCore (T ⧸ F))).comp (QuotientGroup.mk' F)

theorem xhatMap_apply (F : Subgroup T) [F.Normal] (x : T) :
    xhatMap F x = (QuotientGroup.mk (QuotientGroup.mk x : T ⧸ F) :
      (T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F)) := rfl

theorem xhatMap_surjective (F : Subgroup T) [F.Normal] : Function.Surjective (xhatMap F) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem mem_ker_xhatMap (F : Subgroup T) [F.Normal] {x : T} :
    x ∈ (xhatMap F).ker ↔ (QuotientGroup.mk x : T ⧸ F) ∈ Open.fusionOddCore (T ⧸ F) := by
  rw [MonoidHom.mem_ker, xhatMap_apply, QuotientGroup.eq_one_iff]

theorem le_ker_xhatMap (F : Subgroup T) [F.Normal] : F ≤ (xhatMap F).ker := by
  intro f hf
  rw [mem_ker_xhatMap, (QuotientGroup.eq_one_iff f).2 hf]
  exact one_mem _

theorem fusionOddCore_xhat (F : Subgroup T) [F.Normal] :
    Open.fusionOddCore ((T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F)) = ⊥ :=
  fusionOddCore_quotient_eq_bot' _

end XhatMap

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
