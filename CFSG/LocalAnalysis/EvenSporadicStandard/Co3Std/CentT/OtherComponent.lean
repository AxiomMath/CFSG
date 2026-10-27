module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.KDApply
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.NoOther
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcCat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcFus
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Transfer

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Open
open scoped commutatorElement

namespace CentConfig

variable {X : Type} [Group X] [Finite X] {a b : X} {E : Subgroup X} {Fus : X → Prop}

section Certified


theorem case_other (hKD : KDCo3Cat) (h : CentConfig X a b E Fus) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (haL : a ∈ normalizer (L : Set X)) (hEL : E ≤ L) (hne : E ≠ L) :
    TransferWitness X a Fus := by
  obtain ⟨hcat, hout⟩ := kd_facts hKD h hL haL hEL hne
  have hperf : commutator ↥L = ⊤ := hL.2.2.1
  have hZ : IsPGroup 2 (center ↥L) := isPGroup_center_component h hL
  have hQ : ExcQuot (↥L ⧸ center ↥L) := ExcQuot.of_catalogue hcat
  have hF : FixLarge ↥L := fixLarge_of_excQuot hQ
  have hLn : L.Normal := h.normal_of_fixLarge hL hEL hF
  haveI : L.Normal := hLn
  obtain ⟨N, hNn, hNidx, hN⟩ :=
    exists_normal_of_cover L hperf hQ.card_mulAut_dvd hQ.center_eq_bot
  have haN : a ∉ N := by
    intro ha
    obtain ⟨k, hk, hkl⟩ := (hN a).mp ha
    exact hout ⟨k, hk⟩ ((conjAut_eq_conj_iff L haL ⟨k, hk⟩).mpr hkl)
  have hidx : ¬ 4 ∣ N.index := by
    intro h4
    exact absurd (h4.trans hNidx) (by norm_num)
  have hFus : ∀ w ∈ N, ¬ Fus w := by
    intro w hwN hFw
    obtain ⟨hw2, _hw1, hD⟩ := h.fus w hFw
    obtain ⟨k, hk, hact⟩ := (hN w).mp hwN
    exact false_of_fus_inner L hZ hQ hw2 hk hact hD
  haveI : N.Normal := hNn
  exact transferWitness_of_normal N h.a_sq haN hidx hFus

end Certified

end CentConfig

end CFSG.EvenSporadicStandard.Co3Std.CentT
