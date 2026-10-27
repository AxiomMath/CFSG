module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputL
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UBasic
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSFacts
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGDefs

import CFSG.LocalAnalysis.OddStandard.SwapPartner.UTwoSec
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD4
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSMain
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UKhat
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UCaseA10
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UCaseL44

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern
  CFSG.Blueprint.NativeSporadic CFSG.OddStandard.AltStdBal

open scoped commutatorElement

theorem exists_stdHyp_of_caseIII {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
    {ι ιd : Perm (Fin 10) →* G} (hL : NonExactShapeEightLookup) (hHS : HSFacts)
    (h : Setting G L 10) (F : UFrame z ι ιd)
    (h8 : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ centralizer (Agrp ι : Set G) →
      Q ≤ centralizer ({z * ι τ₀} : Set G) → Nat.card ↥Q ≤ 8)
    (hKG : CFSG.SectionRank.IsKGroupCat (TwoSec (z * ι τ₀)))
    (hO : CFSG.oddCore (TwoSec (z * ι τ₀)) = ⊥)
    {t : TwoSec (z * ι τ₀)} {Sg V : Subgroup (TwoSec (z * ι τ₀))} (hS : SwapShape t Sg V)
    (hAbar : ((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
        (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀)))) = (⁅Sg, Sg⁆ : Subgroup _))
    {K : Subgroup (TwoSec (z * ι τ₀))} (hK : K = CFSG.layer (TwoSec (z * ι τ₀)))
    (hc : CFSG.IsComponent K) (hAK : ⁅Sg, Sg⁆ ≤ K) (hne : ⁅Sg, Sg⁆ ≠ K) :
    ∃ K' : Subgroup G, CFSG.EvenSporadicStandard.StdHyp G K' ∧
      IsSporadic (↥K' ⧸ center ↥K') .HS := by
  haveI : IsSimpleGroup G := h.std.simple
  have hx : (z * ι τ₀) * (z * ι τ₀) = 1 := F.d8.x_sq
  have hx1 : z * ι τ₀ ≠ 1 := F.d8.x_ne
  have hAx : Agrp ι ≤ centralizer ({z * ι τ₀} : Set G) := Agrp_le_centralizer_of_frame F
  have hA : Group.IsPerfect ↥(Agrp ι) := isPerfect_Agrp F
  haveI hKc : K.Characteristic := by
    rw [hK]
    exact CFSG.LocalCores.layer_characteristic
  haveI hKn : K.Normal := inferInstance
  haveI hKperf : Group.IsPerfect K := hc.1.1
  have h4 : ∀ U : Subgroup (TwoSec (z * ι τ₀)), IsPGroup 2 U →
      U ≤ centralizer ((⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))) :
        Set (TwoSec (z * ι τ₀))) → Nat.card U ≤ 4 := by
    intro U hU hUle
    exact card_le_four_of_card_le_eight_twoSec hx hx1 (Agrp ι) hAx hA h8 U hU (by
      rw [hAbar]
      exact hUle)
  have h10 : 2 ^ 10 ∣ Nat.card (TwoSec (z * ι τ₀)) :=
    two_pow_ten_dvd_card_twoSec hx hx1
      (two_pow_eleven_dvd_card_centralizer h.std.nonab F)
  have hAK' : ((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
      (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀)))) ≤ K := by
    rw [hAbar]
    exact hAK
  rcases hL (TwoSec (z * ι τ₀)) t Sg V K hKG hO hS hK hc hAK hne with hA10 | hHS' | hL44
  · obtain ⟨e⟩ := hA10
    exact (false_of_alternating_ten hS hAK hne e h4 h10).elim
  · obtain ⟨e⟩ := hHS'
    have hKq : CFSG.IsQuasisimple ↥K := hc.1
    obtain ⟨Kh, hle, hnormal, hperf, hquasi, hAKh, ⟨e'⟩⟩ :=
      exists_khat hAx hA hKq hAK'
    have hs : IsSporadic (↥Kh ⧸ center ↥Kh) .HS := ⟨e'.trans e⟩
    exact ⟨Kh, HSCtx.exists_stdHyp
      { frame := F
        khat := { le := hle, normal := hnormal, perfect := hperf, quasisimple := hquasi,
                  agrp_le := hAKh, hs := hs }
        facts := hHS
        h8 := h8 } h⟩
  · have hKq : CFSG.IsQuasisimple ↥K := hc.1
    obtain ⟨Kh, hle, hnormal, hperf, hquasi, hAKh, ⟨e'⟩⟩ :=
      exists_khat hAx hA hKq hAK'
    exact (false_of_lieModel_l44 F hle hnormal hperf hAKh
      (CFSG.Blueprint.LieModel.of_mulEquiv e'.symm hL44)).elim

end CFSG.OddStandard.AltStdSec.SwapPartner
