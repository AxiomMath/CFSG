module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.Combinator
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayOuterDihedral
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UMainIII
import CFSG.LocalAnalysis.OddStandard.SwapPartner.D5One
import CFSG.LocalAnalysis.OddStandard.SwapPartner.SectionXExists
import CFSG.LocalAnalysis.OddStandard.SwapPartner.Trichotomy
import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayMain
import CFSG.LocalAnalysis.OddStandard.SwapPartner.WpGMain
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UCaseI
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UTwoSec
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD4
import CFSG.LocalAnalysis.OddStandard.SwapPartner.UKhatZ

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

theorem ys04a_of_inputs (hD : DihedralOuterInvolutionFact) (hL : NonExactShapeEightLookup)
    (hHS : HSFacts) : SwapFrameP2One := by
  intro G _ _ L Q z h d ι F hP2 hp
  classical
  haveI : IsSimpleGroup G := h.std.simple
  obtain ⟨ιd, hCd, hz, hagree, hg⟩ :=
    exists_frame_at_d_of_pairOrder_N10_one F.cent F.conj hP2 hp
  have UF : UFrame z ι ιd := ⟨F.cent, hCd, hz, hagree, hg⟩
  have h8 : ∀ Q' : Subgroup G, IsPGroup 2 Q' → Q' ≤ centralizer (Agrp ι : Set G) →
      Q' ≤ centralizer ({z * ι τ₀} : Set G) → Nat.card Q' ≤ 8 :=
    fun Q' hQ hQA hQx =>
      card_le_eight_of_isPGroup_of_pairOrder_N10_one F.cent F.conj hP2 hp hQ hQA hQx
  have hxx : (z * ι τ₀) * (z * ι τ₀) = 1 := x₂_mul_self F.cent
  have hx1 : z * ι τ₀ ≠ 1 := x₂_ne_one F.cent
  have hx2 : orderOf (z * ι τ₀) = 2 := orderOf_x₂ F.cent
  have hKG : CFSG.SectionRank.IsKGroupCat (TwoSec (z * ι τ₀)) :=
    isKGroupCat_twoSec h hx1
  have hO : CFSG.oddCore (TwoSec (z * ι τ₀)) = ⊥ := oddCore_twoSec_eq_bot h hx2
  obtain ⟨Sg, V, hS, hAbar⟩ := exists_swapShape_twoSec F.cent F.conj hP2
  have hStray := hStray_of_swapShape hD hS
  have hAx : Agrp ι ≤ centralizer ({z * ι τ₀} : Set G) := Agrp_le_centralizer_of_frame UF
  have hA : Group.IsPerfect ↥(Agrp ι) := isPerfect_Agrp UF
  have h4 : ∀ U : Subgroup (TwoSec (z * ι τ₀)), IsPGroup 2 U →
      U ≤ centralizer
        ((((Agrp ι).subgroupOf (centralizer ({z * ι τ₀} : Set G))).map
          (QuotientGroup.mk' (zpowers (selfC (z * ι τ₀))))) : Set (TwoSec (z * ι τ₀))) →
      Nat.card U ≤ 4 :=
    card_le_four_of_card_le_eight_twoSec hxx hx1 (Agrp ι) hAx hA h8
  have h4' : ∀ U : Subgroup (TwoSec (z * ι τ₀)), IsPGroup 2 U →
      U ≤ centralizer
        ((⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))) : Set (TwoSec (z * ι τ₀))) →
      Nat.card U ≤ 4 := by
    intro U hU hUA
    rw [← hAbar] at hUA
    exact h4 U hU hUA
  have h10 : 2 ^ 10 ∣ Nat.card (TwoSec (z * ι τ₀)) :=
    two_pow_ten_dvd_card_twoSec hxx hx1
      (two_pow_eleven_dvd_card_centralizer h.std.nonab UF)
  rcases trichotomy hO hS hStray with ⟨_, hnorm, _⟩ | ⟨K, hW⟩ | ⟨K, hK, hc, hAK, hne, _⟩
  · haveI : (⁅Sg, Sg⁆ : Subgroup (TwoSec (z * ι τ₀))).Normal := hnorm
    exact (false_of_normal_abar hS h4' h10).elim
  · exact (false_of_wreathCase F hP2 (z_mem_centralizer_x₂ F.cent) hW).elim
  · exact exists_stdHyp_of_caseIII hL hHS h UF h8 hKG hO hS hAbar hK hc hAK hne

end CFSG.OddStandard.AltStdSec.SwapPartner
