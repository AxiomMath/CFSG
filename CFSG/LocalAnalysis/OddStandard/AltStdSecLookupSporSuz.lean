module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupAlt9
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporBase
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ONOuter
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz
public import CFSG.Sporadic.ONOddCore.Block
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

theorem lookup_card_fixedSubgroup_eq {G : Type} [Group G] (α : MulAut G) :
    Nat.card (fixedSubgroup α) = Nat.card (fixSub α) :=
  congrArg (fun H : Subgroup G => Nat.card H) (by ext x; exact Iff.rfl)

theorem lookup_orderOf_eq_two_of_not_inner {G : Type} [Group G] {α : MulAut G} (hα2 : α * α = 1)
    (hα : α ∉ inner G) : orderOf α = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hα2) (fun h => hα (h ▸ one_mem _))

theorem noLargeAlt_Suz :
    NoLargeAltComponents .Suz := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B _ hAlt => ?_⟩
  · exact not_isLargeAlt_of_card_quotient (c := 20160)
      (fun m hm => lookup_factorial_div_two_ne_of_lt (by norm_num) hm)
      (Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B hB)
  · have hcard := SeitzReduction.SporadicRefine.suz_outer_card_fixedSubgroup e
      (lookup_orderOf_eq_two_of_not_inner hα2 hα) hα
    rw [lookup_card_fixedSubgroup_eq] at hcard
    have h1 : 181440 ∣ Nat.card (fixSub α) :=
      (dvd_card_of_isLargeAlt hAlt).trans (Subgroup.card_subgroup_dvd_card B)
    rcases hcard with h | h <;> rw [h] at h1 <;> revert h1 <;> decide

theorem noLargeAlt_ON :
    NoLargeAltComponents .ONan := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht B hB => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα B _ hAlt => ?_⟩
  · exact not_isLargeAlt_of_card_quotient (c := 20160)
      (fun m hm => lookup_factorial_div_two_ne_of_lt (by norm_num) hm)
      (Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
        ⟨e⟩ t ht B hB)
  · have hord := lookup_orderOf_eq_two_of_not_inner hα2 hα
    have hBd : Nat.card B ∣ Nat.card (fixSub α) := Subgroup.card_subgroup_dvd_card B
    have hfd : Nat.card (fixSub α) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have hcardG : Nat.card G = 460815505920 :=
      (Nat.card_congr e.toEquiv).trans Sporadic.ONOddCore.card_native_ON
    obtain ⟨m, hm, ⟨φ⟩⟩ := hAlt
    rcases Nat.lt_or_ge m 10 with hlt | hge
    · obtain rfl : m = 9 := by omega
      have h64 : 2 ^ 6 ∣ Nat.card B := by
        rw [card_eq_of_equiv_alt (by omega) φ]
        norm_num [Nat.factorial]
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime 2 h64
      let ι : B →* G := (fixSub α).subtype.comp B.subtype
      have hι : Function.Injective ι := (fixSub α).subtype_injective.comp B.subtype_injective
      have hT₀ : Nat.card (T.map ι) = 64 := by
        rw [Subgroup.card_map_of_injective hι, hT]
        norm_num
      have hfixT : ∀ x ∈ T.map ι, α x = x := by
        rintro _ ⟨b, -, rfl⟩
        exact (b : fixSub α).2
      obtain ⟨q, hqT, hq4, W, hWT, hW32, hWc⟩ :=
        SeitzReduction.SporadicRefine.on_outer_exists_of_fix_card_sixtyfour e hord hα hT₀ hfixT
      obtain ⟨b, -, rfl⟩ := hqT
      have hWr : W ≤ ι.range := fun w hw => by
        obtain ⟨c, -, rfl⟩ := hWT hw
        exact ⟨c, rfl⟩
      have hW' : Nat.card (W.comap ι) = 32 := by
        rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hWr, hW32]
      exact lookup_false_of_alt9_order_four φ (q := b)
        (by rw [← orderOf_injective ι hι b]; exact hq4) hW'
        (fun w hw => hι (by rw [map_mul, map_mul]; exact hWc _ hw))
    · have h1 : 1814400 ∣ Nat.card B := by
        rw [card_eq_of_equiv_alt (by omega) φ]
        exact lookup_dvd_factorial_div_two_ten hge
      have h2 := h1.trans (hBd.trans hfd)
      rw [hcardG] at h2
      revert h2
      decide

end CFSG.OddStandard.AltStdSec
