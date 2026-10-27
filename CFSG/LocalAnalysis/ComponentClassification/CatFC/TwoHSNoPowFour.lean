module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HNFactsProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HSData
public import Certificates.Certificate27600

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
  CFSG.Sporadic.HNOddCore.Native CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.EvenSporadicStandard.TwoHS

section Abstract


theorem pow_four_ne_aux (t : C6) (htJ : (t : JH) = aJ) (ht1 : phi6 t = 1)
    (htc : ∀ y : C6, y * t = t * y) :
    ∀ y : C6, y ∈ Dsub.comap phi6 → y ^ 4 = t → False := by
  obtain rfl : t = t6C := Subtype.ext (htJ.trans coe_t6C.symm)
  exact Certificates.certificate27600

theorem pow_four_ne_of_doubleCover_hs {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E)
    (hc : Nat.card (Subgroup.center E) = 2)
    (hq : CFSG.Blueprint.NativeSporadic.IsSporadic (E ⧸ Subgroup.center E) .HS)
    {z : E} (hz : z ∈ Subgroup.center E) (hz1 : z ≠ 1) (w : E) : w ^ 4 ≠ z := by
  intro hw
  have hd := coverData_aux t6C t6C_mem_ker t6C_ne_one t6C_central
  have hE₀ := hd.isHSCover sign_core.2
  have hfin : Finite C6 := Nat.finite_of_card_ne_zero (by rw [card_CJ_t6]; norm_num)
  obtain ⟨f⟩ := nonempty_mulEquiv_of_doubleCover_hs hE hE₀.perfect hc hE₀.card_center hq
    hE₀.quotient
  have hzc : f z ∈ center ↥(Dsub.comap phi6) := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := f.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hd.center_comap, mem_subgroupOf] at hzc
  rcases hd.eq_one_or_eq hzc with h1 | h1
  · exact hz1 (f.injective (by rw [map_one]; exact Subtype.ext h1))
  · have h4 : ((f w : ↥(Dsub.comap phi6)) : C6) ^ 4 = t6C := by
      rw [← Subgroup.coe_pow, ← map_pow, hw, h1]
    exact pow_four_ne_aux t6C coe_t6C (MonoidHom.mem_ker.1 t6C_mem_ker) t6C_central _ (f w).2 h4

end Abstract

end CFSG.ComponentClassification.CatFC
