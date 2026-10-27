module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf5Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Orth

section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem eq_of_isUniqueInvolution_secImgR {R : Subgroup G} {t : G}
    {z : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)}
    (hRc : R ≤ Subgroup.centralizer ({c} : Set G))
    (hRH : R.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ coreHull Ω c) (htR : t ∈ R)
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hz : IsUniqueInvolution (secImgR Ω c R) z) :
    z = QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
      ⟨⟨t, hRc htR⟩, hRH (Subgroup.mem_subgroupOf.mpr htR)⟩ := by
  set x : ↥(coreHull Ω c) := ⟨⟨t, hRc htR⟩, hRH (Subgroup.mem_subgroupOf.mpr htR)⟩ with hx
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥(coreHull Ω c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c)
  have hxP : x ∈ ((R.subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf (coreHull Ω c)) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr htR)
  have hxmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) x ∈ secImgR Ω c R :=
    Subgroup.mem_map_of_mem _ hxP
  have hxx : x * x = 1 := Subtype.ext (Subtype.ext ht2)
  have hsq : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) x *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) x = 1 := by
    rw [← map_mul, hxx, map_one]
  have hx1 : x ≠ 1 := fun h => ht1 (congrArg (fun y : ↥(coreHull Ω c) => ((y : ↥(Subgroup.centralizer ({c} : Set G))) : G)) h)
  have hne : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) x ≠ 1 := by
    intro h
    have hker : x ∈ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))).ker :=
      MonoidHom.mem_ker.mpr h
    rw [QuotientGroup.ker_mk'] at hker
    have hxN : (⟨x, hker⟩ : classicalInvolutionOddCore ↥(coreHull Ω c)) *
        ⟨x, hker⟩ = 1 := Subtype.ext hxx
    have hxN1 : (⟨x, hker⟩ : classicalInvolutionOddCore ↥(coreHull Ω c)) ≠ 1 :=
      fun h' => hx1 (congrArg Subtype.val h')
    have h2 : orderOf (⟨x, hker⟩ : classicalInvolutionOddCore ↥(coreHull Ω c)) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hxN) hxN1
    have h3 := orderOf_dvd_natCard (⟨x, hker⟩ : classicalInvolutionOddCore ↥(coreHull Ω c))
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h3)
  exact ((hz.unique _ hxmem hsq).resolve_left hne).symm

end Sec

end Orth

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
