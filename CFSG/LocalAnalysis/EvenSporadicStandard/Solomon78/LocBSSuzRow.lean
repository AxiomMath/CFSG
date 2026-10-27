module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSOutModel

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.SuzOddCore

section Row


theorem odd_orderOf_of_pow_three {X : Type*} [Group X] {a : X} (h : a ^ 3 = 1) :
    Odd (orderOf a) := by
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h) with h1 | h1 <;>
    rw [h1] <;> decide

theorem suz_outModel : Nonempty (OutRowModel suzM (invE 0) rho0 suzD (suzInv 0)) := by
  obtain ⟨A, B, Z, l, hA, hB, hAM, hBM, hLM, hA3, hB3, hZmem, hZZ, hl0, hM, -, -, hcard, ht0M,
    hZ1, ⟨hZE, hZρ⟩, hnc⟩ := suz_row_facts
  have hcls := suz_classCheck
  refine ⟨{
    quot := suz_quot2Data
    A := A
    B := B
    z := Z
    l := l
    t_mem := ht0M
    E_iff := ?_
    A_mem := hA
    B_mem := hB
    A_odd := ?_
    B_odd := ?_
    gen_card := ?_
    z_mem := hZmem
    z_sq := hZZ
    z_ne := hZ1
    z_two := ?_
    l_mem := hLM
    l_conj := hl0
    gen := hM
    z_not_conj := hnc
    D_fuse := ?_ }⟩
  · intro y
    rw [invE_eq_centM (by norm_num : 0 < 4), centM, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, and_comm]
  · rw [Subgroup.orderOf_mk]
    exact odd_orderOf_of_pow_three hA3
  · rw [Subgroup.orderOf_mk]
    exact odd_orderOf_of_pow_three hB3
  · rw [card_suzD]
    exact hcard
  · intro hz hzD
    refine (suzD_twoAdic_centralizer hcls hzD ?_ ?_).ge
    · have : rho0 (⟨Z, hz⟩ * ⟨Z, hz⟩) = 1 := by
        have : (⟨Z, hz⟩ * ⟨Z, hz⟩ : invE 0) = 1 := Subtype.ext hZZ
        rw [this, map_one]
      rwa [map_mul] at this
    · exact fun h => hZρ h
  · intro x hx y hy hx2 hy2 hx1 hy1 _ _
    exact suzD_involutions_conj hcls x hx y hy hx2 hy2 hx1 hy1

end Row

end CFSG.EvenSporadicStandard.Solomon78
