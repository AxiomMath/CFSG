module

public import CFSG.ClassicalInvolution.Q3.Q3E7MStep
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclHJ

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)

section HJ

theorem conjSub_std_of_torus3 {y : M₇}
    (hy : ∃ b : Fin (Tag.rank .E7) → (GaloisField 3 1)ˣ,
      εm (GaloisField 3 1) y = rootDiagUnit .E7 b) {γ : V7} (hγ : IsRoot .E7 γ) :
    conjSub y (stdRankOne D₇ γ) = stdRankOne D₇ γ := by
  have hF : ringChar (GaloisField 3 1) ≠ 2 := ringChar_galoisField_ne_two (by norm_num)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hγF := std_mem_fund3 hγ
  obtain ⟨b, hb⟩ := hy
  have hwd : εm (GaloisField 3 1) y * rootTorusSL2 .E7 (GaloisField 3 1) γ (-1) =
      rootTorusSL2 .E7 (GaloisField 3 1) γ (-1) * εm (GaloisField 3 1) y := by
    rw [hb, rootTorusSL2_eq_thetaDiag hγ, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  apply eq_of_map_εm_eq3 (conjSub_mem_fundamentalSubgroups hγF y) hγF
  rw [map_conjSub, map_stdRankOne_εm hγ,
    map_conj_rootRankOneGroup_of_commute_gen hF hodd hγ (εm_mem y) hwd]

theorem exists_mem_HJ_conj3 {x : M₇}
    (hx : ∃ η ∈ NJ (GaloisField 3 1) JE7, ∃ b : Fin (Tag.rank .E7) → (GaloisField 3 1)ˣ,
      εm (GaloisField 3 1) x = η * rootDiagUnit .E7 b) :
    ∃ h ∈ HJ 3 1, ∀ γ : V7, IsRoot .E7 γ →
      conjSub x (stdRankOne D₇ γ) = conjSub h (stdRankOne D₇ γ) := by
  obtain ⟨η, hη, b, hxe⟩ := hx
  obtain ⟨h₀, hh₀, hεh₀⟩ := Subgroup.mem_map.1 (NJ_le_map_HJ hη)
  refine ⟨h₀, hh₀, fun γ hγ => ?_⟩
  have hεy : εm (GaloisField 3 1) (h₀⁻¹ * x) = rootDiagUnit .E7 b := by
    rw [map_mul, map_inv, hεh₀, hxe]
    group
  have hx' : x = h₀ * (h₀⁻¹ * x) := by group
  rw [hx', conjSub_mul, conjSub_std_of_torus3 ⟨b, hεy⟩ hγ]

theorem commutes_HJ_theta3 : Commutes (HJ 3 1) (stdRankOne D₇ thetaE7) := by
  refine commutes_iSup_left.mpr fun i => ?_
  exact commutes_std3 (isRoot_single .E7 (iota7 i)) isRoot_thetaE7
    (iform_single_eq_zero_of_mem_E7 (iota7_mem_JE7 i))

end HJ

end CFSG.ClassicalInvolution.Q3.Q3W
