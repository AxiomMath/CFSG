module

public import CFSG.GH74.E2.A6Inner
public import CFSG.GH74.E2.A6AutTable
public import CFSG.GH74.E2.OuterCore

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS CFSG.GH74.Generic

theorem noLocalA6_of_tables
    (hComp : ComponentList) (hP : PumpUpData) : NoLocalA6 := by
  intro G _ _ hH t K c hd hsh
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, huniq⟩ := hComp G hH t hd.order_t K hd.comp
  obtain ⟨-, hncen, hrk⟩ := a6_terminal_facts hComp hP hH hd.order_t hd.comp hsh
  have hnc : ∀ S : Sylow 2 G, ¬ ((S : Subgroup G) ≤ Cen t) := fun S hS =>
    hncen (isCentralInvolution_of_sylow_le_cen hd.order_t S hS)
  have hT := unique_involution_of_pRank hd.order_t hd.comp.1 hrk
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  obtain ⟨eR⟩ := sylow_two_of_shapeA6 hsh R
  have hsr : (DihedralGroup.sr 0 : DihedralGroup 4) ^ 2 = 1 := by decide
  have hsrr : (DihedralGroup.sr 0 : DihedralGroup 4) * DihedralGroup.r 1 ≠
      DihedralGroup.r 1 * DihedralGroup.sr 0 := by decide
  let f0 : ↥(R : Subgroup ↥K) := eR.symm (DihedralGroup.sr 0)
  let g0 : ↥(R : Subgroup ↥K) := eR.symm (DihedralGroup.r 1)
  have hf0 : f0 ^ 2 = 1 := by
    show eR.symm (DihedralGroup.sr 0) ^ 2 = 1
    rw [← map_pow, hsr, map_one]
  have hfg0 : f0 * g0 ≠ g0 * f0 := by
    intro h
    apply hsrr
    have := congrArg eR h
    simpa [f0, g0] using this
  have hf2 : (((f0 : ↥K) : G)) ^ 2 = 1 := by
    simpa using congrArg (fun x : ↥(R : Subgroup ↥K) => ((x : ↥K) : G)) hf0
  have hfg : ((f0 : ↥K) : G) * ((g0 : ↥K) : G) ≠ ((g0 : ↥K) : G) * ((f0 : ↥K) : G) := by
    intro h
    exact hfg0 (Subtype.ext (Subtype.ext h))
  obtain ⟨S₁, hS₁C, hS₁2, -, hmax, htS, haut⟩ := exists_sylow_haut_of_noQ8C2 hH hd.order_t hd.comp
    huniq hd.quat hT (noQ8C2_A6 hsh) (sylow_map_le K R) (sylow_map_isPGroup K R)
    (f := ((f0 : ↥K) : G)) (g := ((g0 : ↥K) : G)) ⟨f0, f0.2, rfl⟩ ⟨g0, g0.2, rfl⟩ hf2 hfg
  exact false_of_haut_of_noncentral hnc hS₁C hS₁2 htS hmax haut

theorem noLocalA6Outer_of_tables
    (hComp : ComponentList) (hP : PumpUpData) : NoLocalA6Outer :=
  fun G _ _ hH t K c hd hsh _ => noLocalA6_of_tables hComp hP G hH t K c hd hsh

end CFSG.GH74.E2
