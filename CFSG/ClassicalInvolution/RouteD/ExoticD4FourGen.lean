module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {a : ℕ} {K : Subgroup G}
  {z : G}

theorem eq_top_of_outerGen_le (S : RouteDSetup p f K z)
    (hloc : LocalShapeT p f a .POmegaPlus 4 (conjClass K) z) {N M : Subgroup G}
    (hN : N ∈ conjClass K) (hM : M ∈ outerSet (conjClass K) N) {H : Subgroup G}
    (hNH : outerGen (conjClass K) N ≤ H) (hMH : outerGen (conjClass K) M ≤ H) : H = ⊤ := by
  set Ω := conjClass K with hΩdef
  let 𝔖 : Set (Subgroup G) := {J | J ∈ Ω ∧ outerGen Ω J ≤ H ∧
    ∃ E ∈ outerSet Ω J, outerGen Ω E ≤ H}
  have hsub : 𝔖 ⊆ Ω := fun J hJ => hJ.1
  have hne : 𝔖.Nonempty := ⟨N, hN, hNH, M, hM, hMH⟩
  have hcl : ∀ J ∈ 𝔖, ∀ L ∈ Ω, L ≠ J → Commutes J L → L ∈ 𝔖 := by
    rintro J ⟨hJ, hJH, E, hE, hEH⟩ L hL - hc
    by_cases htw : cnbhd Ω L = cnbhd Ω J
    · refine ⟨hL, ?_, E, ?_, hEH⟩
      · rw [outerGen_eq_of_cnbhd_eq htw]
        exact hJH
      · rw [outerSet_eq_of_cnbhd_eq htw]
        exact hE
    · have hLout : L ∈ outerSet Ω J := ⟨⟨hL, Or.inr hc.symm⟩, htw⟩
      obtain ⟨y, hy, hyE⟩ := exists_conj_of_shape S hloc hJ hE hLout
      have hyH : y ∈ H := hJH hy
      refine ⟨hL, ?_, J, mem_outerSet_symm hJ hLout, hJH⟩
      rw [← hyE, outerGen_conj S.inClass.conjInvariant]
      have := conjSub_mono (n := y) hEH
      rwa [conjSub_eq_self_of_mem hyH] at this
  have hall : Ω ⊆ 𝔖 := subset_of_adj_closed S.conn hsub hne hcl
  rw [eq_top_iff, ← S.inClass.generated]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨-, -, E, hE, hEH⟩ := hall hL
  exact (le_outerGen (mem_outerSet_symm hL hE)).trans hEH

end CFSG.ClassicalInvolution.RouteD.Exotic
