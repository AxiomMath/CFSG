module

public import CFSG.ClassicalInvolution.RouteD.TWZLayer
public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance

set_option linter.unusedSectionVars false

section Closure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem eq_top_of_closure {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hconn : DeltaConnected Ω) {H : Subgroup G} {K J : Subgroup G} (hK : K ∈ Ω)
    (hKH : K ≤ H) (hJH : J ≤ H)
    (hneighK : ∀ L ∈ Ω, L ≠ K → Commutes K L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J)
    (hneighJ : ∀ L ∈ Ω, L ≠ J → Commutes J L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J) : H = ⊤ := by
  set 𝔖 : Set (Subgroup G) :=
    {L | L ∈ Ω ∧ ∃ h ∈ H, L = conjSub h K ∨ L = conjSub h J} with h𝔖
  have hsub : 𝔖 ⊆ Ω := fun L hL => hL.1
  have hne : 𝔖.Nonempty := ⟨K, hK, 1, H.one_mem, Or.inl (conjSub_one K).symm⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨hNΩ, h, hhH, hNh⟩ L hL hLN hc
    have hL' : conjSub h⁻¹ L ∈ Ω := hΩ.conjInvariant _ L hL
    have hLeq : L = conjSub h (conjSub h⁻¹ L) := (conjSub_conjSub_inv h L).symm
    refine ⟨hL, ?_⟩
    have hcc : Commutes (conjSub h⁻¹ N) (conjSub h⁻¹ L) := (commutes_conjSub_iff h⁻¹).mpr hc
    rcases hNh with hN | hN
    · rw [hN, conjSub_inv_conjSub] at hcc
      have hne' : conjSub h⁻¹ L ≠ K := fun hEq => hLN (by rw [hLeq, hEq, hN])
      obtain ⟨y, hy, hyeq⟩ := hneighK _ hL' hne' hcc
      refine ⟨h * y, H.mul_mem hhH hy, ?_⟩
      rcases hyeq with hyeq | hyeq
      · left
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y K) := by rw [hyeq]
          _ = conjSub (h * y) K := (conjSub_mul h y K).symm
      · right
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y J) := by rw [hyeq]
          _ = conjSub (h * y) J := (conjSub_mul h y J).symm
    · rw [hN, conjSub_inv_conjSub] at hcc
      have hne' : conjSub h⁻¹ L ≠ J := fun hEq => hLN (by rw [hLeq, hEq, hN])
      obtain ⟨y, hy, hyeq⟩ := hneighJ _ hL' hne' hcc
      refine ⟨h * y, H.mul_mem hhH hy, ?_⟩
      rcases hyeq with hyeq | hyeq
      · left
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y K) := by rw [hyeq]
          _ = conjSub (h * y) K := (conjSub_mul h y K).symm
      · right
        calc L = conjSub h (conjSub h⁻¹ L) := hLeq
          _ = conjSub h (conjSub y J) := by rw [hyeq]
          _ = conjSub (h * y) J := (conjSub_mul h y J).symm
  have hall := subset_of_adj_closed hconn hsub hne hcl
  have hle : ∀ L ∈ Ω, L ≤ H := by
    intro L hL
    obtain ⟨-, h, hhH, hLh⟩ := hall hL
    have key : ∀ M : Subgroup G, M ≤ H → conjSub h M ≤ H := by
      intro M hM x hx
      rw [mem_conjSub_iff] at hx
      have h1 := H.mul_mem (H.mul_mem hhH (hM hx)) (H.inv_mem hhH)
      have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rwa [e] at h1
    rcases hLh with hLh | hLh
    · rw [hLh]; exact key K hKH
    · rw [hLh]; exact key J hJH
  refine eq_top_iff.mpr ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun L hL => hle L hL

end Closure

end CFSG.ClassicalInvolution.RouteD.TWZ
