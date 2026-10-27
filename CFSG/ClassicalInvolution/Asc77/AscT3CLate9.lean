module

public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9D
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate9B

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20.late_swap_not_sq_X (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (h8 : 8 < Nat.card R) {u : G} (hu : u ∈ (S : Subgroup G)) (huK : conjSub u K = K')
    (hX : u * u ∈ sec20X (CoreAssembly.conjClass K) z K K') : False := by
  obtain ⟨σ, hσ, hσK, hσ2⟩ := d.late_exists_sq_W c3 hu huK hX
  exact d.late_no_sq_W h8 hσ hσK hσ2

theorem Std20.late_nine_three (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (h8 : 8 < Nat.card R) : ∀ u ∈ (S : Subgroup G),
      u * u ∈ sec20X (CoreAssembly.conjClass K) z K K' → u ∈ Subgroup.normalizer (K : Set G) := by
  intro u hu hX
  rcases d.late_conj_K (d.hSz hu) with h | h
  · exact mem_normalizer_iff_conjSub_eq.mpr h
  · exact (d.late_swap_not_sq_X c3 h8 hu h hX).elim

theorem Std20.late_SX_le_N_K (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (h8 : 8 < Nat.card R) :
    (S : Subgroup G) ⊓ sec20X (CoreAssembly.conjClass K) z K K' ≤
      Subgroup.normalizer (K : Set G) := fun u hu =>
  d.late_nine_three c3 h8 u hu.1 (Subgroup.mul_mem _ hu.2 hu.2)

theorem Std20.late_not_le_X (d : Std20 p f K K' J S R R' W V z t) (c3 : Concl20_3 K K' V z)
    (h8 : 8 < Nat.card R) :
    ∃ s ∈ (S : Subgroup G), s ∉ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  refine ⟨u, hu, fun hX => d.late_swap_not_sq_X c3 h8 hu huK (Subgroup.mul_mem _ hX hX)⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
