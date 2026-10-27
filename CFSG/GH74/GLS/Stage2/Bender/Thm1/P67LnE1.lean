module

public import CFSG.GH74.GLS.Stage2.OddAut.LinNAut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.Stage2.OddAut

section E1

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem false_of_e1_cop (hn : 3 ≤ n) {r : ℕ} (hcop : Nat.Coprime n r) (hrK : r ∣ Nat.card K - 1)
    {V Z : Subgroup (MulAut (projectiveSL n K))} (h2 : N2Cfg (projectiveSL n K) r V Z)
    (h3 : N3Full (projectiveSL n K) V Z) (hVI : V ≤ linearAutGroup n K) : False := by
  obtain ⟨hr, -, hVe, hVc, -⟩ := id h2
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => by
    have := hVe
    exact setLike_mul_comm hx hy
  have hVe' : ∀ v ∈ V, v ^ r = 1 := fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv
  rw [linearAutGroup_eq_range] at hVI
  obtain ⟨B, hB⟩ := inner_plane_toral_of_coprime hn hr hcop hrK V hVI hVc hVe' hVab
  exact Ln.false_of_toral hn h2 h3 B hB

end E1

end CFSG.GH74.GLS.Stage2.Bender.Thm1
