module

public import CFSG.ClassicalInvolution.Phan.PhanP19Perp
public import CFSG.ClassicalInvolution.Phan.PhanP20Common
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanG
open scoped MatrixGroups

section Graph

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G}

theorem ptGraph_adj_of_mul {g h y ρ z : G} (hy : y ∈ parab S {1, 2, 3}) (hρ : ρ ∈ parab S {0})
    (hz : z ∈ parab S {1, 2, 3}) (hgh : g⁻¹ * h = y * ρ * z)
    (hne : (g : G ⧸ parab S {1, 2, 3}) ≠ (h : G ⧸ parab S {1, 2, 3})) :
    (ptGraph S).Adj (g : G ⧸ parab S {1, 2, 3}) (h : G ⧸ parab S {1, 2, 3}) := by
  refine ⟨hne, ((g * y : G) : G ⧸ torusSub S), ((g * y * ρ : G) : G ⧸ torusSub S), ?_, ?_, ?_⟩
  · rw [ptMap_mk]
    refine QuotientGroup.eq.2 ?_
    simpa using inv_mem hy
  · rw [ptMap_mk]
    refine QuotientGroup.eq.2 ?_
    have : (g * y * ρ)⁻¹ * h = z := by
      have : h = g * (y * ρ * z) := by rw [← hgh]; group
      rw [this]; group
    rw [this]
    exact hz
  · rw [phanSystem_adj_mk]
    simpa [mul_assoc] using hρ


theorem edist_le_two_of {V : Type} {Γ : SimpleGraph V} {x z y : V} (h1 : x = z ∨ Γ.Adj x z)
    (h2 : z = y ∨ Γ.Adj z y) : Γ.edist x y ≤ 2 := by
  have e1 : Γ.edist x z ≤ 1 := by
    rcases h1 with rfl | h
    · simp
    · exact (SimpleGraph.edist_eq_one_iff_adj.2 h).le
  have e2 : Γ.edist z y ≤ 1 := by
    rcases h2 with rfl | h
    · simp
    · exact (SimpleGraph.edist_eq_one_iff_adj.2 h).le
  calc Γ.edist x y ≤ Γ.edist x z + Γ.edist z y := SimpleGraph.edist_triangle
    _ ≤ 1 + 1 := add_le_add e1 e2
    _ = 2 := by norm_num

end Graph

section Diam

variable {p e : ℕ} [Fact p.Prime]

theorem StdModel.ediam_le_two (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    (ptGraph M.S).ediam ≤ 2 := by
  have h2 := two_ne_zero_gf hp2 e
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  rw [SimpleGraph.ediam_le_iff]
  intro u v
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective v
  obtain ⟨h, hh1, hh2⟩ := exists_common_perp (ε := M.ε) (hε := M.hε) (h4 := M.h4) h2 hodd M.nonsq
    (g₁⁻¹ * g₂)
  refine edist_le_two_of (z := ((g₁ * h : _) : _ ⧸ parab M.S {1, 2, 3})) ?_ ?_
  · by_cases hne : ((g₁ : _) : _ ⧸ parab M.S {1, 2, 3}) = ((g₁ * h : _) : _)
    · exact Or.inl hne
    · obtain ⟨y, hy, ρ, hρ, z, hz, hyρz⟩ := mem_mul_of_perp M hp2 hq hh1
      exact Or.inr (ptGraph_adj_of_mul hy hρ hz (by rw [inv_mul_cancel_left]; exact hyρz) hne)
  · by_cases hne : ((g₁ * h : _) : _ ⧸ parab M.S {1, 2, 3}) = ((g₂ : _) : _)
    · exact Or.inl hne
    · have hperp : ∀ a ∈ planeA M.ε M.hε M.h4, ∀ a' ∈ planeA M.ε M.hε M.h4,
          polar (quadPlus 4 (GaloisField p e))
            (spinAction (quadPlus 4 (GaloisField p e)) ((g₁⁻¹ * g₂)⁻¹ * h) a) a' = 0 := by
        intro a ha a' ha'
        have := hh2 a ha a' ha'
        rw [map_mul, LinearEquiv.mul_apply, ← polar_spinAction (quadPlus 4 (GaloisField p e))
          (g₁⁻¹ * g₂), ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        simpa using this
      obtain ⟨y, hy, ρ, hρ, z, hz, hyρz⟩ := mem_mul_of_perp M hp2 hq hperp
      refine Or.inr (ptGraph_adj_of_mul hy hρ hz ?_ (Ne.symm hne)).symm
      rw [← hyρz]
      group

theorem StdModel.connected (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    (ptGraph M.S).Connected := by
  have hd := M.ediam_le_two hp2 hq
  refine (SimpleGraph.connected_iff _).2 ⟨fun u v => ?_,
    ⟨((1 : spinGroup (quadPlus 4 (GaloisField p e))) : _ ⧸ parab M.S {1, 2, 3})⟩⟩
  refine SimpleGraph.reachable_of_edist_ne_top ?_
  exact ne_top_of_le_ne_top (by simp) ((SimpleGraph.edist_le_ediam).trans hd)

end Diam

end CFSG.ClassicalInvolution.PhanP
