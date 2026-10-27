module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnAsm

public section

open scoped Pointwise commutatorElement

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP

variable {X : Type*} [Group X]

@[expose] def polB (D : RankTwoSystem X 3) (θ : X ≃* X) : Subgroup ↥(foldFix θ) :=
  D.B.subgroupOf (foldFix θ)

@[expose] def polU (D : RankTwoSystem X 3) (θ : X ≃* X) : Subgroup ↥(foldFix θ) :=
  D.U.subgroupOf (foldFix θ)

theorem mem_polB {D : RankTwoSystem X 3} {θ : X ≃* X} (g : ↥(foldFix θ)) :
    g ∈ polB D θ ↔ (g : X) ∈ D.B := Subgroup.mem_subgroupOf

theorem mem_polU {D : RankTwoSystem X 3} {θ : X ≃* X} (g : ↥(foldFix θ)) :
    g ∈ polU D θ ↔ (g : X) ∈ D.U := Subgroup.mem_subgroupOf

variable {D : RankTwoSystem X 3} {θ : X ≃* X}

theorem polarity_rankOne_data (hθ : D.IsPolarity θ) {c₀ : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀)
    (hc₀f : θ c₀ = c₀)
    (hKC : ∀ k ∈ D.B, θ k = k → (∀ u ∈ D.U, θ u = u → k * u = u * k) → k ∈ D.U) :
    polU D θ ≤ polB D θ ∧
      (∀ b ∈ polB D θ, ∀ u ∈ polU D θ, b * u * b⁻¹ ∈ polU D θ) ∧
      (∀ g : ↥(foldFix θ), g ∈ polB D θ ∨ ∃ b ∈ polB D θ, ∃ u ∈ polU D θ,
        g = b * (⟨c₀, hc₀f⟩ : ↥(foldFix θ)) * u) ∧
      (∀ u ∈ polU D θ, (⟨c₀, hc₀f⟩ : ↥(foldFix θ)) * u * (⟨c₀, hc₀f⟩ : ↥(foldFix θ))⁻¹ ∈ polB D θ →
        u = 1) ∧
      (∀ k ∈ polB D θ, (∀ u ∈ polU D θ, k * u = u * k) → k ∈ polU D θ) := by
  refine ⟨fun g hg => (mem_polB g).2 (D.U_le_B ((mem_polU g).1 hg)), ?_, ?_, ?_, ?_⟩
  · intro b hb u hu
    exact (mem_polU _).2 (D.conj_mem_U_of_mem_B ((mem_polB b).1 hb) ((mem_polU u).1 hu))
  · intro g
    rcases hθ.fixed_mem_B_or_top (mem_foldFix.1 g.2) with hg | hg
    · exact Or.inl ((mem_polB g).2 hg)
    · obtain ⟨b, hb, hbf, u, hu, huf, hgbu⟩ := hθ.top_decomp hc₀ hg hc₀f (mem_foldFix.1 g.2)
      exact Or.inr ⟨⟨b, hbf⟩, (mem_polB _).2 hb, ⟨u, huf⟩, (mem_polU _).2 hu, Subtype.ext hgbu⟩
  · intro u hu h
    exact Subtype.ext (RankTwoSystem.U_meet_top hc₀ ((mem_polU u).1 hu) ((mem_polB _).1 h))
  · intro k hk hcomm
    refine (mem_polU k).2 (hKC k ((mem_polB k).1 hk) (mem_foldFix.1 k.2) fun u hu huf => ?_)
    exact congrArg Subtype.val (hcomm ⟨u, huf⟩ ((mem_polU _).2 hu))

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
