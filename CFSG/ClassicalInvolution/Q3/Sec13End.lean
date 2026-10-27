module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpEnd
public import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

@[expose] def EndBranchS4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), EndHyp Ω →
    ∀ W ∈ WSet Ω, MuIsoS4 Ω W → False

@[expose] def EndBranchWyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), EndHyp Ω →
    ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W → False

theorem EndHyp.false_of_muIsoS3' {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hS3 : MuIsoS3 Ω W) : False :=
  h.false_of_muIsoS3 h.perp9 hW hS3

theorem dLeafEnd_three_of_branches (hS4 : EndBranchS4)
    (hWyl : EndBranchWyl) (IH : ℕ → Prop) : DLeafEnd 3 IH := by
  intro G _ _ Ω hc hZ hdisc hstar hmu
  have h := EndHyp.ofDCex hc hZ hdisc hstar hmu
  obtain ⟨K, hK, -⟩ := h.exists_ne
  obtain ⟨S, hKS⟩ := (h.thmD.two K hK).exists_le_sylow
  obtain ⟨η, hη, -, -, -⟩ := h.exists_wSet_of_le hK S hKS
  have hW : (⨆ V ∈ η, V : Subgroup G) ∈ WSet Ω := ⟨η, hη, rfl⟩
  rcases hmu _ hW with hS3 | hS4' | hWyl'
  · exact h.false_of_muIsoS3' hW hS3
  · exact hS4 G Ω h _ hW hS4'
  · exact hWyl G Ω h _ hW hWyl'

end CFSG.ClassicalInvolution.Q3.Sec13
