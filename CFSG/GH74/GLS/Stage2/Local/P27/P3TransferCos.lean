module

public import CFSG.GH74.GLS.Stage2.Local.P27.P3Transfer

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem not_mem_commutator_of_sep {X P M : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P X) (hMP : M ≤ P) (hM : M.relIndex P = 2)
    {s : G} (hsP : s ∈ P) (hsM : s ∉ M) (hs2 : s * s = 1)
    (hsep : ∀ g ∈ X, g⁻¹ * s * g ∈ P → g⁻¹ * s * g ∉ M) : s ∉ ⁅X, X⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPX : P ≤ X := hP.le
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP
  obtain ⟨-, hP2, hPidx⟩ := hP
  obtain ⟨N, hN, hcyc, -, hsN⟩ := transfer_normal_of_sep (X := ↥X) (P := P.subgroupOf X)
    (Q := M.subgroupOf X) hP2.comap_subtype hPidx (fun y hy => hMP hy)
    (by rw [Subgroup.relIndex_subgroupOf hPX]; exact hM)
    (s := ⟨s, hPX hsP⟩) hsP hsM (Subtype.ext hs2)
    (fun g hg => hsep (g : G) g.2 hg)
  intro hs
  apply hsN
  have h1 : (⟨s, hPX hsP⟩ : ↥X) ∈ commutator ↥X := by
    have h2 : s ∈ (commutator ↥X).map X.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hs
    obtain ⟨y', hy', hyy⟩ := h2
    have : y' = ⟨s, hPX hsP⟩ := Subtype.ext hyy
    rwa [← this]
  exact commutator_le_of_isCyclic_quotient hcyc h1

end Ambient

end CFSG.GH74.GLS.Stage2.Local.P27
