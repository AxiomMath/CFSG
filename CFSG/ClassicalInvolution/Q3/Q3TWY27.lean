module

public import CFSG.ClassicalInvolution.Q3.Q3TWY26
public import CFSG.ClassicalInvolution.Q3.Q3TWY23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local macro "nd_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.DAdj, edgeD]; done)
    | (simp [DNodes3.DAdj, edgeD]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


structure ChainDT3 (u : ℕ) (Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1
    Nat.prime_three).K) : Prop where
  dist : ∀ a b, a + 1 < b → b ≤ u + 1 → ∀ i j,
    IsFundamental (quadOdd (u + 5) 𝔽₃) ((Rz (a + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) i →
    IsFundamental (quadOdd (u + 5) 𝔽₃) ((Rz (b + 2)).map (spinAction (quadOdd (u + 5) 𝔽₃))) j →
      i ≠ j
  twin : ∀ i j,
    IsFundamental (quadOdd (u + 5) 𝔽₃) ((Rz (u + 3)).map (spinAction (quadOdd (u + 5) 𝔽₃))) i →
    IsFundamental (quadOdd (u + 5) 𝔽₃) ((Rz (u + 4)).map (spinAction (quadOdd (u + 5) 𝔽₃))) j →
      i = j

section Cases

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {M : Subgroup G}

theorem hdt_five3 (c : TCtx3 .POmegaOdd (0 + 5) Ω K z) (nd : DNodes3 (0 + 5) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (hMz : M ∈ centralizingMembers Ω {z})
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (0 + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (0 + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM) : ChainDT3 0 Rz := by
  have cq := centralQuot3_odd (m := 0 + 5) (by omega)
  have hfr : Module.finrank 𝔽₃ (Fin (0 + 5) ⊕ Fin (0 + 5) ⊕ Unit → 𝔽₃) = 11 := by
    rw [finrank_odd]
  refine ⟨fun a b hab hb => absurd hb (by omega), ?_⟩
  exact chain_twin_five3 hfr cq (R0 := Rz 2) (R1 := Rz 3) (Rtw := Rz 4) (RM := RzM)
    (hch.fund 2 (by omega) (by omega)) (hch.fund 3 (by omega) (by omega))
    (hch.fund 4 (by omega) (by omega)) hch.fundM
    (hch.adj h0 (a := 2) (b := 3) (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (hch.adj h0 (a := 2) (b := 4) (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (hch.comm h0 (a := 3) (b := 4) (by omega) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (a := ⟨3, by omega⟩) (b := ⟨4, by omega⟩)
        (Fin.ne_of_val_ne (by nd_idx)) (by nd_idx)))
    (hch.commM h0 hMz (a := 2) (by omega) (by omega))
    (hch.commM h0 hMz (a := 3) (by omega) (by omega))
    (hch.commM h0 hMz (a := 4) (by omega) (by omega))

theorem hdt_ge7 {u : ℕ} (hu : 2 ≤ u) (c : TCtx3 .POmegaOdd (u + 5) Ω K z)
    (nd : DNodes3 (u + 5) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K)
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM) : ChainDT3 u Rz := by
  obtain ⟨u', rfl⟩ : ∃ u', u = u' + 2 := ⟨u - 2, by omega⟩
  have cq := centralQuot3_odd (m := u' + 2 + 5) (by omega)
  have hdim : 9 ≤ Module.finrank 𝔽₃ (Fin (u' + 2 + 5) ⊕ Fin (u' + 2 + 5) ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
    omega
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen3 (u := u') hdim cq
    (R := fun a => Rz (a + 2)) (Rtw := Rz (u' + 2 + 4))
    (fun a ha => hch.fund (a + 2) (by omega) (by omega)) (hch.fund _ (by omega) (by omega))
    (fun a ha => hch.adj h0 (a := a + 2) (b := a + 3) (by omega) (by omega) (by omega)
      (by omega) (by nd_idx))
    (fun a b hab hb => hch.comm h0 (a := a + 2) (b := b + 2) (by omega) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (a := ⟨a + 2, by omega⟩) (b := ⟨b + 2, by omega⟩)
        (Fin.ne_of_val_ne (by nd_idx)) (by nd_idx)))
    (hch.adj h0 (a := u' + 4) (b := u' + 2 + 4) (by omega) (by omega) (by omega) (by omega)
      (by nd_idx))
    (fun a ha => hch.comm h0 (a := a + 2) (b := u' + 2 + 4) (by omega) (by omega) (by omega)
      (by omega) (nd.commutes_of_not_adj (a := ⟨a + 2, by omega⟩) (b := ⟨u' + 2 + 4, by omega⟩)
        (Fin.ne_of_val_ne (by nd_idx)) (by nd_idx)))
    (hch.comm h0 (a := u' + 3 + 2) (b := u' + 2 + 4) (by omega) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (a := ⟨u' + 3 + 2, by omega⟩) (b := ⟨u' + 2 + 4, by omega⟩)
        (Fin.ne_of_val_ne (by nd_idx)) (by nd_idx)))
  exact ⟨hdist, htwin⟩

end Cases

end CFSG.ClassicalInvolution.Q3.Q3TWY
