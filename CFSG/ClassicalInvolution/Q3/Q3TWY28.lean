module

public import CFSG.ClassicalInvolution.Q3.Q3TWY27

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Timmesfeld
  CFSG.ClassicalInvolution.RouteD.TWE.B6
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


section Six

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {M : Subgroup G}

theorem hdt_six3 (c : TCtx3 .POmegaOdd (1 + 5) Ω K z) (nd : DNodes3 (1 + 5) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K)
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (1 + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (1 + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM) {N : Subgroup G} (hNΩ : N ∈ Ω)
    (hNc : ∀ a : Fin (1 + 5), a.val < 1 + 3 → Commutes N (nd.J a))
    (hN4 : ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨1 + 3, by omega⟩) N)
    (hN5 : ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨1 + 4, by omega⟩) N) : ChainDT3 1 Rz := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have cq := centralQuot3_odd (m := 1 + 5) (by omega)
  have hdimV : 9 ≤ Module.finrank 𝔽₃ (Fin (1 + 5) ⊕ Fin (1 + 5) ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
    omega
  obtain ⟨wN, hwN⟩ := c.hΩ.classical N hNΩ
  have hNz : N ∈ centralizingMembers Ω {z} := by
    have := hNc ⟨0, by omega⟩ (by norm_num)
    rw [h0] at this
    exact mem_centralizingMembers_of_commutes hNΩ c.hz.mem this
  obtain ⟨W4, hW4⟩ := hN4
  obtain ⟨W5, hW5⟩ := hN5
  have hn4N : ¬ Commutes N (nd.J ⟨4, by omega⟩) := fun h =>
    not_commutes_of_linearBlockStandardPair hW4 (commutes_symm h)
  have hN4ne : N ≠ nd.J ⟨4, by omega⟩ := fun h => ne_of_linearBlockStandardPair hW4 h.symm
  have hn5N : ¬ Commutes N (nd.J ⟨5, by omega⟩) := fun h =>
    not_commutes_of_linearBlockStandardPair hW5 (commutes_symm h)
  have hN5ne : N ≠ nd.J ⟨5, by omega⟩ := fun h => ne_of_linearBlockStandardPair hW5 h.symm
  have hN2ne : N ≠ nd.J ⟨2, by omega⟩ := fun h => by
    have := hNc ⟨2, by omega⟩ (by norm_num)
    rw [← h] at this
    exact not_commutes_self3 hwN this
  obtain ⟨hNK, hNQ⟩ := c.ne_and_not_le_Q₁3 hNz (node_mem_z3 c nd h0 (a := 4) (by omega) (by omega))
    hN4ne hn4N
  obtain ⟨RN, hRN, hNR⟩ := c.exists_fund_of_ne hNz hNK hNQ
  obtain ⟨ic, hic⟩ := cq.map_mem _ (hch.fund 3 (by omega) (by omega))
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ (hch.fund 2 (by omega) (by omega))
  obtain ⟨i₂, hi₂⟩ := cq.map_mem _ (hch.fund 4 (by omega) (by omega))
  obtain ⟨i₃, hi₃⟩ := cq.map_mem _ (hch.fund 5 (by omega) (by omega))
  obtain ⟨iS, hiS⟩ := cq.map_mem _ hRN
  have cm : ∀ a b (ha : a < 1 + 5) (hb : b < 1 + 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b), a ≠ b →
      ¬ DNodes3.DAdj (⟨a, ha⟩ : Fin (1 + 5)) ⟨b, hb⟩ →
      Commutes ((Rz a).map (spinAction (quadOdd (1 + 5) 𝔽₃)))
        ((Rz b).map (spinAction (quadOdd (1 + 5) 𝔽₃))) := fun a b ha hb ha2 hb2 hab hn =>
    (cq.commutes_iff (hch.fund a ha ha2)).mpr (hch.comm h0 ha hb ha2 hb2
      (nd.commutes_of_not_adj (Fin.ne_of_val_ne hab) hn))
  have ad : ∀ a b (ha : a < 1 + 5) (hb : b < 1 + 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.DAdj (⟨a, ha⟩ : Fin (1 + 5)) ⟨b, hb⟩ →
      ModelAdj (scalars 𝔽₃ (Fin (1 + 5) ⊕ Fin (1 + 5) ⊕ Unit → 𝔽₃))
        ((Rz a).map (spinAction (quadOdd (1 + 5) 𝔽₃)))
        ((Rz b).map (spinAction (quadOdd (1 + 5) 𝔽₃))) := fun a b ha hb ha2 hb2 hab =>
    cq.modelAdj (hch.fund a ha ha2) (hch.fund b hb hb2) (hch.adj h0 ha hb ha2 hb2 hab)
  have hNne : ∀ a (ha : a < 1 + 5) (ha2 : 2 ≤ a), N ≠ nd.J ⟨a, ha⟩ →
      RN.map (spinAction (quadOdd (1 + 5) 𝔽₃)) ≠
        (Rz a).map (spinAction (quadOdd (1 + 5) 𝔽₃)) := fun a ha ha2 hne e =>
    hne (c.eq_of_locImg_eq hNz (node_mem_z3 c nd h0 ha ha2)
      (by rw [hNR, hch.img a ha ha2, cq.map_inj hRN (hch.fund a ha ha2) e]))
  have hnc : ∀ a (ha : a < 1 + 5) (ha2 : 2 ≤ a), ¬ Commutes N (nd.J ⟨a, ha⟩) →
      ¬ Commutes (RN.map (spinAction (quadOdd (1 + 5) 𝔽₃)))
        ((Rz a).map (spinAction (quadOdd (1 + 5) 𝔽₃))) := fun a ha ha2 hcn h =>
    hcn ((c.commutes_iff_fund hNz (node_mem_z3 c nd h0 ha ha2) hRN hNR
      (hch.img a ha ha2)).mpr ((cq.commutes_iff hRN).mp h))
  have hcN2 : Commutes (RN.map (spinAction (quadOdd (1 + 5) 𝔽₃)))
      ((Rz 2).map (spinAction (quadOdd (1 + 5) 𝔽₃))) :=
    (cq.commutes_iff hRN).mpr ((c.commutes_iff_fund hNz
      (node_mem_z3 c nd h0 (a := 2) (by omega) (by omega)) hRN hNR
      (hch.img 2 (by omega) (by omega))).mp (hNc ⟨2, by omega⟩ (by norm_num)))
  have hI : ∀ a (ha : a < 1 + 5) (ha2 : 2 ≤ a), Commute wN (nd.w ⟨a, ha⟩) →
      ModelInvComm (scalars 𝔽₃ (Fin (1 + 5) ⊕ Fin (1 + 5) ⊕ Unit → 𝔽₃))
        (RN.map (spinAction (quadOdd (1 + 5) 𝔽₃)))
        ((Rz a).map (spinAction (quadOdd (1 + 5) 𝔽₃))) := fun a ha ha2 hc => by
    obtain ⟨r, r', hr, hr', hcen, -, -⟩ := c.modelInvComm3 hNz
      (node_mem_z3 c nd h0 ha ha2) hRN (hch.fund a ha ha2) hNR (hch.img a ha ha2) hwN
      (nd.cl _) hc
    exact cq.modelInvComm hRN (hch.fund a ha ha2) ⟨r, r', hr, hr', hcen⟩
  have hcw2 : Commute wN (nd.w ⟨2, by omega⟩) := hNc ⟨2, by omega⟩ (by norm_num) _ hwN.mem _
    (nd.cl _).mem
  have hcw4 : Commute wN (nd.w ⟨4, by omega⟩) :=
    (standardPair_involutions_commute h2 hW4 (nd.cl _).mem hwN.mem (nd.cl _).orderOf_eq_two
      hwN.orderOf_eq_two).symm
  have hcw5 : Commute wN (nd.w ⟨5, by omega⟩) :=
    (standardPair_involutions_commute h2 hW5 (nd.cl _).mem hwN.mem (nd.cl _).orderOf_eq_two
      hwN.orderOf_eq_two).symm
  obtain ⟨hn21, hn31, h32⟩ := star_twin_of_distinguish hodd hdimV hic hi₁ hi₂ hi₃ hiS
    (ad 3 2 (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (ad 3 4 (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (ad 3 5 (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (cm 2 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (cm 2 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (cm 4 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by nd_idx))
    (hNne 2 (by omega) (by omega) hN2ne) (hNne 4 (by omega) (by omega) hN4ne)
    (hNne 5 (by omega) (by omega) hN5ne) (hI 2 (by omega) (by omega) hcw2)
    (hI 4 (by omega) (by omega) hcw4) (hI 5 (by omega) (by omega) hcw5) hcN2
    (hnc 4 (by omega) (by omega) hn4N) (hnc 5 (by omega) (by omega) hn5N)
  refine ⟨fun a b hab hb i j hi hj => ?_, fun i j hi hj => ?_⟩
  · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
    have e1 := IsFundamental.involution_unique hodd hi hi₁
    have e2 := IsFundamental.involution_unique hodd hj hi₂
    rw [e1, e2]
    exact hn21.symm
  · have e1 := IsFundamental.involution_unique hodd hi hi₂
    have e2 := IsFundamental.involution_unique hodd hj hi₃
    rw [e1, e2, h32]

end Six

section Dispatch

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {M : Subgroup G}

theorem hdt_odd3 {u : ℕ} (c : TCtx3 .POmegaOdd (u + 5) Ω K z) (nd : DNodes3 (u + 5) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (hMz : M ∈ centralizingMembers Ω {z})
    {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    {RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
    (hch : LayerChain3 c nd Rz RzM) {N : Subgroup G} (hNΩ : N ∈ Ω)
    (hNc : ∀ a : Fin (u + 5), a.val < u + 3 → Commutes N (nd.J a))
    (hN4 : ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 3, by omega⟩) N)
    (hN5 : ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J ⟨u + 4, by omega⟩) N) : ChainDT3 u Rz := by
  by_cases hu : 2 ≤ u
  · exact hdt_ge7 hu c nd h0 hch
  · obtain rfl | rfl : u = 0 ∨ u = 1 := by omega
    · exact hdt_five3 c nd h0 hMz hch
    · exact hdt_six3 c nd h0 hch hNΩ hNc hN4 hN5

end Dispatch

end CFSG.ClassicalInvolution.Q3.Q3TWY
