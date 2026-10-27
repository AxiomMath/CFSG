module

public import CFSG.ClassicalInvolution.Q3.Q3TWY25
public import CFSG.ClassicalInvolution.Q3.Q3TWY14

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


section Chain

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G} {u : ℕ}
  {M : Subgroup G}

theorem node_commutes_K3 (nd : DNodes3 (u + 5) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) {a : ℕ}
    (ha : a < u + 5) (h2 : 2 ≤ a) : Commutes K (nd.J ⟨a, ha⟩) := by
  rw [← h0]
  exact nd.commutes_of_not_adj (Fin.ne_of_val_ne (by nd_idx)) (by nd_idx)

theorem node_mem_z3 (c : TCtx3 .POmegaOdd (u + 5) Ω K z) (nd : DNodes3 (u + 5) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) {a : ℕ} (ha : a < u + 5) (h2 : 2 ≤ a) :
    nd.J ⟨a, ha⟩ ∈ centralizingMembers Ω {z} :=
  mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
    (commutes_symm (node_commutes_K3 nd h0 ha h2))

theorem node_commutes_β3 (nd : DNodes3 (u + 5) Ω M) {β : Subgroup G}
    (h1 : nd.J ⟨1, by omega⟩ = β) {a : ℕ} (ha : a < u + 5) (h3 : 3 ≤ a) :
    Commutes β (nd.J ⟨a, ha⟩) := by
  rw [← h1]
  exact nd.commutes_of_not_adj (Fin.ne_of_val_ne (by nd_idx)) (by nd_idx)

theorem exists_nb_node3 {a : ℕ} (ha : a < u + 5) (h2 : 2 ≤ a) :
    ∃ b, ∃ hb : b < u + 5, 2 ≤ b ∧ DNodes3.DAdj (⟨a, ha⟩ : Fin (u + 5)) ⟨b, hb⟩ := by
  by_cases h : a ≤ u + 2
  · exact ⟨a + 1, by omega, by omega, by nd_idx⟩
  · exact ⟨u + 2, by omega, by omega, by nd_idx⟩

structure LayerChain3 (c : TCtx3 .POmegaOdd (u + 5) Ω K z) (nd : DNodes3 (u + 5) Ω M)
    (Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K)
    (RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K) : Prop where
  fund : ∀ a, a < u + 5 → 2 ≤ a →
    Rz a ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).D
  img : ∀ a (h : a < u + 5), 2 ≤ a → locImg Ω z (nd.J ⟨a, h⟩) = (Rz a).map c.d.ψ
  fundM : RzM ∈ fundamentalSubgroups .POmegaOdd
    (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).D
  imgM : locImg Ω z M = RzM.map c.d.ψ

theorem exists_layerChain3 (c : TCtx3 .POmegaOdd (u + 5) Ω K z) (nd : DNodes3 (u + 5) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (hMz : M ∈ centralizingMembers Ω {z}) (hMK : M ≠ K)
    (hMQ : ¬ locImg Ω z M ≤ c.d.Q₁) :
    ∃ (Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K)
      (RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K),
      LayerChain3 c nd Rz RzM := by
  classical
  have hlayer : ∀ a (h : a < u + 5), 2 ≤ a →
      nd.J ⟨a, h⟩ ≠ K ∧ ¬ locImg Ω z (nd.J ⟨a, h⟩) ≤ c.d.Q₁ := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := exists_nb_node3 (u := u) h ha
    exact c.ne_and_not_le_Q₁3 (node_mem_z3 c nd h0 h ha) (node_mem_z3 c nd h0 hb hb2)
      (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K,
      ∀ (h : a < u + 5), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaOdd
          (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < u + 5 ∧ 2 ≤ a
    · obtain ⟨R, hR, hLR⟩ := c.exists_fund_of_ne (node_mem_z3 c nd h0 hv.1 hv.2)
        (hlayer a hv.1 hv.2).1 (hlayer a hv.1 hv.2).2
      exact ⟨R, fun _ _ => ⟨hR, hLR⟩⟩
    · exact ⟨⊥, fun h ha => absurd ⟨h, ha⟩ hv⟩
  choose Rz hRz using hexRz
  obtain ⟨RzM, hRzM, hMR⟩ := c.exists_fund_of_ne hMz hMK hMQ
  exact ⟨Rz, RzM, fun a h ha => (hRz a h ha).1, fun a h ha => (hRz a h ha).2, hRzM, hMR⟩

variable {c : TCtx3 .POmegaOdd (u + 5) Ω K z} {nd : DNodes3 (u + 5) Ω M}
  {Rz : ℕ → Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}
  {RzM : Subgroup (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K}

theorem LayerChain3.comm (hch : LayerChain3 c nd Rz RzM) (h0 : nd.J ⟨0, by omega⟩ = K) {a b : ℕ}
    (ha : a < u + 5) (hb : b < u + 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (h : Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩)) : Commutes (Rz a) (Rz b) :=
  (c.commutes_iff_fund (node_mem_z3 c nd h0 ha ha2) (node_mem_z3 c nd h0 hb hb2)
    (hch.fund a ha ha2) (hch.img a ha ha2) (hch.img b hb hb2)).mp h

theorem LayerChain3.commM (hch : LayerChain3 c nd Rz RzM) (h0 : nd.J ⟨0, by omega⟩ = K)
    (hMz : M ∈ centralizingMembers Ω {z}) {a : ℕ} (ha : a < u + 5) (ha2 : 2 ≤ a) :
    Commutes RzM (Rz a) :=
  (c.commutes_iff_fund hMz (node_mem_z3 c nd h0 ha ha2) hch.fundM hch.imgM (hch.img a ha ha2)).mp
    (nd.commK _)

theorem LayerChain3.adj (hch : LayerChain3 c nd Rz RzM) (h0 : nd.J ⟨0, by omega⟩ = K) {a b : ℕ}
    (ha : a < u + 5) (hb : b < u + 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hab : DNodes3.DAdj (⟨a, ha⟩ : Fin (u + 5)) ⟨b, hb⟩) :
    ModelAdj (Subgroup.center (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K)
      (Rz a) (Rz b) :=
  modelAdj_of_adj3 c (node_mem_z3 c nd h0 ha ha2) (node_mem_z3 c nd h0 hb hb2)
    (hch.fund a ha ha2) (hch.fund b hb hb2) (hch.img a ha ha2) (hch.img b hb hb2) (nd.cl _)
    (nd.cl _) (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab) (nd.commute_w two_ne_zero_gf3 _ _)
    (nd.conjSub_w two_ne_zero_gf3 hab)

theorem LayerChain3.lin (hch : LayerChain3 c nd Rz RzM) (h0 : nd.J ⟨0, by omega⟩ = K) {a b : ℕ}
    (ha : a < u + 5) (hb : b < u + 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hab : DNodes3.DAdj (⟨a, ha⟩ : Fin (u + 5)) ⟨b, hb⟩) :
    ∃ W, LinearBlockStandardPair 𝔽₃ W (Rz a) (Rz b) := by
  have hadm : StatedLieAdmissible .POmegaOdd (u + 5) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, by norm_num⟩
  have : Finite (modelUniv .POmegaOdd (u + 5) 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
  obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1
    (node_mem_z3 c nd h0 ha ha2) (node_mem_z3 c nd h0 hb hb2) hW₁
  rw [hch.img a ha ha2, hch.img b hb hb2] at hW₂
  exact exists_lin_of_map3' (not_three_dvd_card_center' c.hY.cop) c.d.ψ c.d.ker_le
    (c.hY.pow3 _ (hch.fund a ha ha2)) (c.hY.pow3 _ (hch.fund b hb hb2)) ⟨W₂, hW₂⟩

theorem LayerChain3.ne (hch : LayerChain3 c nd Rz RzM) (h0 : nd.J ⟨0, by omega⟩ = K) {a b : ℕ}
    (ha : a < u + 5) (hb : b < u + 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hab : a ≠ b) :
    Rz a ≠ Rz b := fun h =>
  nd.ne_J (Fin.ne_of_val_ne hab) (c.eq_of_locImg_eq (node_mem_z3 c nd h0 ha ha2)
    (node_mem_z3 c nd h0 hb hb2) (by rw [hch.img a ha ha2, hch.img b hb hb2, h]))

end Chain

end CFSG.ClassicalInvolution.Q3.Q3TWY
