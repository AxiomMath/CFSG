module

public import CFSG.ClassicalInvolution.Q3.Q3TWY14
public import CFSG.ClassicalInvolution.RouteD.GapsFrBNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

structure DNodes3 {G : Type} [Group G] (m : ℕ) (Ω : Set (Subgroup G)) (K : Subgroup G) where
  J : Fin m → Subgroup G
  w : Fin m → G
  mem : ∀ a, J a ∈ Ω
  cl : ∀ a, IsClassicalMember3 (J a) (w a)
  commK : ∀ a, Commutes K (J a)
  comm : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (J a) (J b)
  pair : ∀ a b, edgeD m a b → ∃ W, LinearBlockStandardPair 𝔽₃ W (J a) (J b)

namespace DNodes3

variable {G : Type} [Group G] {m : ℕ} {Ω : Set (Subgroup G)} {K : Subgroup G}
  (nd : DNodes3 m Ω K)

@[expose] def DAdj (a b : Fin m) : Prop := edgeD m a b ∨ edgeD m b a

theorem DAdj.ne {a b : Fin m} (h : DAdj a b) : a ≠ b := by
  rintro rfl
  unfold DAdj edgeD at h
  omega

theorem pair_of_adj {a b : Fin m} (h : DAdj a b) :
    ∃ W, LinearBlockStandardPair 𝔽₃ W (nd.J a) (nd.J b) := by
  rcases h with h | h
  · exact nd.pair a b h
  · obtain ⟨W, hW⟩ := nd.pair b a h
    exact ⟨W, linearBlockStandardPair_symm hW⟩

theorem not_commutes_of_adj {a b : Fin m} (h : DAdj a b) : ¬ Commutes (nd.J a) (nd.J b) := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact not_commutes_of_linearBlockStandardPair hW

theorem commutes_of_not_adj {a b : Fin m} (hab : a ≠ b) (h : ¬ DAdj a b) :
    Commutes (nd.J a) (nd.J b) :=
  nd.comm a b hab (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))

theorem ne_J {a b : Fin m} (hab : a ≠ b) : nd.J a ≠ nd.J b := by
  intro h
  by_cases hadj : DAdj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact ne_of_linearBlockStandardPair hW h
  · have := nd.commutes_of_not_adj hab hadj
    rw [← h] at this
    exact not_commutes_self3 (nd.cl a) this

end DNodes3


section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_dnodes_of_pair_odd3_ge4 {m : ℕ} (hm : 4 ≤ m) (c : TCtx3 .POmegaOdd m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t) (hKβ : ∃ W, LinearBlockStandardPair 𝔽₃ W K β)
    {M : Subgroup G} (hMΩ : M ∈ Ω) (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes3 m Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
  classical
  have hm3 : 3 ≤ m := by omega
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hadm : StatedLieAdmissible .POmegaOdd m 3 1 :=
    ⟨Nat.prime_three, le_rfl, hm3, by norm_num⟩
  have : Finite (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hMΩ
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hMΩ hxM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  obtain ⟨hKM', hKQ⟩ := cx.ne_and_not_le_Q₁3 hKx hβx hKne hnKβ
  obtain ⟨hβM', hβQ⟩ := cx.ne_and_not_le_Q₁3 hβx hKx hKne.symm (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := cx.exists_fund_of_ne hKx hKM' hKQ
  obtain ⟨Rβ, hRβ, hβR⟩ := cx.exists_fund_of_ne hβx hβM' hβQ
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K) RK Rβ :=
    modelAdj_of_adj3 cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := exists_lin_of_map3' (not_three_dvd_card_center' cx.hY.cop) cx.d.ψ cx.d.ker_le
    (cx.hY.pow3 RK hRK) (cx.hY.pow3 Rβ hRβ) ⟨W', hW'⟩
  have cq := centralQuot3_odd (m := m) hm3
  have hdim : 9 ≤ Module.finrank 𝔽₃ (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd m 𝔽₃).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd m 𝔽₃ h2)
  let F₀ : HypFrame (quadOdd m 𝔽₃) m := (oddFrame m 𝔽₃).toHypFrame
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair3_gen_Q hQ hm F₀ hdim cq hRK hRβ hadj hlinR
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  have hRfund : ∀ k, dNode hm3 F₀ x₀ k ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D := by
    intro k
    by_cases h : k.val + 1 < m
    · rw [dNode_lt hm3 F₀ x₀ k h]
      exact cq.rootSL2_conj_mem F₀ _ _ _ _ _ x₀
    · rw [dNode_last hm3 F₀ x₀ k h]
      exact cq.rootSL2_conj_mem F₀ _ _ _ _ _ x₀
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes_gen3 (fun k => dNode hm3 F₀ x₀ k) hRfund
    (fun a b => edgeD m a b) (fun a b hab h1 h2' => commutes_dNode hm3 F₀ x₀ hab h1 h2')
    (fun a b h => stdPair_dNode_odd hm3 x₀ h)
  have hR0 : dNode hm3 F₀ x₀ a0 = RK := by
    rw [dNode_lt hm3 F₀ x₀ a0 (by show 0 + 1 < m; omega)]
    exact hx0.symm
  have hR1 : dNode hm3 F₀ x₀ a1 = Rβ := by
    rw [dNode_lt hm3 F₀ x₀ a1 (by show 1 + 1 < m; omega)]
    exact hx1.symm
  have hex : ∀ a, ∃ w, IsClassicalMember3 (j a) w := fun a =>
    c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes3 m Ω M :=
    { J := j
      w := w
      mem := fun a => (hj a).1.1
      cl := hw
      commK := hjM
      comm := hjc
      pair := hjp }
  refine ⟨nd, ?_, ?_⟩
  · exact cx.eq_of_locImg_eq (hj a0).1 hKx (by rw [(hj a0).2.2.2, hR0, hKR])
  · exact cx.eq_of_locImg_eq (hj a1).1 hβx (by rw [(hj a1).2.2.2, hR1, hβR])

end Nodes

end CFSG.ClassicalInvolution.Q3.Q3TWY
