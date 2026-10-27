module

public import CFSG.ClassicalInvolution.Q3.Q3TY28

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.LieType.Universal CFSG.LieType CFSG.Timmesfeld
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups commutatorElement

section Nodes

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

structure DNodes3 (n : ℕ) (Ω : Set (Subgroup G)) (K : Subgroup G) where
  J : Fin n → Subgroup G
  w : Fin n → G
  mem : ∀ a, J a ∈ Ω
  cl : ∀ a, IsClassicalMember3 (J a) (w a)
  commK : ∀ a, Commutes K (J a)
  comm : ∀ a b, a ≠ b → ¬ edgeD n a b → ¬ edgeD n b a → Commutes (J a) (J b)
  pair : ∀ a b, edgeD n a b → ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (J a) (J b)

namespace DNodes3

variable {n : ℕ} {K : Subgroup G} (nd : DNodes3 n Ω K)

@[expose] def Adj (a b : Fin n) : Prop := edgeD n a b ∨ edgeD n b a

theorem adj_def (a b : Fin n) : Adj a b ↔
    (((a.val + 1 = b.val ∧ b.val + 1 < n) ∨ (a.val + 3 = n ∧ b.val + 1 = n)) ∨
    ((b.val + 1 = a.val ∧ a.val + 1 < n) ∨ (b.val + 3 = n ∧ a.val + 1 = n))) := Iff.rfl

theorem Adj.ne {a b : Fin n} (h : Adj a b) : a ≠ b := by
  rintro rfl
  unfold Adj edgeD at h
  omega

theorem Adj.symm {a b : Fin n} (h : Adj a b) : Adj b a := Or.symm h

theorem pair_of_adj {a b : Fin n} (h : Adj a b) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (nd.J a) (nd.J b) := by
  rcases h with h | h
  · exact nd.pair a b h
  · obtain ⟨W, hW⟩ := nd.pair b a h
    exact ⟨W, linearBlockStandardPair_symm hW⟩

theorem not_commutes_of_adj {a b : Fin n} (h : Adj a b) : ¬ Commutes (nd.J a) (nd.J b) := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact not_commutes_of_linearBlockStandardPair hW

theorem commutes_of_not_adj {a b : Fin n} (hab : a ≠ b) (h : ¬ Adj a b) :
    Commutes (nd.J a) (nd.J b) :=
  nd.comm a b hab (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))

theorem ne_J {a b : Fin n} (hab : a ≠ b) : nd.J a ≠ nd.J b := by
  intro h
  by_cases hadj : Adj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact ne_of_linearBlockStandardPair hW h
  · have := nd.commutes_of_not_adj hab hadj
    rw [← h] at this
    exact not_commutes_self3 (nd.cl a) this

theorem commute_w (a b : Fin n) : Commute (nd.w a) (nd.w b) := by
  by_cases hab : a = b
  · subst hab
    exact Commute.refl _
  by_cases hadj : Adj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact standardPair_involutions_commute two_ne_zero_gf3 hW (nd.cl a).mem (nd.cl b).mem
      (nd.cl a).orderOf_eq_two (nd.cl b).orderOf_eq_two
  · exact (nd.commutes_of_not_adj hab hadj) _ (nd.cl a).mem _ (nd.cl b).mem

theorem conjSub_w {a b : Fin n} (h : Adj a b) : conjSub (nd.w b) (nd.J a) = nd.J a := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact conjSub_eq_of_standardPair two_ne_zero_gf3 hW (nd.cl b).mem (nd.cl b).orderOf_eq_two

end DNodes3

end Nodes

section Layer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

@[expose] def IsLayerMember3 (cx : Q3TC.TCtx3 tY nY Ω K z) (L : Subgroup G) : Prop :=
  L ∈ centralizingMembers Ω {z} ∧ L ≠ K ∧ ¬ locImg Ω z L ≤ cx.d.Q₁

theorem IsLayerMember3.of_not_commutes (cx : Q3TC.TCtx3 tY nY Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z}) (hne : L ≠ L')
    (hc : ¬ Commutes L L') : IsLayerMember3 cx L :=
  ⟨hL, (cx.ne_and_not_le_Q₁3 hL hL' hne hc).1, (cx.ne_and_not_le_Q₁3 hL hL' hne hc).2⟩

theorem IsLayerMember3.exists_fund {cx : Q3TC.TCtx3 tY nY Ω K z} {L : Subgroup G}
    (hL : IsLayerMember3 cx L) :
    ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      locImg Ω z L = R.map cx.d.ψ :=
  cx.exists_fund_of_ne hL.1 hL.2.1 hL.2.2

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3.lift_lin
    [Finite (modelUniv tY nY 3 1 Nat.prime_three).K] (cx : Q3TC.TCtx3 tY nY Ω K z)
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R.map cx.d.ψ) (R'.map cx.d.ψ)) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R' :=
  exists_lin_of_map3' (not_three_dvd_card_center' cx.hY.cop) cx.d.ψ cx.d.ker_le (cx.hY.pow3 R hR)
    (cx.hY.pow3 R' hR') h

theorem exists_dnodes_of_pair_minus3 {m : ℕ} (hm : 5 ≤ m) (c : Q3TC.TCtx3 .POmegaMinus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes3 (m - 1) Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
  classical
  have hm3 : 3 ≤ m - 1 := by omega
  have hadm : StatedLieAdmissible .POmegaMinus m 3 1 := ⟨Nat.prime_three, le_rfl, by omega⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have : Finite (modelUniv .POmegaMinus m 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by omega) Nat.prime_three trivial hadm
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hMΩ
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hMΩ hxM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t := standardPair_involutions_commute h2 hW c.hz.mem ht.mem
    c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember3.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember3.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaMinus m 3 1 Nat.prime_three).K) RK Rβ :=
    cx.modelAdj_of_adj3 hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := cx.lift_lin hRK hRβ ⟨W', hW'⟩
  have cq := centralQuot3_minus hadm
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_minus 3 1 m (by omega)]
    omega
  have hQ : (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite m (GaloisField 3 1) (minusCoeffs_irr 3 1))
  let F₀ : HypFrame (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
      (m - 1) := (minusFrame m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair3_frame hQ (m := m - 1) (by omega) F₀ hdim cq hRK hRβ
    hadj hlinR
  let a0 : Fin (m - 1) := ⟨0, by omega⟩
  let a1 : Fin (m - 1) := ⟨1, by omega⟩
  have hRfund : ∀ k, dNode hm3 F₀ x₀ k ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus m 3 1 Nat.prime_three).D := by
    intro k
    by_cases h : k.val + 1 < m - 1
    · rw [dNode_lt hm3 F₀ x₀ k h]
      exact cq.rootSL2_conj_mem F₀ _ _ _ _ _ x₀
    · rw [dNode_last hm3 F₀ x₀ k h]
      exact cq.rootSL2_conj_mem F₀ _ _ _ _ _ x₀
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes_gen3 (fun k => dNode hm3 F₀ x₀ k) hRfund
    (fun a b => edgeD (m - 1) a b) (fun a b hab h1 h2' => commutes_dNode hm3 F₀ x₀ hab h1 h2')
    (fun a b h => stdPair_dNode_minus (p := 3) (f := 1) hm (by norm_num) x₀ h)
  have hR0 : dNode hm3 F₀ x₀ a0 = RK := by
    rw [dNode_lt hm3 F₀ x₀ a0 (by show 0 + 1 < m - 1; omega)]
    exact hx0.symm
  have hR1 : dNode hm3 F₀ x₀ a1 = Rβ := by
    rw [dNode_lt hm3 F₀ x₀ a1 (by show 1 + 1 < m - 1; omega)]
    exact hx1.symm
  have hex : ∀ a, ∃ w, IsClassicalMember3 (j a) w := fun a => c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes3 (m - 1) Ω M :=
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

end Layer

end CFSG.ClassicalInvolution.Q3.Q3TY
