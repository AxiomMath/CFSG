module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBNodes

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType
  CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalGroups.Orthogonal QuadraticMap

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem exists_dnodes_of_pair_odd_ge4 {m : ℕ} (hm : 4 ≤ m) (c : TCtx p f .POmegaOdd m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaOdd m Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes p f m Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hq4 : 4 ≤ p ^ f := by have := c.hq; omega
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  obtain ⟨xM, hxM⟩ := c.hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hxM
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
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaOdd m p f Fact.out).K) RK Rβ :=
    modelAdj_of_adj cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hF := orthFacts_odd c.hp2 hm4 c.hq
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  have cq := centralQuot_odd (m := m) (f := f) c.hp2 hm3 c.hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd m (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2)
  let F₀ : HypFrame (quadOdd m (GaloisField p f)) m := (oddFrame m (GaloisField p f)).toHypFrame
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_gen c.hp2 c.hq hQ hm4 F₀ hdim cq hRK hRβ hadj hlinR
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  have hRfund : ∀ k, dNode hm3 F₀ x₀ k ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd m p f Fact.out).D := by
    intro k
    by_cases h : k.val + 1 < m
    · rw [dNode_lt hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
    · rw [dNode_last hm3 F₀ x₀ k h]
      exact rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ _ _ x₀
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes (fun k => dNode hm3 F₀ x₀ k) hRfund
    (fun a b => edgeD m a b) (fun a b hab h1 h2' => commutes_dNode hm3 F₀ x₀ hab h1 h2')
    (fun a b h => stdPair_dNode_odd hm3 x₀ h)
  have hR0 : dNode hm3 F₀ x₀ a0 = RK := by
    rw [dNode_lt hm3 F₀ x₀ a0 (by show 0 + 1 < m; omega)]
    exact hx0.symm
  have hR1 : dNode hm3 F₀ x₀ a1 = Rβ := by
    rw [dNode_lt hm3 F₀ x₀ a1 (by show 1 + 1 < m; omega)]
    exact hx1.symm
  have hex : ∀ a, ∃ w, IsClassicalMember p f (j a) w := fun a =>
    c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes p f m Ω M :=
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

end CFSG.ClassicalInvolution.RouteD.TWE.B4
