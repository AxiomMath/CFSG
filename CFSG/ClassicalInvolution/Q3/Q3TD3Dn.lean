module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Nodes
public import CFSG.ClassicalInvolution.Q3.Q3TY33
public import CFSG.ClassicalInvolution.Q3.Q3TY23
public import CFSG.ClassicalInvolution.RouteD.GapsFrNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open scoped MatrixGroups commutatorElement


section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem finrank_plus3 (m : ℕ) :
    Module.finrank (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

theorem exists_dnodes_of_pair_plus3 {m : ℕ} (hm : 5 ≤ m) (c : TCtx3 .POmegaPlus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes3 m Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hadm : StatedLieAdmissible .POmegaPlus m 3 1 := ⟨Nat.prime_three, le_rfl, by omega⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have : Finite (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K :=
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
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K) RK Rβ :=
    cx.modelAdj_of_adj3 hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := cx.lift_lin hRK hRβ ⟨W', hW'⟩
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  have hR0f : RK.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField 3 1) hm3) := map_symm_mem_fund_iso hm3 hcι hRK
  have hR1f : Rβ.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField 3 1) hm3) := map_symm_mem_fund_iso hm3 hcι hRβ
  have hadj' := ModelAdj.map_equiv ι.symm hadj
  have hlin' : ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (RK.map ι.symm.toMonoidHom)
      (Rβ.map ι.symm.toMonoidHom) := by
    obtain ⟨W₁, hW₁⟩ := hlinR
    exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  have cq := centralQuot3_plus (m := m) (by omega)
  have hQ : (quadPlus m (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus m (GaloisField 3 1))
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1) := by
    rw [finrank_plus3]
    omega
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair3_frame hQ (m := m) (by omega)
    (plusFrame m (GaloisField 3 1) hm3) hdim cq hR0f hR1f hadj' hlin'
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  let S : Fin m → Subgroup (spinGroup (quadPlus m (GaloisField 3 1))) := fun a =>
    conjSub x₀ (rankOne (plusDatum m (GaloisField 3 1) hm3).rootGroup a)
  let R : Fin m → Subgroup (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K := fun a =>
    (S a).map ι.toMonoidHom
  have hRfund : ∀ a, R a ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D := fun a =>
    map_mem_fund_iso hm3 hcι (conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a) x₀)
  have hcomm : ∀ a b, a ≠ b → ¬ edgeD m a b → ¬ edgeD m b a → Commutes (R a) (R b) :=
    fun a b hab h1 h2 => (commutes_map_equiv ι).mpr
      ((commutes_rankOne_plusDatum hm3 (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1).conjSub x₀)
  have hstd : ∀ a b, edgeD m a b →
      ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (R a) (R b) :=
    fun a b h => by
      obtain ⟨W₁, hW₁⟩ := standardPair_plusDatum_edge (F := GaloisField 3 1) hm3 h
      exact ⟨_, linearBlockStandardPair_map_equiv ι
        (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ x₀)⟩
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes_gen3 R hRfund (fun a b => edgeD m a b) hcomm hstd
  have hid : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  have hR0 : R a0 = RK := by
    have hS : S a0 = RK.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum m (GaloisField 3 1) hm3).rootGroup a0) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a0) (by show 0 + 1 < m; omega)]
      exact hx0.symm
    show (S a0).map ι.toMonoidHom = RK
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hR1 : R a1 = Rβ := by
    have hS : S a1 = Rβ.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum m (GaloisField 3 1) hm3).rootGroup a1) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a1) (by show 1 + 1 < m; omega)]
      exact hx1.symm
    show (S a1).map ι.toMonoidHom = Rβ
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hex : ∀ a, ∃ w, IsClassicalMember3 (j a) w := fun a => c.hΩ.classical _ (hj a).1.1
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

end CFSG.ClassicalInvolution.Q3.Q3TD
