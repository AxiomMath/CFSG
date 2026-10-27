module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Dn
public import CFSG.ClassicalInvolution.Q3.Q3TD3Orth
public import CFSG.ClassicalInvolution.RouteD.TWS7Grp
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open scoped MatrixGroups commutatorElement


local macro "fr_idx4" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem exists_spin_pair_four3
    {R₀ R₁ : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1)))}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField 3 1) (by omega)))
    (hR₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField 3 1) (by omega)))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₀ R₁) :
    ∃ x : spinGroup (quadPlus 4 (GaloisField 3 1)),
      R₀ = ((rootSL2 (plusFrame 4 (GaloisField 3 1) (by omega)) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 (plusFrame 4 (GaloisField 3 1) (by omega)) 1 2 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) := by
  classical
  have hm3 : 3 ≤ 4 := by norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have hQ : (quadPlus 4 (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 4 (GaloisField 3 1))
  have cq := centralQuot3_plus (m := 4) le_rfl
  let L : ℕ → Subgroup ((Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)) :=
    fun a => (if a = 0 then R₀ else R₁).map (spinAction (quadPlus 4 (GaloisField 3 1)))
  have hL0 : L 0 = R₀.map (spinAction (quadPlus 4 (GaloisField 3 1))) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction (quadPlus 4 (GaloisField 3 1))) := by simp [L]
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let i : ℕ → ((Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental (quadPlus 4 (GaloisField 3 1)) (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  obtain ⟨W, hW⟩ := hlin
  have hlinV : ∃ W', LinearBlockStandardPair (GaloisField 3 1) W'
      (R₀.map (spinAction (quadPlus 4 (GaloisField 3 1))))
      (R₁.map (spinAction (quadPlus 4 (GaloisField 3 1)))) :=
    ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
  obtain ⟨cm, N, C⟩ := ModelFacts.D4Rigid.adj_data_of_linear hodd hi₀ hi₁ hlinV
  have hVchain : VChain (quadPlus 4 (GaloisField 3 1)) 2 L i := by
    refine ⟨hi, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => by omega⟩
    · have : a = 0 := by omega
      subst this
      simpa [i] using cm
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using N
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using C
    · have : a = 0 := by omega
      subst this
      have := hasSingularVector_of_linearPair3 hi₀ hi₁ cm N C hlinV
      simpa [i] using this
  obtain ⟨pp, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hVchain (le_refl 2)
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ (plusFrame 4 (GaloisField 3 1) hm3) (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 (plusFrame 4 (GaloisField 3 1) hm3) a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction (quadPlus 4 (GaloisField 3 1))) := by
    intro a ha
    have := La_range_eq_of_pairs (plusFrame 4 (GaloisField 3 1) hm3) (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  refine ⟨x, ?_, ?_⟩
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₀)
      (rootSL2_map_conj_pow3 _ 0 1 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₁)
      (rootSL2_map_conj_pow3 _ 1 2 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL1]; exact hnode 1 (by omega))

section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_dnodes_of_pair_four3 (c : TCtx3 .POmegaPlus 4 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ nd : DNodes3 4 Ω M, nd.J ⟨0, by omega⟩ = K ∧ nd.J ⟨1, by omega⟩ = β := by
  classical
  have hm3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have : Finite (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
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
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := cx.lift_lin hRK hRβ ⟨W', hW'⟩
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  have hR0f : RK.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField 3 1) hm3) := map_symm_mem_fund_iso hm3 hcι hRK
  have hR1f : Rβ.map ι.symm.toMonoidHom ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField 3 1) hm3) := map_symm_mem_fund_iso hm3 hcι hRβ
  have hlin' : ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (RK.map ι.symm.toMonoidHom)
      (Rβ.map ι.symm.toMonoidHom) := by
    obtain ⟨W₁, hW₁⟩ := hlinR
    exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair_four3 hR0f hR1f hlin'
  let a0 : Fin 4 := ⟨0, by omega⟩
  let a1 : Fin 4 := ⟨1, by omega⟩
  let S : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1))) := fun a =>
    conjSub x₀ (rankOne (plusDatum 4 (GaloisField 3 1) hm3).rootGroup a)
  let R : Fin 4 → Subgroup (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K := fun a =>
    (S a).map ι.toMonoidHom
  have hRfund : ∀ a, R a ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D := fun a =>
    map_mem_fund_iso hm3 hcι (conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a) x₀)
  have hcomm : ∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (R a) (R b) :=
    fun a b hab h1 h2 => (commutes_map_equiv ι).mpr
      ((commutes_rankOne_plusDatum hm3 (LevisSpin.cartanD_of_not_edgeD hab h1 h2).1).conjSub x₀)
  have hstd : ∀ a b, edgeD 4 a b →
      ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (R a) (R b) :=
    fun a b h => by
      obtain ⟨W₁, hW₁⟩ := standardPair_plusDatum_edge (F := GaloisField 3 1) hm3 h
      exact ⟨_, linearBlockStandardPair_map_equiv ι
        (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₁ x₀)⟩
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes_gen3 R hRfund (fun a b => edgeD 4 a b) hcomm hstd
  have hid : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  have hR0 : R a0 = RK := by
    have hS : S a0 = RK.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum 4 (GaloisField 3 1) hm3).rootGroup a0) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a0) (by show 0 + 1 < 4; omega)]
      exact hx0.symm
    show (S a0).map ι.toMonoidHom = RK
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hR1 : R a1 = Rβ := by
    have hS : S a1 = Rβ.map ι.symm.toMonoidHom := by
      show conjSub x₀ (rankOne (plusDatum 4 (GaloisField 3 1) hm3).rootGroup a1) = _
      rw [rankOne_plusDatum_of_lt hm3 (k := a1) (by show 1 + 1 < 4; omega)]
      exact hx1.symm
    show (S a1).map ι.toMonoidHom = Rβ
    rw [hS, Subgroup.map_map, hid, Subgroup.map_id]
  have hex : ∀ a, ∃ w, IsClassicalMember3 (j a) w := fun a => c.hΩ.classical _ (hj a).1.1
  choose w hw using hex
  let nd : DNodes3 4 Ω M :=
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

theorem exists_fixed_twin_data3 (c : TCtx3 .POmegaPlus 4 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfix : HasFixedMember Ω K β z) :
    ∃ M M' J : Subgroup G,
      M ∈ centralizingMembers Ω {z} ∧ M ≠ K ∧ ¬ locImg Ω z M ≤ c.d.Q₁ ∧
      M' ∈ centralizingMembers Ω {z} ∧ M' ≠ K ∧ ¬ locImg Ω z M' ≤ c.d.Q₁ ∧
      J ∈ centralizingMembers Ω {z} ∧ J ≠ K ∧ ¬ locImg Ω z J ≤ c.d.Q₁ ∧
      Commutes M M' ∧ Commutes M J ∧ Commutes M' J ∧ Commutes β M ∧ Commutes β M' ∧
      conjSub t J = J ∧ (∃ W, LinearBlockStandardPair (GaloisField 3 1) W β J) ∧
      ¬ Commutes β J ∧ ∃ x ∈ J, x ≠ 1 ∧ x ^ 3 = 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨M, hMΩ, hKM, hβM, hMN⟩ := hfix
  have hMN' : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMN fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨nd, h0, h1⟩ :=
    exists_dnodes_of_pair_four3 c hsingle hβ ht hKβ hMΩ hKM hβM
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem (commutes_symm hKM)
  obtain ⟨N, hNz, hNM, hNc⟩ := hMN'
  have hML : IsLayerMember3 c M :=
    IsLayerMember3.of_not_commutes c hMz hNz (fun h => hNM h.symm) hNc
  obtain ⟨w, hw⟩ := hΩ.classical M hMΩ
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hMΩ hw
  obtain ⟨T, hTw, hTQ⟩ := cx.exists_twin
  have hKw : K ∈ centralizingMembers Ω {w} := mem_centralizingMembers_of_commutes c.hK hw.mem hKM
  have hβw : β ∈ centralizingMembers Ω {w} := mem_centralizingMembers_of_commutes hβ hw.mem hβM
  have hKL := IsLayerMember3.of_not_commutes cx hKw hβw hKne hnKβ
  have hKT : K ≠ T := fun h => hKL.2.2 (by rw [h, hTQ])
  have hTK : Commutes T K := cx.commutes_T_of_ne hTw hTQ.le hKw hKT
  have hnβK : ¬ Commutes β K := fun h => hnKβ (commutes_symm h)
  have hβT : β ≠ T := fun h => hnβK (h ▸ hTK)
  have hTβ : Commutes T β := cx.commutes_T_of_ne hTw hTQ.le hβw hβT
  have hMw : M ∈ centralizingMembers Ω {w} := ⟨hMΩ, isSubnormal_le hw.subnormal⟩
  have hTM : Commutes T M := cx.commutes_T_of_ne hTw hTQ.le hMw (cx.twin_ne hTw hTQ.le).symm
  have hTz : T ∈ centralizingMembers Ω {z} := mem_centralizingMembers_of_commutes hTw.1 c.hz.mem hTK
  have hTKne : T ≠ K := hKT.symm
  have hTQz : ¬ locImg Ω z T ≤ c.d.Q₁ := by
    intro hTQz
    obtain ⟨zT, hzT⟩ := hΩ.classical T hTw.1
    obtain ⟨g₁, hg₁⟩ := hsingle T hTw.1
    obtain ⟨g₂, hg₂⟩ := hsingle M hMΩ
    have hKconj : ∃ g : G, T = conjSub g K := ⟨g₁, hg₁⟩
    have hMconj : ∃ g : G, T = conjSub g M := ⟨g₁ * g₂⁻¹, by
      rw [hg₁, hg₂, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]⟩
    have e1 := centralizingMembers_eq_of_twin3 hΩ c.hz hzT hKconj hTz
      fun N hN hNT => c.commutes_T_of_ne hTz hTQz hN hNT
    have e2 := centralizingMembers_eq_of_twin3 hΩ hw hzT hMconj hTw
      fun N hN hNT => cx.commutes_T_of_ne hTw hTQ.le hN hNT
    have hβz : β ∈ centralizingMembers Ω {z} := by rw [← e1, e2]; exact hβw
    exact hnKβ (c.commutes_K_of_ne hβz hKne.symm)
  have hKJ : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx4)) (by fr_idx4)
  have hJz : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} := fun a h ha =>
    mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm (hKJ a h ha))
  have hJw : ∀ a : Fin 4, nd.J a ∈ centralizingMembers Ω {w} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hw.mem (commutes_symm (nd.commK a))
  have hadj1 : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a →
      DNodes3.Adj (⟨1, by omega⟩ : Fin 4) ⟨a, h⟩ := fun a h ha => by fr_idx4
  have key : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → ¬ locImg Ω z (nd.J ⟨a, h⟩) ≤ c.d.Q₁ →
      ∃ M M' J : Subgroup G,
        M ∈ centralizingMembers Ω {z} ∧ M ≠ K ∧ ¬ locImg Ω z M ≤ c.d.Q₁ ∧
        M' ∈ centralizingMembers Ω {z} ∧ M' ≠ K ∧ ¬ locImg Ω z M' ≤ c.d.Q₁ ∧
        J ∈ centralizingMembers Ω {z} ∧ J ≠ K ∧ ¬ locImg Ω z J ≤ c.d.Q₁ ∧
        Commutes M M' ∧ Commutes M J ∧ Commutes M' J ∧ Commutes β M ∧ Commutes β M' ∧
        conjSub t J = J ∧ (∃ W, LinearBlockStandardPair (GaloisField 3 1) W β J) ∧
        ¬ Commutes β J ∧ ∃ x ∈ J, x ≠ 1 ∧ x ^ 3 = 1 ∧ t * x * t⁻¹ = x⁻¹ := by
    intro a h ha hQ
    have hJK : nd.J ⟨a, h⟩ ≠ K := by
      rw [← h0]
      exact nd.ne_J (Gaps.fin_ne_of_val_ne (by fr_idx4)) |>.symm
    have hnβJ : ¬ Commutes β (nd.J ⟨a, h⟩) := by
      have := nd.not_commutes_of_adj (hadj1 a h ha)
      rwa [h1] at this
    have hJT : nd.J ⟨a, h⟩ ≠ T := fun hJT => hnβJ (by rw [hJT]; exact commutes_symm hTβ)
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨a, h⟩) (b := ⟨1, by omega⟩)
      (DNodes3.Adj.symm (hadj1 a h ha))
    obtain ⟨W₂, hW₂⟩ := nd.pair_of_adj (hadj1 a h ha)
    rw [h1] at hW₁ hW₂
    refine ⟨M, T, nd.J ⟨a, h⟩, hMz, hML.2.1, hML.2.2, hTz, hTKne, hTQz, hJz a h ha, hJK, hQ,
      commutes_symm hTM, nd.commK _, cx.commutes_T_of_ne hTw hTQ.le (hJw _) hJT, hβM,
      commutes_symm hTβ, conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two, ⟨W₂, hW₂⟩,
      hnβJ, ?_⟩
    exact RouteD.TWS7.exists_inverted_unipotent (p := 3) h2 hW₁ ht.mem ht.orderOf_eq_two
  by_cases hQ2 : locImg Ω z (nd.J ⟨2, by omega⟩) ≤ c.d.Q₁
  · refine key 3 (by omega) (by omega) fun hQ3 => ?_
    have := c.eq_of_locImg_le_Q₁ (hJz 2 (by omega) (by omega)) (hJz 3 (by omega) (by omega))
      hQ2 hQ3
    exact nd.ne_J (Gaps.fin_ne_of_val_ne (by fr_idx4)) this
  · exact key 2 (by omega) (by omega) hQ2

end Nodes

end CFSG.ClassicalInvolution.Q3.Q3TD
