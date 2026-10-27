module

public import CFSG.ClassicalInvolution.Q3.Q3TY17
public import CFSG.ClassicalInvolution.Q3.Q3TY23
public import CFSG.ClassicalInvolution.Q3.Q3TY19
public import CFSG.ClassicalInvolution.Q3.Q3TY10
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusNodes
public import CFSG.ClassicalInvolution.RouteD.GapsFrBNodes
public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem modelInvComm3 (cx : TCtx3 tY nY Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω z L = R.map cx.d.ψ) (hLR' : locImg Ω z L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hc : Commute w w') :
    ∃ r r', InvOf R r ∧ InvOf R' r' ∧
      ⁅r, r'⁆ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      cx.d.ψ r = locElt Ω z w (le_centralizingLayer hL hw.mem) ∧
      cx.d.ψ r' = locElt Ω z w' (le_centralizingLayer hL' hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := Q3TY.exists_involution_of_fund3 cx hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := Q3TY.exists_involution_of_fund3 cx hL' hR' hLR' hw'
  refine ⟨r, r', hr, hr', cx.d.ker_le ?_, hψr, hψr'⟩
  have hcomm : cx.d.ψ r * cx.d.ψ r' = cx.d.ψ r' * cx.d.ψ r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem conjSub_eq3 (cx : TCtx3 tY nY Ω K z) {L : Subgroup G}
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω z L = R.map cx.d.ψ) {w : G} (hwx : w ∈ locLayer Ω z)
    {r : (modelUniv tY nY 3 1 Nat.prime_three).K} (hr : cx.d.ψ r = locElt Ω z w hwx)
    (hN : conjSub w L = L) : conjSub r R = R := by
  refine eq_of_map_eq_of_pow3 cx.d.ψ cx.d.ker_le cx.ker_cop ((cx.hY.pow3 R hR).conjSub r)
    (cx.hY.pow3 R hR) ?_
  have h1 := locImg_conjSub_layer (Ω := Ω) (x := z) L ⟨w, hwx⟩
  rw [hN, hLR] at h1
  have h2 : (conjSub r R).map cx.d.ψ =
      (R.map cx.d.ψ).map (MulAut.conj (locMk Ω z ⟨w, hwx⟩)).toMonoidHom := by
    show (R.map (MulAut.conj r).toMonoidHom).map cx.d.ψ = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv]
    rw [show locMk Ω z ⟨w, hwx⟩ = locElt Ω z w hwx from rfl, ← hr]
  rw [h2, ← h1]

theorem modelAdj_of_adj3 (cx : TCtx3 tY nY Ω K z) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {z}) (hL' : L' ∈ centralizingMembers Ω {z})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω z L = R.map cx.d.ψ) (hLR' : locImg Ω z L' = R'.map cx.d.ψ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ := cx.modelInvComm3 hL hL' hR hR' hLR hLR' hw hw' hc
  refine ⟨fun h => hne (cx.eq_of_locImg_eq hL hL' (by rw [hLR, hLR', h])), ?_, r, r', hr, hr',
    hcen, ?_⟩
  · intro h
    exact hnc ((cx.commutes_iff_fund hL hL' hR hLR hLR').mpr h)
  · intro y hy
    have h := cx.conjSub_eq3 hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN
    rw [← h]
    exact ⟨y, hy, rfl⟩

end CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.LieType.Universal CFSG.LieType CFSG.Timmesfeld
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups commutatorElement

section Leaves

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}


theorem exists_leaves_td5_3 (c : TCtx3 .POmegaMinus 5 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G}
    (hMΩ : M ∈ Ω) (hKM : Commutes K M) (hβM : Commutes β M) :
    ∃ J₂ ∈ Ω, ∃ J₃ ∈ Ω, J₂ ≠ J₃ ∧ Commutes J₂ J₃ ∧ Commutes M J₂ ∧ Commutes M J₃ ∧
      Commutes K J₂ ∧ Commutes K J₃ ∧ (∃ W, LinearBlockStandardPair (GaloisField 3 1) W β J₂) ∧
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W β J₃ := by
  classical
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ 5; omega⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have : Finite (modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have hirr := minusCoeffs_irr 3 1
  have hm3 : 3 ≤ 5 - 1 := by omega
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
  obtain ⟨hKK, hKQ⟩ := cx.ne_and_not_le_Q₁3 hKx hβx hKne hnKβ
  obtain ⟨hβK, hβQ⟩ := cx.ne_and_not_le_Q₁3 hβx hKx hKne.symm (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := cx.exists_fund_of_ne hKx hKK hKQ
  obtain ⟨Rβ, hRβ, hβR⟩ := cx.exists_fund_of_ne hβx hβK hβQ
  have hadj : ModelAdj (Subgroup.center (modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K) RK Rβ :=
    cx.modelAdj_of_adj3 hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W RK Rβ :=
    exists_lin_of_map3' (not_three_dvd_card_center' cx.hY.cop) cx.d.ψ cx.d.ker_le
      (cx.hY.pow3 _ hRK) (cx.hY.pow3 _ hRβ) ⟨W', hW'⟩
  have cq := centralQuot3_minus hadm
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_minus 3 1 5 (by omega)]
    omega
  have hQ : (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 5 (GaloisField 3 1) hirr)
  set F₀ : HypFrame (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
      (5 - 1) := (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame with hF₀
  obtain ⟨x₀, hx0, hx1⟩ := exists_spin_pair3_frame hQ (m := 5 - 1) (by norm_num) F₀ hdim cq hRK hRβ
    hadj hlinR
  have hRfund : ∀ k, dNode hm3 F₀ x₀ k ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D := by
    intro k
    by_cases h : k.val + 1 < 5 - 1
    · rw [dNode_lt hm3 F₀ x₀ k h]
      exact cq.rootSL2_conj_mem F₀ _ _ _ _ _ x₀
    · rw [dNode_last hm3 F₀ x₀ k h]
      exact cq.rootSL2_conj_mem F₀ _ _ _ _ _ x₀
  obtain ⟨j, hj, hjc, hjp, hjM⟩ := cx.exists_nodes_gen3 (fun k => dNode hm3 F₀ x₀ k) hRfund
    (fun a b => edgeD (5 - 1) a b) (fun a b hab h1 h2' => commutes_dNode hm3 F₀ x₀ hab h1 h2')
    (fun a b h => stdPair_dNode_minus (p := 3) (f := 1) (by norm_num) (by norm_num) x₀ h)
  have hR0 : dNode hm3 F₀ x₀ ⟨0, by omega⟩ = RK := by
    rw [dNode_lt hm3 F₀ x₀ ⟨0, by omega⟩ (by show 0 + 1 < 5 - 1; omega)]
    exact hx0.symm
  have hR1 : dNode hm3 F₀ x₀ ⟨1, by omega⟩ = Rβ := by
    rw [dNode_lt hm3 F₀ x₀ ⟨1, by omega⟩ (by show 1 + 1 < 5 - 1; omega)]
    exact hx1.symm
  have hj0 : j ⟨0, by omega⟩ = K :=
    cx.eq_of_locImg_eq (hj _).1 hKx (by rw [(hj _).2.2.2, hR0, hKR])
  have hj1 : j ⟨1, by omega⟩ = β :=
    cx.eq_of_locImg_eq (hj _).1 hβx (by rw [(hj _).2.2.2, hR1, hβR])
  have hJ₂Ω : j ⟨2, by omega⟩ ∈ Ω := (hj _).1.1
  have hJ₃Ω : j ⟨3, by omega⟩ ∈ Ω := (hj _).1.1
  have hcomm23 : Commutes (j ⟨2, by omega⟩) (j ⟨3, by omega⟩) :=
    hjc _ _ (by simp [Fin.ext_iff]) (by simp [edgeD]) (by simp [edgeD])
  obtain ⟨wJ, hwJ⟩ := c.hΩ.classical _ hJ₂Ω
  have hne23 : j ⟨2, by omega⟩ ≠ j ⟨3, by omega⟩ := fun h => by
    rw [← h] at hcomm23
    exact not_commutes_self3 hwJ hcomm23
  refine ⟨j ⟨2, by omega⟩, hJ₂Ω, j ⟨3, by omega⟩, hJ₃Ω, hne23, hcomm23, hjM _, hjM _, ?_, ?_, ?_,
    ?_⟩
  · rw [← hj0]
    exact hjc _ _ (by simp [Fin.ext_iff]) (by simp [edgeD]) (by simp [edgeD])
  · rw [← hj0]
    exact hjc _ _ (by simp [Fin.ext_iff]) (by simp [edgeD]) (by simp [edgeD])
  · rw [← hj1]
    exact hjp _ _ (by simp [edgeD])
  · rw [← hj1]
    exact hjp _ _ (by simp [edgeD])

end Leaves

end CFSG.ClassicalInvolution.Q3.Q3TY
