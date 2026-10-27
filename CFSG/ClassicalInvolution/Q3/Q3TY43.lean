module

public import CFSG.ClassicalInvolution.Q3.Q3TY41
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLeaf

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups commutatorElement

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


section Spin

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {𝓕 : Set (Subgroup (spinGroup Q))} {Z' : Subgroup (V ≃ₗ[F] V)}

omit [Finite F] in
theorem map_conj_mem_fund3 (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) Z')
    {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝓕) (x : spinGroup Q) :
    R.map (MulAut.conj x).toMonoidHom ∈ 𝓕 := by
  obtain ⟨i, hi⟩ := cq.map_mem R hR
  have hg : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have himg : (R.map (MulAut.conj x).toMonoidHom).map (spinAction Q) =
      (R.map (spinAction Q)).map (MulAut.conj (spinAction Q x)).toMonoidHom :=
    CFSG.ClassicalInvolution.ModelFacts.map_conj_map (spinAction Q) x R
  have hL : (R.map (MulAut.conj x).toMonoidHom).map (spinAction Q) ∈ fundSet Q :=
    ⟨_, himg ▸ IsFundamental.conj hg hi⟩
  obtain ⟨R', hR', hR'e⟩ := cq.surj _ hL
  have hpow : Pow3 (R.map (MulAut.conj x).toMonoidHom) :=
    (cq.pow3 R hR).map (MulAut.conj x).toMonoidHom
  have := eq_of_map_eq_of_pow3 (spinAction Q) cq.ker_le cq.cop (cq.pow3 R' hR') hpow hR'e
  rwa [← this]

end Spin

section Leaf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem leaf_fixed_cluster3 (c : Q3TC.TCtx3 .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (nd : DNodes3 (7 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    (x : SpinM3 7) (tM : Bool)
    (hnode : ∀ a (ha : a ≤ 2), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a (a + 1) (by omega)
        (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 4 5 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ) :
    ∃ R : Subgroup (SpinM3 7),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) ∧
      (∃ F_N : OPFrame (QM3 7), R.map (spinAction (QM3 7)) = F_N.La.range ∧
        TwinSmall.leafV₀ 7 (⟨2, by omega⟩ : Fin (7 - 1)) ∈ F_N.span ∧
          ∀ w, planeVec 7 w ∈ F_N.span) ∧
      ∀ y ∈ R.map (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have cq := ctx_centralQuot3 (by norm_num : 4 ≤ 7)
  have hKJ : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 7 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  obtain ⟨R, hR, hRF, hcommR, hncommR, hneR, hinvR⟩ := exists_leaf_subgroup3 (m := 7)
    (by norm_num) (i := ⟨2, by omega⟩) (j := ⟨3, by omega⟩)
    (by simp [Fin.ext_iff]) true false
  have hRx : R.map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) :=
    map_conj_mem_fund3 cq hR x
  have hRd : (rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 2 3 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) :=
    cq.rootSL2_conj_mem _ (by omega) (by omega) (by omega) _ _ x
  obtain ⟨N, hNz, hNK, hNQ, hNimg⟩ := c.exists_member_of_fund hRx
  have hNK' : Commutes N K := commutes_symm (c.commutes_K_of_ne hNz hNK)
  have hJ2z := hmemz 2 (by omega) le_rfl
  have hJ4z := hmemz 4 (by omega) (by omega)
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  have hN2 : Commutes N (nd.J ⟨2, by omega⟩) :=
    (c.commutes_iff_fund hNz hJ2z hRx hNimg (hnode 0 (by omega))).mpr
      (commutes_map_of_commutes _ (hcommR 0 1 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true false))
  have hNM : Commutes N M :=
    (c.commutes_iff_fund hNz hMz hRx hNimg hMimg).mpr
      (commutes_map_of_commutes _ (hcommR 4 5 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true tM))
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNz.1
  have hDne : nd.J ⟨4, by omega⟩ ≠ N := by
    intro e
    rw [← e] at hNimg
    have h1' := (hnode 2 (by omega)).symm.trans hNimg
    have h2' := eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop
      (cq.pow3 _ hRd) (cq.pow3 _ hRx) h1'
    exact hneR (Subgroup.map_injective (MulAut.conj x).injective h2').symm
  have hDNn : ¬ Commutes (nd.J ⟨4, by omega⟩) N := by
    intro hc
    have := (c.commutes_iff_fund hJ4z hNz hRd (hnode 2 (by omega)) hNimg).mp hc
    exact hncommR ((TwinSmall.commutes_map_conj_iff x).mp this)
  have hinv : ∀ r r', InvOf ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 2 3
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom) r →
      InvOf (R.map (MulAut.conj x).toMonoidHom) r' → r * r' = r' * r :=
    TwinSmall.invs_commute_map_conj x fun r r' hr hr' => (hinvR r' r hr' hr).symm
  have hDNw : Commute (nd.w ⟨4, by omega⟩) wN :=
    commute_w_of_model3 c hJ4z hNz hRd hRx (hnode 2 (by omega)) hNimg (nd.cl _) hwN hinv
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  have a32 : DNodes3.Adj (⟨3, by omega⟩ : Fin (7 - 1)) ⟨2, by omega⟩ := by fr_idx
  have hβN : Commutes N β :=
    leaf_commutes_beta_gen3 (by norm_num : 7 ≤ 7) c hsingle nd h0 h1 hMΩ hxM
      (fun a h _ => commutes_symm (nd.commK ⟨a, h⟩)) (nd.mem ⟨3, by omega⟩) (nd.cl _)
      (commutes_symm (nd.commK _)) (commutes_symm (hKJ 3 (by omega) (by omega)))
      (nd.not_commutes_of_adj a32) (nd.ne_J a32.ne) (nd.commute_w _ _)
      (nd.mem ⟨4, by omega⟩) hNz.1 (nd.cl _) hwN (commutes_symm (nd.commK _)) hNM
      (commutes_symm (hKJ 4 (by omega) (by omega)))
      (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp)) (by fr_idx)) hNK' hN2 hDne hDNn hDNw
  refine ⟨R, hR, hRF, fun y hy => ?_⟩
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβN n hn t ht.mem)
  exact (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hNz).mp hNt (c.d.ψ y)
    (by rw [hNimg]; exact ⟨y, hy, rfl⟩)

theorem leaf_fixed_M3 (c : Q3TC.TCtx3 .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (nd : DNodes3 (7 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    (x : SpinM3 7) (tM : Bool)
    (hnode : ∀ a (ha : a ≤ 2), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a (a + 1) (by omega)
        (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ)
    (hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 4 5 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ) :
    ∃ R : Subgroup (SpinM3 7),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) ∧
      (∃ F_N : OPFrame (QM3 7), R.map (spinAction (QM3 7)) = F_N.La.range ∧
        TwinSmall.leafV₀ 7 (⟨4, by omega⟩ : Fin (7 - 1)) ∈ F_N.span ∧
          ∀ w, planeVec 7 w ∈ F_N.span) ∧
      ∀ y ∈ R.map (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant htz (c.d.ψ y) = c.d.ψ y := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have cq := ctx_centralQuot3 (by norm_num : 4 ≤ 7)
  have hKJ : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 7 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  have hJ2z := hmemz 2 (by omega) le_rfl
  have hJ4z := hmemz 4 (by omega) (by omega)
  obtain ⟨R, hR, hRF, hcommR, hncommR, hneR, hinvR⟩ := exists_leaf_subgroup3 (m := 7)
    (by norm_num) (i := ⟨4, by omega⟩) (j := ⟨5, by omega⟩)
    (by simp [Fin.ext_iff]) true tM
  have hRx : R.map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) :=
    map_conj_mem_fund3 cq hR x
  have hRM : (rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 4 5 (by omega)
      (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) :=
    cq.rootSL2_conj_mem _ (by omega) (by omega) (by omega) _ _ x
  obtain ⟨N, hNz, hNK, hNQ, hNimg⟩ := c.exists_member_of_fund hRx
  have hNK' : Commutes N K := commutes_symm (c.commutes_K_of_ne hNz hNK)
  have hN2 : Commutes N (nd.J ⟨2, by omega⟩) :=
    (c.commutes_iff_fund hNz hJ2z hRx hNimg (hnode 0 (by omega))).mpr
      (commutes_map_of_commutes _ (hcommR 0 1 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true false))
  have hN4 : Commutes N (nd.J ⟨4, by omega⟩) :=
    (c.commutes_iff_fund hNz hJ4z hRx hNimg (hnode 2 (by omega))).mpr
      (commutes_map_of_commutes _ (hcommR 2 3 (by omega) (by omega) (by omega) (by simp) (by simp)
        (by simp) (by simp) true false))
  have hRE : (rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 1 4 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) :=
    cq.rootSL2_conj_mem _ (by omega) (by omega) (by omega) _ _ x
  obtain ⟨E, hEz, hEK, hEQ, hEimg⟩ := c.exists_member_of_fund hRE
  have hEK' : Commutes E K := commutes_symm (c.commutes_K_of_ne hEz hEK)
  obtain ⟨wE, hwE⟩ := hΩ.classical E hEz.1
  have hE4 : Commutes E (nd.J ⟨4, by omega⟩) :=
    (c.commutes_iff_fund hEz hJ4z hRE hEimg (hnode 2 (by omega))).mpr
      (commutes_map_of_commutes _ (commutes_rootSL2_disjoint _ (a := 1) (b := 4) (c := 2) (d := 3)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) true false true false))
  obtain ⟨W, hW⟩ := TwinSmall.stdPair_E (p := 3) (f := 1) (by norm_num) x
  obtain ⟨W', hW'⟩ := c.stdPair_of_fund hJ2z hEz hW (hnode 0 (by omega)) hEimg
  have hEJ : ¬ Commutes E (nd.J ⟨2, by omega⟩) := fun h =>
    not_commutes_of_linearBlockStandardPair hW' (commutes_symm h)
  have hEne : E ≠ nd.J ⟨2, by omega⟩ := fun e =>
    ne_of_linearBlockStandardPair hW' e.symm
  have hEw : Commute wE (nd.w ⟨2, by omega⟩) :=
    (standardPair_involutions_commute h2 hW' (nd.cl ⟨2, by omega⟩).mem hwE.mem
      (nd.cl ⟨2, by omega⟩).orderOf_eq_two hwE.orderOf_eq_two).symm
  obtain ⟨wN, hwN⟩ := hΩ.classical N hNz.1
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  have hDne : M ≠ N := by
    intro e
    rw [← e] at hNimg
    have h1' := hMimg.symm.trans hNimg
    have h2' := eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop
      (cq.pow3 _ hRM) (cq.pow3 _ hRx) h1'
    exact hneR (Subgroup.map_injective (MulAut.conj x).injective h2').symm
  have hDNn : ¬ Commutes M N := by
    intro hc
    have := (c.commutes_iff_fund hMz hNz hRM hMimg hNimg).mp hc
    exact hncommR ((TwinSmall.commutes_map_conj_iff x).mp this)
  have hinv : ∀ r r', InvOf ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 4 5
      (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom) r →
      InvOf (R.map (MulAut.conj x).toMonoidHom) r' → r * r' = r' * r :=
    TwinSmall.invs_commute_map_conj x fun r r' hr hr' => (hinvR r' r hr' hr).symm
  have hDNw : Commute xM wN := commute_w_of_model3 c hMz hNz hRM hRx hMimg hNimg hxM hwN hinv
  have hβN : Commutes N β :=
    leaf_commutes_beta_gen3 (by norm_num : 7 ≤ 7) c hsingle nd h0 h1 (nd.mem ⟨4, by omega⟩)
      (nd.cl ⟨4, by omega⟩)
      (fun a h ha => nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx))
      hEz.1 hwE hE4 hEK' hEJ hEne hEw hMΩ hNz.1 hxM hwN (nd.commK _) hN4 hMK (nd.commK _) hNK'
      hN2 hDne hDNn hDNw
  refine ⟨R, hR, hRF, fun y hy => ?_⟩
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hβN n hn t ht.mem)
  exact (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hNz).mp hNt (c.d.ψ y)
    (by rw [hNimg]; exact ⟨y, hy, rfl⟩)

end Leaf

end CFSG.ClassicalInvolution.Q3.Q3TY
