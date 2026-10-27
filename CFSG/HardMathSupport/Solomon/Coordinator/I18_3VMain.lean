module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VBalance
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VDiag
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification Subgroup

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem i183v_comp_up {p : ℕ} (hp : p.Prime) {H M K : Subgroup G} (hK : GLAPComponent p H K)
    (hHM : H ≤ M) (hsnM : IsSubnormal K M) : GLAPComponent p M K := by
  obtain ⟨hKH, hsn, hcomp, hmin⟩ := hK
  have hKX : K ≤ M := hKH.trans hHM
  refine ⟨hKX, hsnM, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := M) p hsnM
    rwa [barX_self] at this
  · have e : ↥(barX p M K) ≃* ↥(barX p H K) :=
      (quotEquivBarX hp hKX hsnM).symm.trans (quotEquivBarX hp hKH hsn)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcomp.2.2
  · intro J hJ hJsn heq
    have hJK : J ≤ K := hJ.le
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn (hJK.trans hKH) hHM
    have hcoreK : K ⊓ GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnM]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hsn
    refine hmin J hJ hJsnH ?_
    show barX p H J = barX p H K
    refine le_antisymm (barX_mono p hJK) ?_
    refine barX_le_of_forall (hJK.trans hKH) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) (le_of_eq heq.symm) hk (hKX hk)
    exact ⟨j, hj, hcoreK ⟨K.mul_mem (K.inv_mem (hJK hj)) hk, hjk⟩⟩

theorem i183v_glaPLayer_gLBConj (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hL g)

theorem i183v_le_normalizer_glaPLayer (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (GLAPLayer p X : Set G) := fun g hg => by
  rw [mem_normalizer_iff_gLBConj_eq, ← i183v_glaPLayer_gLBConj,
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)]

theorem i183v_mem_zpowers {x e : G} (hx3 : x ^ 3 = 1) (he : e ∈ Subgroup.zpowers x) :
    ∃ r : ℕ, r < 3 ∧ e = x ^ r := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
  have hx3' : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
  have h1 : x ^ k = x ^ (k % 3) := zpow_eq_zpow_emod k hx3'
  have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hlt : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  rw [h1, ← zpow_natCast, Int.toNat_of_nonneg hnn]

end Helpers

section Main

variable {G : Type} [Group G] [Finite G]

theorem input18_3_12_of_schreier (hS : CatalogueRelativeB.CatalogueSchreier) :
    UniquenessMaximal.Input18_3_12 := by
  intro G _ _ hKP x y hx1 hy1 hx3 hy3 hxy J hJ
  have hp : Nat.Prime 3 := Nat.prime_three
  have hxX : x ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxy
  have hEX : Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.zpowers_le.2 hxX
  have hE : IsElemAbelian 3 (Subgroup.zpowers x) := i183v_isElemAbelian_zpowers hx3
  have hEp : IsPGroup 3 ↥(Subgroup.zpowers x) := isPGroup_of_isElemAbelian' hE
  have hcz : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hH0 : GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (i183_glaPLayer_le 3 _))
  have hnorm : Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ⊓
        Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := fun h hh =>
    i183_mem_normalizer_inf (i183v_le_normalizer_glaPLayer 3 _ hh.2) (Subgroup.le_normalizer hh.1)
  have hsn : IsSubnormal J (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isSubnormal_trans' hJ.2.1 (CFSG.Quasithin.A3.subnormal_of_normal hH0
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hH0).2 hnorm))
  have hJ' : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) J := i183v_comp_up hp hJ hH0 hsn
  have hJ'' : GLAPComponent 3 (Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) J := by
    rw [hcz]
    exact hJ'
  have hJL : J ≤ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)) := by
    refine (le_sSup hJ' : J ≤ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G))).trans ?_
    by_cases hyc : Subgroup.centralizer ({y} : Set G) = ⊤
    · rw [hyc, top_inf_eq]
      exact i183v_glaPLayer_centralizer_le_top hS hKP hx3
    · have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G)) :=
        CatalogueKProper.proper_subgroup_open_isKGroup
          (CatalogueKProper.kProper_of_isKProper hKP) _ hyc
      have := i183_glaPLayer_inf_centralizer_le hS hK hp hEX hEp
      rwa [hcz] at this
  have hCeq := i183_iSup_family_eq hp hJ'' hJL
  have hJE : J ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    hJ''.1.trans inf_le_right
  have hstab : ∀ L ∈ i183Family 3 (Subgroup.centralizer ({y} : Set G)) J, GLBConj x L ∈
      i183Family 3 (Subgroup.centralizer ({y} : Set G)) J := fun L hL =>
    i183_gLBConj_mem_family hEX hJE hL (Subgroup.mem_zpowers x)
  have htrans := fun L₁ L₂ h₁ h₂ => i183_transitive hp hEX hEp hJ'' hJL (L₁ := L₁) (L₂ := L₂) h₁ h₂
  have hJK : J ≤ ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)), GLBConj g J :=
    le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (gLBConj_one J).ge
  obtain ⟨M, hM⟩ : ∃ M, M ∈ i183Family 3 (Subgroup.centralizer ({y} : Set G)) J := by
    by_contra hne
    push Not at hne
    have h0 : (⨆ L ∈ i183Family 3 (Subgroup.centralizer ({y} : Set G)) J, L) = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun L hL => absurd hL (hne L))
    rw [hCeq] at h0
    have := hJK.trans h0.le
    exact i183v_not_le_core hJ'' inf_le_left (this.trans bot_le)
  by_cases hxM : GLBConj x M = M
  · left
    have hsub : ∀ L ∈ i183Family 3 (Subgroup.centralizer ({y} : Set G)) J, L = M := by
      intro L hL
      obtain ⟨e, he, rfl⟩ := htrans M L hM hL
      exact gLBConj_eq_of_mem_normalizer
        (Subgroup.zpowers_le.2 (mem_normalizer_iff_gLBConj_eq.2 hxM) he)
    have hKM : (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)), GLBConj g J) = M := by
      rw [← hCeq]
      exact le_antisymm (iSup₂_le fun L hL => (hsub L hL).le) (le_iSup₂_of_le M hM le_rfl)
    rw [hKM]
    exact ⟨hM.1, mem_normalizer_iff_gLBConj_eq.2 hxM⟩
  · right
    have hx3' : x * (x * x) = 1 := by
      rw [← pow_three]
      exact hx3
    have h3 : GLBConj x (GLBConj x (GLBConj x M)) = M := by
      rw [gLBConj_gLBConj, gLBConj_gLBConj, hx3', gLBConj_one]
    have h2 : GLBConj x (GLBConj x M) ≠ M := by
      intro h
      apply hxM
      exact (h3.symm.trans (congrArg (GLBConj x) h)).symm
    have hM1 := hstab M hM
    have hM2 := hstab _ hM1
    have hKeq : (⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({y} : Set G)), GLBConj g J) =
        M ⊔ GLBConj x M ⊔ GLBConj x (GLBConj x M) := by
      rw [← hCeq]
      refine le_antisymm (iSup₂_le fun L hL => ?_) (sup_le (sup_le
        (le_iSup₂_of_le M hM le_rfl) (le_iSup₂_of_le _ hM1 le_rfl)) (le_iSup₂_of_le _ hM2 le_rfl))
      obtain ⟨e, he, rfl⟩ := htrans M L hM hL
      obtain ⟨r, hr, rfl⟩ := i183v_mem_zpowers hx3 he
      have hcg : GLBConj (x ^ r) M = i183vM x M r := rfl
      rw [hcg]
      interval_cases r
      · rw [i183vM_zero]
        exact le_sup_of_le_left le_sup_left
      · rw [i183vM_one]
        exact le_sup_of_le_left le_sup_right
      · rw [i183vM_two]
        exact le_sup_right
    refine ⟨M, hM.1, hxM, h2, hKeq, ?_⟩
    exact i183v_diag ⟨hxX, hx3, hM.1, hxM, h2⟩ hJ' (hKeq ▸ hJK)

end Main

theorem input18_3_12_holds :

    UniquenessMaximal.Input18_3_12 :=
  input18_3_12_of_schreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds

end CFSG.HardMathSupport.Solomon.Coordinator
