module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Model
public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Grp
public import CFSG.ClassicalInvolution.Q3.Q3TD3Pat
public import CFSG.ClassicalInvolution.Q3.Q3EXD4FLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Asm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem partnerPatternPlus3_four_of_model (hMFZ : Gaps.FundNoncentral 3)
    (c : TCtx3 .POmegaPlus 4 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    PartnerPatternPlus3 4 Ω K β t := by
  have hmodel := @CFSG.ClassicalInvolution.Q3.Q3TD.modelLeafD3_proved
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have htz := partner_involution_commutes_z3 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hm3 : 3 ≤ 4 := by omega
  obtain ⟨M, M', J, hMz, hMK, hMQ, hM'z, hM'K, hM'Q, hJz, hJK, hJQ, hMM', hMJ, hM'J, hβM, hβM',
    hJt, hJpair, hnβJ, x, hxJ, hx1, hxp, hxinv⟩ :=
    exists_fixed_twin_data3 c hsingle hβ ht ⟨W, hW⟩ hfixM
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  obtain ⟨RM, hRM, hMR⟩ := c.exists_fund_of_ne hMz hMK hMQ
  obtain ⟨RM', hRM', hM'R⟩ := c.exists_fund_of_ne hM'z hM'K hM'Q
  obtain ⟨RJ, hRJ, hJR⟩ := c.exists_fund_of_ne hJz hJK hJQ
  let ψ : spinGroup (quadPlus 4 (GaloisField 3 1)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  let τ := locAut hΩ.conjInvariant htz
  have hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField 3 1))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have hτ2 : ∀ y, τ (τ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hτr : ∀ k, τ (ψ k) ∈ ψ.range := by
    intro k
    obtain ⟨y, hy⟩ := c.locAut_mem_range htz h2t hKt
      (range_le_iSup_fund_plus (p := 3) (f := 1) (by omega) hadm c.d.ψ) (ι k)
    exact ⟨ι.symm y, by simpa [ψ] using hy⟩
  have hc : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K},
      L ∈ centralizingMembers Ω {z} → L' ∈ centralizingMembers Ω {z} →
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D →
      locImg Ω z L = R.map c.d.ψ → locImg Ω z L' = R'.map c.d.ψ → Commutes L L' →
      Commutes (R.map ι.symm.toMonoidHom) (R'.map ι.symm.toMonoidHom) :=
    fun hL hL' hR hLR hLR' hcomm => (commutes_map_equiv ι.symm).mpr
      ((c.commutes_iff_fund hL hL' hR hLR hLR').mp hcomm)
  have hfixC : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K},
      L ∈ centralizingMembers Ω {z} → locImg Ω z L = R.map c.d.ψ → Commutes β L →
      ∀ r ∈ R.map ι.symm.toMonoidHom, τ (ψ r) = ψ r := fun hL hLR hβL =>
    fixed_of_map_symm ι c.d.ψ τ hLR
      ((locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hL).mp fun n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hβL t ht.mem n hn).symm)
  have hMne : RM.map ι.symm.toMonoidHom ≠ RM'.map ι.symm.toMonoidHom := by
    intro h
    have h1 : RM = RM' := Subgroup.map_injective ι.symm.injective h
    have : M = M' := c.eq_of_locImg_eq hMz hM'z (by rw [hMR, hM'R, h1])
    obtain ⟨zM, hzM⟩ := hΩ.classical M hMz.1
    exact not_commutes_self3 hzM (this ▸ hMM')
  have hxL : x ∈ locLayer Ω z := le_centralizingLayer hJz hxJ
  obtain ⟨r₀, hr₀, hr₀x⟩ : locMk Ω z ⟨x, hxL⟩ ∈ RJ.map c.d.ψ := by
    rw [← hJR]
    exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩
  set xt : spinGroup (quadPlus 4 (GaloisField 3 1)) := ι.symm r₀ with hxt
  have hxtC : xt ∈ RJ.map ι.symm.toMonoidHom := ⟨r₀, hr₀, rfl⟩
  have hψxt : ψ xt = locMk Ω z ⟨x, hxL⟩ := by
    show c.d.ψ (ι (ι.symm r₀)) = _
    rw [MulEquiv.apply_symm_apply]
    exact hr₀x
  have hψx1 : ψ xt ≠ 1 := by
    rw [hψxt]
    intro h
    have h1 : locMk Ω z ⟨x, hxL⟩ = locMk Ω z 1 := by rw [h, map_one]
    have := EX.locMk_inj_of_member3 c.hex hJz (b := 1) (by exact hxJ) (by exact one_mem _) h1
    exact hx1 (by simpa using congrArg Subtype.val this)
  have hr₀p : r₀ ^ 3 = 1 := by
    have h1 : c.d.ψ (r₀ ^ 3) = 1 := by
      rw [map_pow, hr₀x, ← map_pow]
      have : (⟨x, hxL⟩ : ↥(locLayer Ω z)) ^ 3 = 1 := Subtype.ext (by simpa using hxp)
      rw [this, map_one]
    exact c.hY.central RJ hRJ (r₀ ^ 3) (pow_mem hr₀ 3) (c.d.ker_le (MonoidHom.mem_ker.mpr h1))
  have hxtp : xt ^ 3 = 1 := by
    rw [hxt, ← map_pow, hr₀p, map_one]
  have hψxinv : τ (ψ xt) = (ψ xt)⁻¹ := by
    rw [hψxt, ← map_inv]
    show locMk Ω z (layerAut hΩ.conjInvariant htz ⟨x, hxL⟩) = _
    congr 1
    apply Subtype.ext
    simpa [coe_layerAut] using hxinv
  obtain ⟨Rn, hRn, hRnc, hRns, hRnf, hRnn, hRnm⟩ := hmodel ψ hker τ hτ2 hτr
    (RM.map ι.symm.toMonoidHom) (RM'.map ι.symm.toMonoidHom) (RJ.map ι.symm.toMonoidHom)
    (map_symm_mem_fund_iso hm3 hcι hRM) (map_symm_mem_fund_iso hm3 hcι hRM')
    (map_symm_mem_fund_iso hm3 hcι hRJ) hMne (hc hMz hM'z hRM hMR hM'R hMM')
    (hc hMz hJz hRM hMR hJR hMJ) (hc hM'z hJz hRM' hM'R hJR hM'J) (hfixC hMz hMR hβM)
    (hfixC hM'z hM'R hβM') xt hxtC hψx1 hxtp hψxinv
  let R' : Fin 4 → Subgroup (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K := fun a =>
    (Rn a).map ι.toMonoidHom
  have hR'f : ∀ a, R' a ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D := fun a => map_mem_fund_iso hm3 hcι (hRn a)
  have hR'c : ∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (R' a) (R' b) :=
    fun a b hab h1 h2 => (commutes_map_equiv ι).mpr (hRnc a b hab h1 h2)
  have hR's : ∀ a b, edgeD 4 a b →
      ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (R' a) (R' b) := fun a b h => by
    obtain ⟨W₁, hW₁⟩ := hRns a b h
    exact ⟨_, linearBlockStandardPair_map_equiv ι hW₁⟩
  obtain ⟨j, hj, hjc, hjp, hjK⟩ := c.exists_nodes_gen3 R' hR'f (fun a b => edgeD 4 a b) hR'c hR's
  have hjmap : ∀ a, locImg Ω z (j a) = (Rn a).map ψ := fun a => by
    rw [(hj a).2.2.2]
    show ((Rn a).map ι.toMonoidHom).map c.d.ψ = _
    rw [Subgroup.map_map]
  have hfix : ∀ a : Fin 4, 1 ≤ a.val → ∀ y ∈ locImg Ω z (j a), τ y = y := by
    intro a ha y hy
    rw [hjmap] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    exact hRnf a ha g hg
  have hmemt : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} := by
    intro L hL
    have := centralizingMembers_conj hΩ.conjInvariant t z
    rw [htz] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  let a0 : Fin 4 := ⟨0, by omega⟩
  let a2 : Fin 4 := ⟨2, by omega⟩
  have hnorm : conjSub t (j a0) = j a0 := by
    have hle : (locImg Ω z (j a0)).map τ.toMonoidHom ≤ locImg Ω z (j a0) := by
      rw [hjmap]
      rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact hRnn g hg
    have heq : (locImg Ω z (j a0)).map τ.toMonoidHom = locImg Ω z (j a0) := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ τ.toMonoidHom τ.injective).toEquiv).le
    rw [locAut_locImg hΩ.conjInvariant htz] at heq
    exact locImg_injOn3 hΩ c.hex c.hP1 c.hO3 (hmemt _ (hj a0).1) (hj a0).1 heq
  have hmov : ¬ Commutes β (j a0) := by
    intro hcm
    have hfx := (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hj a0).1).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcm t ht.mem n hn).symm
    obtain ⟨g, hg, hne⟩ := hRnm
    apply hne
    have : c.d.ψ (ι g) ∈ locImg Ω z (j a0) := by
      rw [hjmap]
      exact ⟨g, hg, rfl⟩
    exact hfx _ this
  have hj2t : j a2 ≤ Subgroup.centralizer ({t} : Set G) :=
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hj a2).1).mpr (hfix a2 (by show 1 ≤ 2; omega))
  have hβj2 : Commutes β (j a2) :=
    c.commutes_partner_of_centralizes3 hMFZ hsingle D hβ ht ⟨W, hW⟩ (hj a2).1 hj2t (hjK a2)
  have hj02 : Commutes (j a0) (j a2) :=
    hjc a0 a2 (by simp [a0, a2, Fin.ext_iff]) (by simp [edgeD, a0, a2]) (by simp [edgeD, a0, a2])
  obtain ⟨w₂, hw₂⟩ := hΩ.classical (j a2) (hj a2).1.1
  obtain ⟨w₀, hw₀⟩ := hΩ.classical (j a0) (hj a0).1.1
  obtain ⟨cx₂⟩ := c.exists_ctx_member hsingle (hj a2).1.1 hw₂
  have hw₀t : Commute w₀ t :=
    (commute_of_conjSub_eq3 hw₀ hnorm).symm
  have hβj0 : β ≠ j a0 := fun h => hnKβ (h ▸ hjK a0)
  have hpair0 : ∃ W', LinearBlockStandardPair (GaloisField 3 1) W' β (j a0) :=
    sign_config_sf3 cx₂ signFacts3_plus4
      (a := K) (b := β) (d := j a0) (wa := z) (wb := t) (wd := w₀)
      (mem_centralizingMembers_of_commutes c.hK hw₂.mem (hjK a2))
      (mem_centralizingMembers_of_commutes hβ hw₂.mem hβj2)
      (mem_centralizingMembers_of_commutes (hj a0).1.1 hw₂.mem hj02) c.hz ht hw₀ hKne hβj0
      ⟨W, hW⟩ hmov (hjK a0) hzt hw₀t hKt hnorm
  refine PartnerPatternPlus3.of_locAut c (j := j) (fun a => (hj a).1) hjK hjc hjp (y := 1)
    (one_mem _) htz ?_ ?_
  · intro a ha y hy
    rw [conjSub_one] at hy
    exact hfix a ha y hy
  · intro a ha
    have : a = a0 := Fin.ext ha
    subst this
    rw [conjSub_one]
    exact hpair0

end Asm

theorem partnerPatternStmtD3_four (h3 : OddThreeFreeInput) : PartnerPatternStmtD3 4 := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_plus le_rfl hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨ι, hι, D, hcard, -⟩ := id hshape
  exact partnerPatternPlus3_four_of_model (Gaps.fundNoncentral 3) c hsingle D
    hβ ht hKβ hfix

end CFSG.ClassicalInvolution.Q3.Q3TD
