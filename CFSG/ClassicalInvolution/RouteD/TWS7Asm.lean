module

public import CFSG.ClassicalInvolution.RouteD.TWS7Grp
public import CFSG.ClassicalInvolution.RouteD.TWS6Cfg
public import CFSG.ClassicalInvolution.RouteD.GapsFrFive
public import CFSG.ClassicalInvolution.RouteD.GapsPatternDAdapted
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourLift
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Timmesfeld
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalGroups.Orthogonal

set_option linter.unusedSectionVars false

@[expose] def ModelLeafD (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ {X : Type} [Group X] (ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* X),
      ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) →
      ∀ (τ : X ≃* X), (∀ y, τ (τ y) = y) → (∀ k, τ (ψ k) ∈ ψ.range) →
      ∀ A B C : Subgroup (spinGroup (quadPlus 4 (GaloisField p f))),
        A ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) →
        B ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) →
        C ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) →
        A ≠ B → Commutes A B → Commutes A C → Commutes B C →
        (∀ r ∈ A, τ (ψ r) = ψ r) → (∀ r ∈ B, τ (ψ r) = ψ r) →
        ∀ x ∈ C, ψ x ≠ 1 → x ^ p = 1 → τ (ψ x) = (ψ x)⁻¹ →
          ∃ R : Fin 4 → Subgroup (spinGroup (quadPlus 4 (GaloisField p f))),
            (∀ a, R a ∈ fundamentalSubgroups .POmegaPlus
              (plusDatum 4 (GaloisField p f) (by norm_num))) ∧
            (∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (R a) (R b)) ∧
            (∀ a b, edgeD 4 a b → ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R b)) ∧
            (∀ a : Fin 4, 1 ≤ a.val → ∀ g ∈ R a, τ (ψ g) = ψ g) ∧
            (∀ g ∈ R ⟨0, by omega⟩, τ (ψ g) ∈ (R ⟨0, by omega⟩).map ψ) ∧
            (∃ g ∈ R ⟨0, by omega⟩, τ (ψ g) ≠ ψ g)

section Asm

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem partnerPatternD_four_of_model (hmodel : ModelLeafD p f) (hMFZ : FundNoncentral p)
    (c : TCtx p f .POmegaPlus 4 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaPlus 4 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    PartnerPatternD p f 4 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf1, by omega⟩
  have hm3 : 3 ≤ 4 := by omega
  obtain ⟨M, M', J, hMz, hMK, hMQ, hM'z, hM'K, hM'Q, hJz, hJK, hJQ, hMM', hMJ, hM'J, hβM, hβM',
    hJt, hJpair, hnβJ, x, hxJ, hx1, hxp, hxinv⟩ :=
    exists_fixed_twin_data c hsingle hshape hβ ht ⟨W, hW⟩ hfixM
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := p) (f := f) hm3
  obtain ⟨RM, hRM, hMR⟩ := c.exists_fund_of_ne hMz hMK hMQ
  obtain ⟨RM', hRM', hM'R⟩ := c.exists_fund_of_ne hM'z hM'K hM'Q
  obtain ⟨RJ, hRJ, hJR⟩ := c.exists_fund_of_ne hJz hJK hJQ
  let ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  let τ := locAut hΩ.conjInvariant htz
  have hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have hτ2 : ∀ y, τ (τ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hτr : ∀ k, τ (ψ k) ∈ ψ.range := by
    intro k
    obtain ⟨y, hy⟩ := locAut_mem_range c htz h2t hKt (range_le_iSup_fund_plus (by omega) hadm c.d.ψ)
      (ι k)
    exact ⟨ι.symm y, by simpa [ψ] using hy⟩
  have hc : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 4 p f Fact.out).K},
      L ∈ centralizingMembers Ω {z} → L' ∈ centralizingMembers Ω {z} →
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D →
      locImg Ω z L = R.map c.d.ψ → locImg Ω z L' = R'.map c.d.ψ → Commutes L L' →
      Commutes (R.map ι.symm.toMonoidHom) (R'.map ι.symm.toMonoidHom) :=
    fun hL hL' hR hLR hLR' hcomm => (commutes_map_equiv ι.symm).mpr
      ((c.commutes_iff_fund hL hL' hR hLR hLR').mp hcomm)
  have hfixC : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaPlus 4 p f Fact.out).K},
      L ∈ centralizingMembers Ω {z} → locImg Ω z L = R.map c.d.ψ → Commutes β L →
      ∀ r ∈ R.map ι.symm.toMonoidHom, τ (ψ r) = ψ r := fun hL hLR hβL =>
    fixed_of_map_symm ι c.d.ψ τ hLR
      ((locAut_fixed_iff hΩ c.hP1 htz hL).mp fun n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hβL t ht.mem n hn).symm)
  have hMne : RM.map ι.symm.toMonoidHom ≠ RM'.map ι.symm.toMonoidHom := by
    intro h
    have h1 : RM = RM' := Subgroup.map_injective ι.symm.injective h
    have : M = M' := c.eq_of_locImg_eq hMz hM'z (by rw [hMR, hM'R, h1])
    exact not_commutes_self_of_mem hΩ (hMz.1) (this ▸ hMM')
  have hxL : x ∈ locLayer Ω z := le_centralizingLayer hJz hxJ
  obtain ⟨r₀, hr₀, hr₀x⟩ : locMk Ω z ⟨x, hxL⟩ ∈ RJ.map c.d.ψ := by
    rw [← hJR]
    exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩
  set xt : spinGroup (quadPlus 4 (GaloisField p f)) := ι.symm r₀ with hxt
  have hxtC : xt ∈ RJ.map ι.symm.toMonoidHom := ⟨r₀, hr₀, rfl⟩
  have hψxt : ψ xt = locMk Ω z ⟨x, hxL⟩ := by
    show c.d.ψ (ι (ι.symm r₀)) = _
    rw [MulEquiv.apply_symm_apply]
    exact hr₀x
  have hψx1 : ψ xt ≠ 1 := by
    rw [hψxt]
    intro h
    have h1 : locMk Ω z ⟨x, hxL⟩ = locMk Ω z 1 := by rw [h, map_one]
    have := Exotic.locMk_inj_of_member c.hex hJz (b := 1) (by exact hxJ) (by exact one_mem _) h1
    exact hx1 (by simpa using congrArg Subtype.val this)
  have hr₀p : r₀ ^ p = 1 := by
    have h1 : c.d.ψ (r₀ ^ p) = 1 := by
      rw [map_pow, hr₀x, ← map_pow]
      have : (⟨x, hxL⟩ : ↥(locLayer Ω z)) ^ p = 1 := Subtype.ext (by simpa using hxp)
      rw [this, map_one]
    exact CFSG.ClassicalInvolution.Asc77.fund_noncentral_modelUniv (p := p) (e := f)
      (t := .POmegaPlus) (n := 4) trivial hadm (by simp) RJ hRJ (r₀ ^ p) (pow_mem hr₀ p)
      (c.d.ker_le (MonoidHom.mem_ker.mpr h1))
  have hxtp : xt ^ p = 1 := by
    rw [hxt, ← map_pow, hr₀p, map_one]
  have hψxinv : τ (ψ xt) = (ψ xt)⁻¹ := by
    rw [hψxt, ← map_inv]
    show locMk Ω z (layerAut hΩ.conjInvariant htz ⟨x, hxL⟩) = _
    congr 1
    apply Subtype.ext
    simpa [coe_layerAut] using hxinv
  obtain ⟨Rn, hRn, hRnc, hRns, hRnf, hRnn, hRnm⟩ := hmodel c.hp2 c.hq ψ hker τ hτ2 hτr
    (RM.map ι.symm.toMonoidHom) (RM'.map ι.symm.toMonoidHom) (RJ.map ι.symm.toMonoidHom)
    (map_symm_mem_fund_iso hm3 hcι hRM) (map_symm_mem_fund_iso hm3 hcι hRM')
    (map_symm_mem_fund_iso hm3 hcι hRJ) hMne (hc hMz hM'z hRM hMR hM'R hMM')
    (hc hMz hJz hRM hMR hJR hMJ) (hc hM'z hJz hRM' hM'R hJR hM'J) (hfixC hMz hMR hβM)
    (hfixC hM'z hM'R hβM') xt hxtC hψx1 hxtp hψxinv
  let R' : Fin 4 → Subgroup (modelUniv .POmegaPlus 4 p f Fact.out).K := fun a =>
    (Rn a).map ι.toMonoidHom
  have hR'f : ∀ a, R' a ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 p f Fact.out).D := fun a => map_mem_fund_iso hm3 hcι (hRn a)
  have hR'c : ∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (R' a) (R' b) :=
    fun a b hab h1 h2 => (commutes_map_equiv ι).mpr (hRnc a b hab h1 h2)
  have hR's : ∀ a b, edgeD 4 a b →
      ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (R' a) (R' b) := fun a b h => by
    obtain ⟨W₁, hW₁⟩ := hRns a b h
    exact ⟨_, linearBlockStandardPair_map_equiv ι hW₁⟩
  obtain ⟨j, hj, hjc, hjp, hjK⟩ := c.exists_nodes R' hR'f (fun a b => edgeD 4 a b) hR'c hR's
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
    exact locImg_injOn hΩ c.hP1 (hmemt _ (hj a0).1) (hj a0).1 heq
  have hmov : ¬ Commutes β (j a0) := by
    intro hcm
    have hfx := (locAut_fixed_iff hΩ c.hP1 htz (hj a0).1).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcm t ht.mem n hn).symm
    obtain ⟨g, hg, hne⟩ := hRnm
    apply hne
    have : c.d.ψ (ι g) ∈ locImg Ω z (j a0) := by
      rw [hjmap]
      exact ⟨g, hg, rfl⟩
    exact hfx _ this
  have hj2t : j a2 ≤ Subgroup.centralizer ({t} : Set G) :=
    (locAut_fixed_iff hΩ c.hP1 htz (hj a2).1).mpr (hfix a2 (by show 1 ≤ 2; omega))
  have hβj2 : Commutes β (j a2) :=
    commutes_partner_of_centralizes hMFZ c hsingle hshape hβ ht ⟨W, hW⟩ (hj a2).1 hj2t (hjK a2)
  have hj02 : Commutes (j a0) (j a2) :=
    hjc a0 a2 (by simp [a0, a2, Fin.ext_iff]) (by simp [edgeD, a0, a2]) (by simp [edgeD, a0, a2])
  obtain ⟨w₂, hw₂⟩ := hΩ.classical (j a2) (hj a2).1.1
  obtain ⟨w₀, hw₀⟩ := hΩ.classical (j a0) (hj a0).1.1
  obtain ⟨cx₂⟩ := exists_ctx_member c hsingle hshape (hj a2).1.1 hw₂
  have hw₀t : Commute w₀ t :=
    (commute_of_conjSub_eq' h2 (c.hex _ (hj a0).1.1) hw₀ hnorm).symm
  have hβj0 : β ≠ j a0 := fun h => hnKβ (h ▸ hjK a0)
  have hpair0 : ∃ W', LinearBlockStandardPair (GaloisField p f) W' β (j a0) :=
    TWS6.sign_config' cx₂ (TWS6.signFacts_plus c.hp2 (le_refl 4) c.hq)
      (a := K) (b := β) (d := j a0) (wa := z) (wb := t) (wd := w₀)
      (mem_centralizingMembers_of_commutes c.hK hw₂.mem (hjK a2))
      (mem_centralizingMembers_of_commutes hβ hw₂.mem hβj2)
      (mem_centralizingMembers_of_commutes (hj a0).1.1 hw₂.mem hj02) c.hz ht hw₀ hKne hβj0
      ⟨W, hW⟩ hmov (hjK a0) hzt hw₀t hKt hnorm
  refine PartnerPatternD.of_locAut c (j := j) (fun a => (hj a).1) hjK hjc hjp (y := 1)
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

end CFSG.ClassicalInvolution.RouteD.TWS7
