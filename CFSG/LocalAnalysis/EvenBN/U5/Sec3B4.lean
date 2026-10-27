module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4Model
public import CFSG.LocalAnalysis.EvenBN.U5.Prelim
public import CFSG.LocalAnalysis.EvenBN.Common.CosetFactorization
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.Semilinear
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3One4
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo
  le_normalizer_oTwo)
open scoped commutatorElement

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

namespace Data

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem conj_η_eq (d : Data G h) {n : G} (hn : n ∈ normalizer (d.L : Set G)) {x : Gam h}
    (hx : Phi h x = d.act ⟨n, hn⟩) (g : hypSU h 2 1) : n * d.η g * n⁻¹ = d.η (actΓ h x g) := by
  have e := d.coe_e_symm_act_apply ⟨n, hn⟩ (hypProj h 2 1 g)
  rw [← hx, Phi_apply] at e
  rw [η_apply, η_apply]
  exact e.symm

theorem innM_eq_of_η_eq (d : Data G h) {g g' : hypSU h 2 1} (he : d.η g = d.η g') :
    innM h g = innM h g' := by
  have h1 : hypProj h 2 1 g = hypProj h 2 1 g' := by
    have e2 : d.e.symm (hypProj h 2 1 g) = d.e.symm (hypProj h 2 1 g') :=
      Subtype.ext (by rw [← η_apply, ← η_apply, he])
    exact d.e.symm.injective e2
  rw [innM, MonoidHom.comp_apply, MonoidHom.comp_apply, h1]

theorem Zp_le_P (d : Data G h) : d.Zp ≤ d.P := d.Zp_le_A₂.trans d.A₂_le_P

theorem Zp_le_L (d : Data G h) : d.Zp ≤ d.L := d.Zp_le_P.trans d.P_le_L

theorem Zp_le_A₁ (d : Data G h) : d.Zp ≤ d.A₁ := d.Zp_le_Z₂p.trans d.Z₂p_le_A₁

theorem isElementaryAbelian_Zp (d : Data G h) : CFSG.IsElementaryAbelian 2 d.Zp :=
  isElementaryAbelian_of_forall (fun x hx y hy => d.A₁_comm_sq.1 x (d.Zp_le_A₁ hx) y
    (d.Zp_le_A₁ hy)) fun x hx => d.A₁_comm_sq.2 x (d.Zp_le_A₁ hx)

theorem I_le_normalizer_P (d : Data G h) : d.I ≤ normalizer (d.P : Set G) :=
  (le_sup_right.trans d.normalizer_P.ge).trans inf_le_right

end Data

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem I_le_normalizer_Zp (d : Data G h) : d.I ≤ normalizer (d.Zp : Set G) := by
  have hZ : CFSG.centerIn d.P = d.Zp := d.sec2_2_three.2.2.2.2
  intro i hi
  refine mem_normalizer_of_conj_le fun z hz => ?_
  rw [← hZ] at hz ⊢
  exact conj_mem_centerIn (d.I_le_normalizer_P hi) hz

theorem Hyp.ZtP_le_B₁ (hd : d.Hyp) : d.ZtP ≤ d.B₁ := by
  rw [hd.ZtP_eq]
  exact sup_le_sup_left d.Zp_le_A₁ _

theorem Hyp.t_mem_ZtP (hd : d.Hyp) : d.t ∈ d.ZtP := by
  rw [hd.ZtP_eq]
  exact mem_sup_left (mem_zpowers _)

theorem Hyp.conj_t_mem_ZtP (hd : d.Hyp) {g : G} (hg : g⁻¹ * d.t * g ∈ d.ZtP) :
    ∃ a ∈ d.Zp, g⁻¹ * d.t * g = d.t * a := by
  have h5 := (hd.sec3_1').2.2.2.2.1
  have hmem : g⁻¹ * d.t * g ∈ {x | ∃ g : G, x = g⁻¹ * d.t * g} ∩ (d.B₁ : Set G) :=
    ⟨⟨g, rfl⟩, hd.ZtP_le_B₁ hg⟩
  rw [h5] at hmem
  obtain ⟨a, ha, hga⟩ := hmem
  refine ⟨a, ?_, hga⟩
  rw [← hd.ZtP_inf_P]
  refine ⟨?_, d.A₁_le_P ha⟩
  have : a = d.t * (g⁻¹ * d.t * g) := by
    rw [hga, ← mul_assoc, hd.t_mul_t, one_mul]
  rw [this]
  exact mul_mem hd.t_mem_ZtP hg

theorem Hyp.exists_conj_eq_t_mul (hd : d.Hyp) {a : G} (ha : a ∈ d.Zp) :
    ∃ g : G, g⁻¹ * d.t * g = d.t * a := by
  have h5 := (hd.sec3_1').2.2.2.2.1
  have hmem : d.t * a ∈ {x | ∃ g : G, x = g⁻¹ * d.t * g} ∩ (d.B₁ : Set G) := by
    rw [h5]
    exact ⟨a, d.Zp_le_A₁ ha, rfl⟩
  obtain ⟨⟨g, hg⟩, -⟩ := hmem
  exact ⟨g, hg.symm⟩

theorem Hyp.normalizer_ZtP_le (hd : d.Hyp) :
    normalizer (d.ZtP : Set G) ≤ normalizer (d.Zp : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_le fun z hz => ?_
  have hzZ : z ∈ d.ZtP := by
    rw [hd.ZtP_eq]
    exact mem_sup_right hz
  have hm : n * z * n⁻¹ ∈ d.ZtP := (mem_normalizer_iff.1 hn z).1 hzZ
  rw [hd.ZtP_eq] at hm
  obtain ⟨a, ha, he | he⟩ := hd.exists_of_mem_zpowers_sup d.Zp_le_L hm
  · rw [he]
    exact ha
  · exfalso
    obtain ⟨g, hg⟩ := hd.exists_conj_eq_t_mul ha
    have hzeq : z = (g * n)⁻¹ * d.t * (g * n) := by
      have e1 : n * z * n⁻¹ = g⁻¹ * d.t * g := by rw [he, hg]
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = n⁻¹ * (g⁻¹ * d.t * g) * n := by rw [e1]
        _ = (g * n)⁻¹ * d.t * (g * n) := by group
    have hz' : (g * n)⁻¹ * d.t * (g * n) ∈ d.ZtP := hzeq ▸ hzZ
    obtain ⟨b, hb, hbe⟩ := hd.conj_t_mem_ZtP hz'
    have hzt : z = d.t * b := hzeq.trans hbe
    have htZ : d.t ∈ d.Zp := by
      have := mul_mem hz (inv_mem hb)
      rwa [hzt, mul_inv_cancel_right] at this
    exact hd.t_not_mem_L (d.Zp_le_L htZ)

theorem Hyp.cosetData (hd : d.Hyp) : CosetData (normalizer (d.ZtP : Set G)) d.Zp d.t := by
  refine ⟨hd.t_mul_t, d.Zp_le_L.trans hd.L_le_centralizer, d.isElementaryAbelian_Zp,
    hd.normalizer_ZtP_le, fun g hg => ?_⟩
  have hg' : g⁻¹ * d.t * g ∈ d.ZtP := by
    have := (mem_normalizer_iff.1 (inv_mem hg) d.t).1 hd.t_mem_ZtP
    rwa [inv_inv] at this
  obtain ⟨a, ha, hga⟩ := hd.conj_t_mem_ZtP hg'
  rw [hga]
  have hat : a * d.t = d.t * a := hd.comm_t (d.Zp_le_L ha)
  rw [mul_assoc, hat, ← mul_assoc, hd.t_mul_t, one_mul]
  exact ha

theorem Hyp.T_le_normalizer_B₁ (hd : d.Hyp) : d.T ≤ normalizer (d.B₁ : Set G) := by
  intro x hx
  set φ : G →* G := (MulAut.conj x).toMonoidHom with hφ
  have hle : d.B₁.map φ ≤ d.T := by
    rintro _ ⟨b, hb, rfl⟩
    change x * b * x⁻¹ ∈ d.T
    exact mul_mem (mul_mem hx (hd.B₁_le_T hb)) (inv_mem hx)
  have := hd.isElementaryAbelian_B₁
  have heq := (hd.sec3_1').2.2.1 _ hle (CFSG.IsElementaryAbelian.map _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hd.card_B₁])
  refine mem_normalizer_of_conj_le fun b hb => ?_
  rw [← heq]
  exact ⟨b, hb, rfl⟩

theorem Hyp.T_le_normalizer_B₃ (hd : d.Hyp) : d.T ≤ normalizer (d.B₃ : Set G) := by
  have hR := hd.R_eq_B₃ (involutionsConjIntoV h) (outerInvolutionFusion h) (perfectLeInn h)
    (twoCentralizerV h)
  intro x hx
  refine mem_normalizer_of_conj_le fun b hb => ?_
  rw [← hR] at hb ⊢
  have hbT : b ∈ d.T := hb.1
  have hbC : b ∈ centralizer (d.B₁ : Set G) := hb.2
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hx hbT) (inv_mem hx), ?_⟩
  have hxN := hd.T_le_normalizer_B₁ hx
  exact (mem_normalizer_iff.1 (Prelim.normalizer_le_normalizer_centralizer d.B₁ hxN) b).1 hbC

theorem Hyp.two_dvd_index_T (hd : d.Hyp) : 2 ∣ d.T.index := by
  set N := normalizer (d.B₃ : Set G) with hN
  have hcard : Nat.card {x | ∃ g ∈ N, x = g⁻¹ * d.t * g} = (2 ^ f) ^ 4 := by
    rw [(hd.sec3_1').2.2.2.1, ← d.card_A₁]
    refine Nat.card_congr ⟨fun x => ⟨d.t⁻¹ * x, ?_⟩, fun a => ⟨d.t * a, a, a.2, rfl⟩, ?_, ?_⟩
    · obtain ⟨_, a, ha, rfl⟩ := x
      simpa using ha
    · rintro ⟨_, a, ha, rfl⟩
      simp
    · rintro ⟨a, ha⟩
      simp
  rw [U4.card_conj_set_eq_relIndex] at hcard
  have hTN : d.T ≤ centralizer ({d.t} : Set G) ⊓ N :=
    le_inf hd.T_le_centralizer hd.T_le_normalizer_B₃
  have h1 : (centralizer ({d.t} : Set G) ⊓ N).relIndex N = (2 ^ f) ^ 4 := by
    rw [Subgroup.inf_relIndex_right, hcard]
  have h2 : (centralizer ({d.t} : Set G) ⊓ N).relIndex N ∣ d.T.relIndex N := by
    rw [← Subgroup.relIndex_mul_relIndex d.T _ N hTN inf_le_right]
    exact dvd_mul_left _ _
  have h3 : d.T.relIndex N ∣ d.T.index := by
    rw [← Subgroup.relIndex_mul_index (hTN.trans inf_le_right)]
    exact dvd_mul_right _ _
  refine (dvd_trans ?_ h2).trans h3
  rw [h1]
  exact dvd_pow (dvd_pow_self 2 (by have := hd.two_le; omega)) (by norm_num)

theorem Hyp.exists_mem_normalizer_T (hd : d.Hyp) :
    ∃ x ∈ normalizer (d.T : Set G), x⁻¹ * d.t * x ≠ d.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hd.isPGroup_T
  have hdvd : 2 ^ (n + 1) ∣ Nat.card G := by
    rw [← d.T.card_mul_index, hn, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd.two_dvd_index_T
  obtain ⟨M, hM, hTM⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hn
  have hidx : (d.T.subgroupOf M).index = 2 := by
    have h1 := Subgroup.card_mul_index (d.T.subgroupOf M)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv, hn, hM, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hnorm : (d.T.subgroupOf M).Normal := Subgroup.normal_of_index_eq_two hidx
  have hMN : M ≤ normalizer (d.T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).1 hnorm
  by_contra hcon
  push Not at hcon
  have hMC : M ≤ centralizer ({d.t} : Set G) := fun x hx => by
    have := hcon x (hMN hx)
    rw [mem_centralizer_singleton_iff]
    calc x * d.t = x * (x⁻¹ * d.t * x) := by rw [this]
      _ = d.t * x := by group
  have hM2 : IsPGroup 2 M := IsPGroup.of_card hM
  have := hd.T_syl.eq_of_le hTM hMC hM2
  rw [this, hn] at hM
  exact absurd hM (by
    have : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega)

theorem Hyp.I₂_le (hd : d.Hyp) :
    d.I₂ ≤ centralizer ({d.t} : Set G) ⊓ normalizer (d.tP : Set G) := by
  have hI₂I : d.I₂ ≤ d.I := d.pull_mono (torusEq_le _)
  have hIL : d.I ≤ d.L := d.pull_le_L _
  have hIP : d.I ≤ normalizer (d.P : Set G) :=
    (le_sup_right.trans d.normalizer_P.ge).trans inf_le_right
  intro i hi
  have hit : i ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (hIL (hI₂I hi))
  refine ⟨hit, mem_normalizer_of_conj_le fun y hy => ?_⟩
  obtain ⟨p, hp, hyp | hyp⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hy <;> subst y
  · exact mem_sup_right ((mem_normalizer_iff.1 (hIP (hI₂I hi)) p).1 hp)
  · have hct : i * d.t * i⁻¹ = d.t := by
      rw [mem_centralizer_singleton_iff.1 hit, mul_inv_cancel_right]
    have e : i * (d.t * p) * i⁻¹ = (i * d.t * i⁻¹) * (i * p * i⁻¹) := by group
    rw [e, hct]
    exact mul_mem (mem_sup_left (mem_zpowers _))
      (mem_sup_right ((mem_normalizer_iff.1 (hIP (hI₂I hi)) p).1 hp))

theorem Hyp.transitive_tP (hd : d.Hyp) :
    ∀ y ∈ d.Zp, ∃ g ∈ normalizer (d.tP : Set G), g⁻¹ * d.t * g = d.t * y := by
  obtain ⟨x, hxT, hxt⟩ := hd.exists_mem_normalizer_T
  have hx := hd.normalizer_T_le hxT
  have hxZ : x⁻¹ * d.t * x ∈ d.ZtP := by
    have := (mem_normalizer_iff.1 (d.normalizer_tP_le_normalizer_ZtP (inv_mem hx)) d.t).1
      hd.t_mem_ZtP
    rwa [inv_inv] at this
  obtain ⟨z₀, hz₀, hxz⟩ := hd.conj_t_mem_ZtP hxZ
  have hz₀1 : z₀ ≠ 1 := fun e => hxt (by rw [hxz, e, mul_one])
  obtain ⟨-, htr, -, -⟩ := d.sec2_1_three hd.two_le
  intro y hy
  by_cases hy1 : y = 1
  · exact ⟨1, one_mem _, by rw [hy1]; group⟩
  obtain ⟨i₀, hi₀, hz₀e⟩ := htr z₀ hz₀ hz₀1
  obtain ⟨i, hi, hye⟩ := htr y hy hy1
  set c := i₀⁻¹ * i with hc
  have hcI : c ∈ d.I₂ := mul_mem (inv_mem hi₀) hi
  obtain ⟨hct, hcN⟩ := hd.I₂_le hcI
  refine ⟨x * c, mul_mem hx hcN, ?_⟩
  have hct' : c⁻¹ * d.t * c = d.t := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hct, inv_mul_cancel_left]
  calc (x * c)⁻¹ * d.t * (x * c) = c⁻¹ * (x⁻¹ * d.t * x) * c := by group
    _ = c⁻¹ * d.t * c * (c⁻¹ * z₀ * c) := by rw [hxz]; group
    _ = d.t * y := by rw [hct', hz₀e, hye, hc]; group


theorem exists_pow_eq_one_of_mem_U {g : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1) :
    ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := CFSG.RankThree.CentralLiftU.isPGroup_hypUnitriangular (h := h) (r := 2)
    (ε := 1) (by norm_num) ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem Hyp.eq_of_η_eq_of_two (hd : d.Hyp) {g g' : hypSU h 2 1} (he : d.η g = d.η g') {k : ℕ}
    (hg : g ^ 2 ^ k = 1) (hg' : g' ^ 2 ^ k = 1) : g = g' :=
  eq_of_innM_eq_of_two hd.center_hypPSU (d.innM_eq_of_η_eq he) hg hg'

theorem Hyp.act_mem_ZPsub (hd : d.Hyp) {x : G} (hxN : x ∈ normalizer (d.ZtP : Set G))
    (hxL : x ∈ normalizer (d.L : Set G)) {y : Gam h} (hy : Phi h y = d.act ⟨x, hxL⟩)
    {z : hypSU h 2 1} (hz : z ∈ ZPsub h) : actΓ h y z ∈ ZPsub h := by
  have h1 : x * d.η z * x⁻¹ ∈ d.Zp :=
    (mem_normalizer_iff.1 (hd.normalizer_ZtP_le hxN) _).1 ⟨z, hz, rfl⟩
  rw [d.conj_η_eq hxL hy] at h1
  obtain ⟨z', hz', he⟩ := h1
  have e : actΓ h y z = z' := by
    refine eq_of_innM_eq_of_sq hd.center_hypPSU (d.innM_eq_of_η_eq he.symm) ?_
      (Vsub_sq (ZPsub_le_Vsub hz'))
    rw [← CFSG.RankThree.PartOne.U5K.Hyp.act_mul, Vsub_sq (ZPsub_le_Vsub hz),
      CFSG.RankThree.PartOne.U5K.Hyp.act_one]
  rw [e]
  exact hz'

theorem Hyp.lift_flag (hd : d.Hyp) {x : G} (hxN : x ∈ normalizer (d.ZtP : Set G))
    (hxL : x ∈ normalizer (d.L : Set G)) {y : Gam h} (hy : Phi h y = d.act ⟨x, hxL⟩) :
    (∀ a, a ≠ ιe₁ → lmat y a ιe₁ = 0) ∧ ∀ b, b ≠ ιf₁ → lmat y ιf₁ b = 0 := by
  have hcol := lmat_col_e₁ (hd.act_mem_ZPsub hxN hxL hy z₁SU_mem_ZPsub)
  exact ⟨hcol, lmat_row_f₁ hcol⟩

theorem Hyp.conj_mem_A₂ (hd : d.Hyp) {x : G} (hxN : x ∈ normalizer (d.ZtP : Set G))
    (hxC : x ∈ centralizer ({d.t} : Set G)) {a : G} (ha : a ∈ d.A₂) : x * a * x⁻¹ ∈ d.A₂ := by
  have hxL := hd.centralizer_le_normalizer hxC
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨x, hxL⟩)
  obtain ⟨hcol, hrow⟩ := hd.lift_flag hxN hxL hy
  obtain ⟨v, hv, rfl⟩ := ha
  rw [d.conj_η_eq hxL hy]
  exact ⟨_, act_mem_A₂sub hcol hrow hv, rfl⟩

theorem Hyp.conj_mem_B₂ (hd : d.Hyp) {x : G} (hxN : x ∈ normalizer (d.ZtP : Set G))
    (hxC : x ∈ centralizer ({d.t} : Set G)) {b : G} (hb : b ∈ d.B₂) : x * b * x⁻¹ ∈ d.B₂ := by
  have hxt : x * d.t * x⁻¹ = d.t := by
    rw [mem_centralizer_singleton_iff.1 hxC, mul_inv_cancel_right]
  obtain ⟨a, ha, hba | hba⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hb <;> subst b
  · exact mem_sup_right (hd.conj_mem_A₂ hxN hxC ha)
  · have e : x * (d.t * a) * x⁻¹ = (x * d.t * x⁻¹) * (x * a * x⁻¹) := by group
    rw [e, hxt]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (hd.conj_mem_A₂ hxN hxC ha))

theorem tP_le_normalizer_ZtP (d : Data G h) : d.tP ≤ normalizer (d.ZtP : Set G) :=
  (le_normalizer).trans d.normalizer_tP_le_normalizer_ZtP

theorem Hyp.mem_K₀_of_mem_L (hd : d.Hyp) {g : G} (hgL : g ∈ d.L)
    (hgZ : ∀ z ∈ d.Zp, z * g = g * z) :
    g ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) := by
  have hgt : g ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer hgL
  have hgC : g ∈ centralizer (d.Zp : Set G) := mem_centralizer_iff.2 fun z hz => hgZ z hz
  refine ⟨⟨Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz => ?_), hgC⟩,
    hgt⟩
  rw [hd.ZtP_eq] at hz
  obtain ⟨a, ha, hza | hza⟩ := hd.exists_of_mem_zpowers_sup d.Zp_le_L hz <;> subst z
  · exact hgZ a ha
  · have h1 : d.t * g = g * d.t := (mem_centralizer_singleton_iff.1 hgt).symm
    calc d.t * a * g = d.t * (g * a) := by rw [mul_assoc, hgZ a ha]
      _ = g * (d.t * a) := by rw [← mul_assoc, h1, mul_assoc]

theorem Hyp.P_le_K₀ (hd : d.Hyp) :
    d.P ≤ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) := by
  have hZ : CFSG.centerIn d.P = d.Zp := d.sec2_2_three.2.2.2.2
  intro p hp
  refine hd.mem_K₀_of_mem_L (d.P_le_L hp) fun z hz => ?_
  rw [← hZ] at hz
  exact (mem_centralizer_iff.1 hz.2 p hp).symm

theorem Hyp.s_mem_K₀ (hd : d.Hyp) :
    d.s ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) := by
  refine hd.mem_K₀_of_mem_L (d.η_mem _) fun z hz => ?_
  obtain ⟨z', hz', rfl⟩ := hz
  rw [Data.s, ← map_mul, ← map_mul, N₂sub_comm_ZPsub sSU_mem_N₂sub hz']

theorem Hyp.B₂_le_K₀ (hd : d.Hyp) :
    d.B₂ ≤ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) := by
  have hB := hd.B₂_spec.2.1
  have hZA : CFSG.centerIn d.A₂ = d.Zp := d.sec2_2_three.2.2.2.1
  refine le_inf (le_inf (hB.trans d.tP_le_normalizer_ZtP) (sup_le ?_ ?_))
    (hB.trans hd.tP_le_centralizer)
  · rw [zpowers_le]
    exact mem_centralizer_iff.2 fun z hz => hd.comm_t (d.Zp_le_L hz)
  · intro a ha
    refine mem_centralizer_iff.2 fun z hz => ?_
    rw [← hZA] at hz
    exact (mem_centralizer_iff.1 hz.2 a ha).symm

theorem Hyp.isPGroup_B₂ (hd : d.Hyp) : IsPGroup 2 d.B₂ :=
  IsPGroup.of_card (n := 1 + f * 7) (by rw [hd.card_B₂, pow_add, pow_one, pow_mul])

theorem Hyp.mem_B₂_of_inner (hd : d.Hyp) {R : Subgroup G}
    (hRK : R ≤ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G))
    (hKR : normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) ≤ normalizer (R : Set G)) (hR2 : IsPGroup 2 R) {x : G}
    (hxR : x ∈ R) (hxL : x ∈ normalizer (d.L : Set G)) (hxP : d.act ⟨x, hxL⟩ ∈ Pi h) :
    x ∈ d.B₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute d.L_commute_centralizer
    ((d.act_mem_Pi_iff hxL).1 hxP)
  have hlt : l ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer hl
  have hct : c ∈ zpowers d.t := by
    rw [← (hd.sec3_1').1]
    refine ⟨hc, ?_⟩
    have := mul_mem (inv_mem hlt) (hRK hxR).2
    rwa [inv_mul_cancel_left] at this
  have htK : d.t ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) := by
    refine ⟨⟨d.tP_le_normalizer_ZtP (mem_sup_left (mem_zpowers _)),
      mem_centralizer_iff.2 fun z hz => ?_⟩, mem_centralizer_singleton_iff.2 rfl⟩
    exact hd.comm_t (d.Zp_le_L hz)
  set S : Subgroup G := (R ⊔ zpowers d.t) ⊓ d.L with hS
  have hS2 : IsPGroup 2 S :=
    (hR2.to_sup_of_normal_left' hd.isPGroup_zpowers_t (zpowers_le.2 (hKR htK))).to_inf_left
  have hSn : ∀ g, g ∈ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) → g ∈ d.L → g ∈ normalizer (S : Set G) := by
    intro g hgK hgL
    refine mem_normalizer_of_conj_le fun y hy => Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hR' : g ∈ normalizer ((R ⊔ zpowers d.t : Subgroup G) : Set G) := by
        refine mem_normalizer_of_conj_le fun w hw => ?_
        have hle : R ⊔ zpowers d.t ≤ (R ⊔ zpowers d.t).comap (MulAut.conj g).toMonoidHom := by
          refine sup_le (fun r hr => mem_sup_left ((mem_normalizer_iff.1 (hKR hgK) r).1 hr))
            (zpowers_le.2 (mem_sup_right ?_))
          change g * d.t * g⁻¹ ∈ zpowers d.t
          rw [mem_centralizer_singleton_iff.1 hgK.2, mul_inv_cancel_right]
          exact mem_zpowers _
        exact hle hw
      exact (mem_normalizer_iff.1 hR' y).1 hy.1
    · have hyL : y ∈ d.L := hy.2
      exact mul_mem (mul_mem hgL hyL) (inv_mem hgL)
  have hSP : S ≤ d.P := by
    have hPS : d.P ≤ normalizer (S : Set G) := fun p hp => hSn p (hd.P_le_K₀ hp) (d.P_le_L hp)
    have h2 : IsPGroup 2 (d.P ⊔ S : Subgroup G) := d.isPGroup_P.to_sup_of_normal_right' hS2 hPS
    have := d.isSylowOf_P.eq_of_le le_sup_left (sup_le d.P_le_L inf_le_right) h2
    rw [← this]
    exact le_sup_right
  have hsS := hSn d.s hd.s_mem_K₀ (d.η_mem _)
  have hlS : l ∈ S := by
    refine ⟨?_, hl⟩
    have := mul_mem (mem_sup_left hxR : l * c ∈ R ⊔ zpowers d.t) (mem_sup_right (inv_mem hct))
    rwa [mul_inv_cancel_right] at this
  obtain ⟨g, hgU, rfl⟩ := hSP hlS
  have hs' : d.s⁻¹ * d.η g * d.s ∈ S := by
    have := (mem_normalizer_iff.1 (inv_mem hsS) (d.η g)).1 hlS
    rwa [inv_inv] at this
  obtain ⟨g', hg'U, hg'e⟩ := hSP hs'
  have hsinv : (sSU h)⁻¹ = sSU h := inv_eq_of_mul_eq_one_right sSU_mul_self
  have hsη : (d.η (sSU h))⁻¹ = d.η (sSU h) := by rw [← map_inv, hsinv]
  have e : d.η g' = d.η (sSU h * g * (sSU h)⁻¹) := by
    rw [hg'e, map_mul, map_mul, map_inv, Data.s, hsη]
  have hgg : g' = sSU h * g * (sSU h)⁻¹ := by
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_U hg'U
    obtain ⟨k', hk'⟩ := exists_pow_eq_one_of_mem_U hgU
    refine hd.eq_of_η_eq_of_two e (k := k + k') ?_ ?_
    · rw [pow_add, pow_mul, hk, one_pow]
    · rw [conj_pow, pow_add, mul_comm, pow_mul, hk', one_pow, mul_one, mul_inv_cancel]
  have hgA : g ∈ A₂sub h := mem_A₂sub_of_conj_s hgU (hgg ▸ hg'U)
  exact mul_mem (mem_sup_right ⟨g, hgA, rfl⟩) (mem_sup_left hct)

theorem Hyp.act_mem_Pi_of_normal (hd : d.Hyp) {R : Subgroup G}
    (hRK : R ≤ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G))
    (hKR : normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) ≤ normalizer (R : Set G)) (hR2 : IsPGroup 2 R) {x : G}
    (hxR : x ∈ R) (hxL : x ∈ normalizer (d.L : Set G)) : d.act ⟨x, hxL⟩ ∈ Pi h := by
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨x, hxL⟩)
  obtain ⟨hcol, hrow⟩ := hd.lift_flag (hRK hxR).1.1 hxL hy
  have hN : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 →
      ∃ v ∈ A₂sub h, actΓ h y n = v * n := by
    intro n hn hnU
    have hηn := hd.mem_K₀_of_mem_L (d.η_mem n) fun z hz => by
      obtain ⟨z', hz', rfl⟩ := hz
      rw [← map_mul, ← map_mul, N₂sub_comm_ZPsub hn hz']
    set w := x * d.η n * x⁻¹ * (d.η n)⁻¹ with hw
    have hwR : w ∈ R := by
      have h1 := (mem_normalizer_iff.1 (hKR hηn) x⁻¹).1 (inv_mem hxR)
      have e : w = x * (d.η n * x⁻¹ * (d.η n)⁻¹) := by rw [hw]; group
      rw [e]
      exact mul_mem hxR h1
    have hwL : w ∈ d.L := by
      have h1 : x * d.η n * x⁻¹ ∈ d.L := (mem_normalizer_iff.1 hxL _).1 (d.η_mem n)
      exact mul_mem h1 (inv_mem (d.η_mem n))
    have hwB := hd.mem_B₂_of_inner hRK hKR hR2 hwR (le_normalizer hwL)
      ((d.act_mem_Pi_iff _).2 (mem_sup_left hwL))
    obtain ⟨a, ha, hwa | hwa⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hwB
    · obtain ⟨v, hv, hva⟩ := hwa ▸ ha
      refine ⟨v, hv, ?_⟩
      have e : d.η (actΓ h y n) = d.η (v * n) := by
        rw [← d.conj_η_eq hxL hy, map_mul, hva, hw]
        group
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_U hnU
      obtain ⟨k', hk'⟩ := exists_pow_eq_one_of_mem_U (mul_mem (A₂sub_le_U hv) hnU)
      refine hd.eq_of_η_eq_of_two e (k := k + k') ?_ ?_
      · rw [← act_pow, pow_add, pow_mul, hk, one_pow, CFSG.RankThree.PartOne.U5K.Hyp.act_one]
      · rw [pow_add, mul_comm, pow_mul, hk', one_pow]
    · exfalso
      have : d.t ∈ d.L := by
        have := mul_mem hwL (inv_mem (d.A₂_le_L ha))
        rwa [hwa, mul_inv_cancel_right] at this
      exact hd.t_not_mem_L this
  have hσ := right_eq_one_of_act_N₂ hcol hrow hN
  obtain ⟨k, hk⟩ := hR2 ⟨x, hxR⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine Dlin_two_mem_Pi ((mem_Dlin_iff hy).2 hσ) (k := k) ?_
  rw [← map_pow]
  have e : (⟨x, hxL⟩ : normalizer (d.L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
  rw [e, map_one]

theorem Hyp.le_B₂_of_normal (hd : d.Hyp) {R : Subgroup G}
    (hRK : R ≤ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G))
    (hKR : normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) ≤ normalizer (R : Set G)) (hR2 : IsPGroup 2 R) :
    R ≤ d.B₂ := fun _ hxR =>
  have hxL := hd.centralizer_le_normalizer (hRK hxR).2
  hd.mem_B₂_of_inner hRK hKR hR2 hxR hxL (hd.act_mem_Pi_of_normal hRK hKR hR2 hxR hxL)

theorem Hyp.oTwo_K₀ (hd : d.Hyp) :
    oTwo (normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G)) = d.B₂ := by
  refine le_antisymm (hd.le_B₂_of_normal (oTwo_le _) (le_normalizer_oTwo _) (isPGroup_oTwo _))
    (le_oTwo hd.B₂_le_K₀ (fun x hx => mem_normalizer_of_conj_le fun b hb =>
      hd.conj_mem_B₂ hx.1.1 hx.2 hb) hd.isPGroup_B₂)

theorem Hyp.normalizer_ZtP_le_normalizer_B₂ (hd : d.Hyp) :
    normalizer (d.ZtP : Set G) ≤ normalizer (d.B₂ : Set G) := by
  intro g hg
  have hgK : g ∈ normalizer ((normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_le fun k hk => hd.cosetData.conj_mem_kernel hg hk
  refine mem_normalizer_of_conj_le fun b hb => ?_
  rw [← hd.oTwo_K₀] at hb ⊢
  exact conj_mem_oTwo_of_mem_normalizer hgK hb

theorem Hyp.le_B₂_of_normal' (hd : d.Hyp) {R : Subgroup G}
    (hR : R ≤ normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G))
    (hRn : normalizer (d.ZtP : Set G) ⊓ centralizer ({d.t} : Set G) ≤ normalizer (R : Set G))
    (hR2 : IsPGroup 2 R) : R ≤ d.B₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 d.Zp := IsPGroup.of_card (n := f) (by rw [d.card_Zp])
  have hZ1 : d.Zp ≠ ⊥ := fun e => by
    have := d.card_Zp
    rw [e, Subgroup.card_bot] at this
    have h4 := hd.four_le
    omega
  have hW := Prelim.inf_centralizer_ne_bot_of_pow_mem hZ2 hZ1
    (fun r hr => hd.normalizer_ZtP_le (hR hr).1) fun r hr => by
      obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
      exact ⟨k, by rw [show r ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk]; exact one_mem _⟩
  obtain ⟨w₀, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
  set w : G := (w₀ : G) with hwdef
  have hwZ : w ∈ d.Zp := (Subgroup.mem_inf.1 w₀.2).1
  have hwR : w ∈ centralizer (R : Set G) := (Subgroup.mem_inf.1 w₀.2).2
  have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
  obtain ⟨-, htr, -, -⟩ := d.sec2_1_three hd.two_le
  have hRZ : R ≤ centralizer (d.Zp : Set G) := by
    intro r hr
    refine mem_centralizer_iff.2 fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1, one_mul, mul_one]
    obtain ⟨i₀, hi₀, hwe⟩ := htr w hwZ hw1'
    obtain ⟨i, hi, hze⟩ := htr z hz hz1
    set c := i₀⁻¹ * i with hc
    have hcI : c ∈ d.I₂ := mul_mem (inv_mem hi₀) hi
    obtain ⟨hct, hcN⟩ := hd.I₂_le hcI
    have hcR := hRn ⟨d.normalizer_tP_le_normalizer_ZtP hcN, hct⟩
    have hzc : z = c⁻¹ * w * c := by rw [hze, hwe, hc]; group
    have h1 : c * r * c⁻¹ ∈ R := (mem_normalizer_iff.1 hcR r).1 hr
    have h2 := mem_centralizer_iff.1 hwR _ h1
    rw [hzc]
    calc c⁻¹ * w * c * r = c⁻¹ * (w * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * w) * c := by rw [h2]
      _ = r * (c⁻¹ * w * c) := by group
  refine hd.le_B₂_of_normal (fun r hr => ⟨⟨(hR hr).1, hRZ hr⟩, (hR hr).2⟩) (fun k hk => ?_) hR2
  exact hRn ⟨hk.1.1, hk.2⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
