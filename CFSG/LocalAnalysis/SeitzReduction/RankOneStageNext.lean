module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageNextBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageNextQuot

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
open CFSG.ABGLocalTools

variable {D : Type} [Group D] [Finite D] {R X U P Up : Subgroup D} {n : ℕ}

namespace SmallRootNextData

variable (hN : SmallRootNextData R X U P Up n)
include hN

omit [Finite D] in
theorem R_le_normalizer_U : R ≤ normalizer (U : Set D) :=
  (gms_R_le_centralizer_U hN.stage.1).trans (centralizer_le_normalizer _)

omit [Finite D] in
theorem V_le_normalizer_U : U ⊔ R ≤ normalizer (U : Set D) :=
  sup_le le_normalizer hN.R_le_normalizer_U

omit [Finite D] in
theorem Xp_le_normalizer_U :
    Up ⊔ (X ⊓ normalizer (U : Set D)) ≤ normalizer (U : Set D) :=
  sup_le hN.Up_le_normalizer_U inf_le_right

theorem Y_le_normalizer_U :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D) ≤
      normalizer (U : Set D) :=
  inf_le_left.trans hN.normalizer_V_le

theorem trP_le_normalizer_V :
    (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔ P ≤
      normalizer ((U ⊔ R : Subgroup D) : Set D) :=
  sup_le inf_le_left (hN.P_le_Y.trans inf_le_left)

omit [Finite D] in
theorem stageImg_R_eq : stageImg U R = stageImg U (U ⊔ R) :=
  (stageImg_sup_left hN.R_le_normalizer_U).symm

omit [Finite D] in
theorem stageImg_tr_eq :
    stageImg U (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) =
      stageImg U Up ⊔ stageImg U R := by
  rw [← hN.sup_eq, stageImg_sup hN.Up_le_normalizer_U hN.R_le_normalizer_U]

omit [Finite D] in
theorem normalizer_R' :
    normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)) =
      stageImg U (normalizer ((U ⊔ R : Subgroup D) : Set D)) := by
  rw [hN.stageImg_R_eq, normalizer_stageImg le_sup_left hN.V_le_normalizer_U]

theorem normalizer_R'_eq :
    normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)) =
      stageImg U (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔
        stageImg U (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D)) := by
  rw [hN.normalizer_R', ← stageImg_sup tr_le_normalizer_U hN.Y_le_normalizer_U,
    ← hN.normalizer_V_eq]

theorem card_R' : Nat.card (stageImg U R) = 2 := by
  obtain ⟨t, -, -, hS⟩ := hN.exists_setup
  obtain ⟨-, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := hN.stage.1
  have h1 := card_stageImg_mul (le_sup_left : U ≤ U ⊔ R) hN.V_le_normalizer_U
  rw [SteinbergBT.card_sup_of_centralizes (gms_R_le_centralizer_U hN.stage.1) hS.inf_eq_bot,
    hUcard, hN.stage.card_eq_two, ← hN.stageImg_R_eq] at h1
  have hpos : 0 < 2 ^ n := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm])

theorem card_U' : Nat.card (stageImg U Up) = 2 ^ n := by
  obtain ⟨-, -, -, -, ⟨-, -, -, hUcard⟩, -⟩ := hN.stage.1
  have h1 := card_stageImg_mul hN.le hN.Up_le_normalizer_U
  rw [hN.stage.card_of_layer hN.three_le hN.le hN.le_tr hN.inf_eq hN.onto, hUcard] at h1
  have hpos : 0 < 2 ^ n := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem isElementaryAbelian_U' : IsElementaryAbelian 2 (stageImg U Up) :=
  isElementaryAbelian_stageImg hN.Up_le_normalizer_U (fun x hx => hN.sq_comm_mem.1 x (hN.le_tr hx))
    fun x hx y hy => hN.sq_comm_mem.2 x (hN.le_tr hx) y (hN.le_tr hy)

omit [Finite D] in
theorem isElementaryAbelian_R' : IsElementaryAbelian 2 (stageImg U R) := by
  refine isElementaryAbelian_stageImg hN.R_le_normalizer_U (fun x hx => ?_) fun x hx y hy => ?_
  · rw [← sq, gms_sq_V hN.stage.1 x (mem_sup_right hx)]
    exact one_mem U
  · rw [gms_comm_V hN.stage.1 x (mem_sup_right hx) y (mem_sup_right hy), mul_inv_cancel_right,
      mul_inv_cancel]
    exact one_mem U

theorem normalizer_V_le_normalizer_tr :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ≤
      normalizer (((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) :
        Subgroup D)) : Set D) := by
  obtain ⟨t, -, -, hS⟩ := hN.exists_setup
  exact hS.normalizer_V_le_normalizer_tr

theorem tr'_le_centralizer :
    stageImg U (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ≤
      centralizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U)) := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := exists_of_mem_stageImg hy
  exact (stageMk_mem_centralizer_iff hN.Up_le_normalizer_U w).mpr fun x hx =>
    hN.sq_comm_mem.2 w hw x (hN.le_tr hx)

theorem mem_tr_of_stageMk_mem_centralizer {K : Subgroup D} (hKR : K ≤ normalizer (R : Set D))
    (hKW : K ≤ normalizer (((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓
      centralizer (U : Set D) : Subgroup D)) : Set D))
    (hKN : K ≤ normalizer (U : Set D)) (g : normalizer (U : Set D))
    (hg : (g : D) ∈ (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔ K)
    (hC : stageMk U g ∈
      centralizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U))) :
    (g : D) ∈ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D) := by
  have hg' : (g : D) ∈ (((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓
      centralizer (U : Set D)) ⊔ K : Subgroup D) : Set D) := hg
  rw [coe_mul_of_right_le_normalizer_left _ K hKW] at hg'
  obtain ⟨w, hw, k, hk, hwk⟩ := hg'
  have hwC : stageMk U ⟨w, tr_le_normalizer_U hw⟩ ∈
      centralizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U)) :=
    hN.tr'_le_centralizer (stageMk_mem_stageImg _ hw)
  have hkeq : (⟨k, hKN hk⟩ : normalizer (U : Set D)) = ⟨w, tr_le_normalizer_U hw⟩⁻¹ * g :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hwk]
      group)
  have hkC : stageMk U ⟨k, hKN hk⟩ ∈
      centralizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U)) := by
    rw [hkeq, map_mul, map_inv]
    exact mul_mem (inv_mem hwC) hC
  have hkV := hN.mem_V_of_comm_mem (hKR hk)
    ((stageMk_mem_centralizer_iff hN.Up_le_normalizer_U _).mp hkC)
  rw [← hwk]
  exact mul_mem hw (hN.V_le_tr hkV)

theorem normalizer_R'_inf_centralizer :
    normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)) ⊓
        centralizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U)) =
      stageImg U Up ⊔ stageImg U R := by
  rw [← hN.stageImg_tr_eq]
  refine le_antisymm (fun y hy => ?_) (le_inf ?_ hN.tr'_le_centralizer)
  · obtain ⟨hyN, hyC⟩ := mem_inf.mp hy
    rw [hN.normalizer_R'] at hyN
    obtain ⟨g, hg, rfl⟩ := exists_of_mem_stageImg hyN
    rw [hN.normalizer_V_eq] at hg
    exact stageMk_mem_stageImg g (hN.mem_tr_of_stageMk_mem_centralizer inf_le_right
      (inf_le_left.trans hN.normalizer_V_le_normalizer_tr) hN.Y_le_normalizer_U g hg hyC)
  · rw [hN.normalizer_R']
    exact stageImg_mono inf_le_left

theorem P'_inf_centralizer :
    stageImg U ((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔ P) ⊓
        centralizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U)) =
      stageImg U Up ⊔ stageImg U R := by
  rw [← hN.stageImg_tr_eq]
  refine le_antisymm (fun y hy => ?_) (le_inf (stageImg_mono le_sup_left) hN.tr'_le_centralizer)
  obtain ⟨hyP, hyC⟩ := mem_inf.mp hy
  obtain ⟨g, hg, rfl⟩ := exists_of_mem_stageImg hyP
  exact stageMk_mem_stageImg g (hN.mem_tr_of_stageMk_mem_centralizer
    (hN.P_le_Y.trans inf_le_right)
    ((hN.P_le_Y.trans inf_le_left).trans hN.normalizer_V_le_normalizer_tr)
    (hN.P_le_Y.trans hN.Y_le_normalizer_U) g hg hyC)

theorem singer' :
    IsCyclic (GMSNormalizerQuotient (stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))))
      (stageImg U Up)) ∧
    Nat.card (GMSNormalizerQuotient (stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))))
      (stageImg U Up)) = 2 ^ n - 1 ∧
    ∀ u v : stageImg U Up, u ≠ 1 → v ≠ 1 →
      ∃! c : GMSNormalizerQuotient (stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))))
        (stageImg U Up),
        gmsQuotConjAct (stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D)))) (stageImg U Up) c u =
          v := by
  obtain ⟨d, hdNX, hdord, hNXeq, hdU, hdtr, hdfix⟩ := hN.exists_singer_layer
  have hdN : d ∈ normalizer (U : Set D) := (mem_inf.mp hdNX).2
  obtain ⟨d', hd'⟩ : ∃ d' : StageQuot U, d' = stageMk U ⟨d, hdN⟩ := ⟨_, rfl⟩
  have hd'pow : ∀ k : ℕ, d' ^ k = stageMk U ⟨d ^ k, pow_mem hdN k⟩ := fun k => by
    rw [hd', ← map_pow]
    rfl
  have hd'ord : orderOf d' = 2 ^ n - 1 := by
    rw [← hdord]
    refine orderOf_eq_orderOf_iff.mpr fun k => ?_
    rw [hd'pow, stageMk_eq_one_iff]
    exact ⟨hdU k, fun h1 => by show d ^ k ∈ U; rw [h1]; exact one_mem U⟩
  have hzp : stageImg U (zpowers d) = zpowers d' := by
    refine le_antisymm (fun y hy => ?_) (zpowers_le.mpr ?_)
    · obtain ⟨x, hx, rfl⟩ := exists_of_mem_stageImg hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
      have hxk : x = ⟨d, hdN⟩ ^ k := Subtype.ext (by rw [coe_zpow]; exact hk.symm)
      rw [hxk, map_zpow, ← hd']
      exact zpow_mem (mem_zpowers _) k
    · rw [hd']
      exact stageMk_mem_stageImg _ (mem_zpowers d)
  have hX'eq : stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))) = stageImg U Up ⊔ zpowers d' := by
    rw [stageImg_sup hN.Up_le_normalizer_U inf_le_right, hNXeq,
      stageImg_sup_left (zpowers_le.mpr hdN), hzp]
  have hU'comm : ∀ x ∈ stageImg U Up, ∀ y ∈ stageImg U Up, x * y = y * x := by
    have := hN.isElementaryAbelian_U'
    intro x hx y hy
    exact congrArg Subtype.val (this.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hd'X : d' ∈ stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))) := by
    rw [hd']
    exact stageMk_mem_stageImg _ (mem_sup_right hdNX)
  have hd'NU : d' ∈ normalizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U)) := by
    rw [hd', stageMk_mem_normalizer_iff hN.le hN.Up_le_normalizer_U]
    exact hN.le_normalizer_NX hdNX
  have hconj : ∀ (k : ℕ) (a : normalizer (U : Set D)), d' ^ k * stageMk U a * (d' ^ k)⁻¹ =
      stageMk U ⟨d ^ k * a * (d ^ k)⁻¹,
        mul_mem (mul_mem (pow_mem hdN k) a.2) (inv_mem (pow_mem hdN k))⟩ := by
    intro k a
    rw [hd'pow, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hreg : ∀ x ∈ stageImg U Up, x ≠ 1 → ∀ y ∈ stageImg U Up, y ≠ 1 →
      ∃! c : zpowers d', (c : StageQuot U) * x * (c : StageQuot U)⁻¹ = y := by
    intro x hx hx1 y hy hy1
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_stageImg hx
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_stageImg hy
    have haU : (a : D) ∉ U := fun h' => hx1 ((stageMk_eq_one_iff a).mpr h')
    have hbU : (b : D) ∉ U := fun h' => hy1 ((stageMk_eq_one_iff b).mpr h')
    obtain ⟨k, hk⟩ := hdtr a ha haU b hb hbU
    have h0 : d' ^ k * stageMk U a * (d' ^ k)⁻¹ = stageMk U b := by
      rw [hconj, stageMk_eq_iff]
      exact hk
    refine ⟨⟨d' ^ k, pow_mem (mem_zpowers d') k⟩, h0, ?_⟩
    rintro ⟨c, hc⟩ hc'
    have hc'' : c * stageMk U a * c⁻¹ = stageMk U b := hc'
    obtain ⟨m, hm⟩ : ∃ m : ℕ, d' ^ m = (d' ^ k)⁻¹ * c :=
      (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2
        (mul_mem (inv_mem (pow_mem (mem_zpowers d') k)) hc))
    have hfix : d' ^ m * stageMk U a * (d' ^ m)⁻¹ = stageMk U a := by
      rw [hm]
      calc (d' ^ k)⁻¹ * c * stageMk U a * ((d' ^ k)⁻¹ * c)⁻¹ =
          (d' ^ k)⁻¹ * (c * stageMk U a * c⁻¹) * d' ^ k := by group
        _ = (d' ^ k)⁻¹ * (d' ^ k * stageMk U a * (d' ^ k)⁻¹) * d' ^ k := by rw [hc'', h0]
        _ = stageMk U a := by group
    rw [hconj, stageMk_eq_iff] at hfix
    have hm1 : d ^ m = 1 := hdfix m a ha haU hfix
    have hd'm : d' ^ m = 1 := by
      rw [hd'pow]
      exact (stageMk_eq_one_iff _).mpr (by show d ^ m ∈ U; rw [hm1]; exact one_mem U)
    apply Subtype.ext
    show c = d' ^ k
    rw [hd'm] at hm
    calc c = d' ^ k * ((d' ^ k)⁻¹ * c) := by group
      _ = d' ^ k := by rw [← hm, mul_one]
  have hU'1 : ∃ x ∈ stageImg U Up, x ≠ 1 := by
    have h8 : 1 < Nat.card (stageImg U Up) := by
      rw [hN.card_U']
      exact Nat.one_lt_two_pow (by have := hN.stage.three_le; omega)
    have : Nontrivial (stageImg U Up) := Finite.one_lt_card_iff_nontrivial.mp h8
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : stageImg U Up)
    exact ⟨x, hx, fun h1 => hx1 (Subtype.ext h1)⟩
  obtain ⟨hcyc, hcard, hreg'⟩ := gmsNormalizerQuotient_of_regular_complement
    (stageImg_mono le_sup_left) hU'comm (zpowers_le.mpr hd'X) (zpowers_le.mpr hd'NU)
    (by rw [hX'eq]; exact inf_le_left) inferInstance hreg hU'1
  refine ⟨hcyc, ?_, hreg'⟩
  rw [hcard, Nat.card_zpowers, hd'ord]

end SmallRootNextData

theorem smallRoot_next (h : SmallRootStage R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (hE : GMSHasRegularNormal U R)
    {Up : Subgroup D} (h1 : U ≤ Up)
    (h2 : Up ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D))
    (h3' : Up ⊓ (U ⊔ R) = U)
    (h4 : Up ⊔ R = normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D))
    (h5 : normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D) ≤
      normalizer (Up : Set D))
    (h6 : X ⊓ normalizer (U : Set D) ≤ normalizer (Up : Set D))
    (h7 : ∀ r ∈ R, r ≠ 1 → ∀ x ∈ Up, x * r * x⁻¹ * r⁻¹ = 1 → x ∈ U)
    (h8 : ∀ r ∈ R, r ≠ 1 → ∀ u ∈ U, ∃ x ∈ Up, x * r * x⁻¹ * r⁻¹ = u) :
    SmallRootStage (stageImg U R) (stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))))
        (stageImg U Up)
        (stageImg U ((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔ P))
        n ∧
      stageImg U (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ normalizer (R : Set D)) ⊔
          stageImg U (normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) =
        normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set _) := by
  have hN : SmallRootNextData R X U P Up n := ⟨h, h3, hE, h1, h2, h3', h4, h5, h6, h7, h8⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, -, -, hS⟩ := hN.exists_setup
  have hR'card := hN.card_R'
  have hJ : Even (Nat.card (stageImg U R)) ∧ ∀ g : StageQuot U,
      g ∉ normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)) →
        Odd (Nat.card (stageImg U R ⊓ (stageImg U R).map (MulAut.conj g⁻¹).toMonoidHom :
          Subgroup (StageQuot U))) :=
    ⟨by rw [hR'card]; exact even_two, fun g hg => by
      rw [card_inf_conj_eq_one_of_card_eq_two hR'card hg]; exact odd_one⟩
  have hRsyl : ∃ T : Sylow 2 (stageImg U R),
      (T : Subgroup (stageImg U R)) = (stageImg U R).subgroupOf (stageImg U R) := by
    have hp : IsPGroup 2 (⊤ : Subgroup (stageImg U R)) :=
      IsPGroup.of_card (n := 1) (by rw [Subgroup.card_top, hR'card, pow_one])
    exact ⟨hp.toSylow (by simp), by rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_self]⟩
  have hX'R : stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))) ≤
      normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)) := by
    rw [hN.normalizer_R']
    exact stageImg_mono (sup_le (hN.le_tr.trans inf_le_left) hN.NX_le_normalizer_V)
  have hX'n : ((stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D)))).subgroupOf
      (normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)))).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hX'R, hN.normalizer_R',
      normalizer_stageImg (hN.le.trans le_sup_left) hN.Xp_le_normalizer_U]
    exact stageImg_mono hN.normalizer_V_le_normalizer_sup
  have hX'C : stageImg U (Up ⊔ (X ⊓ normalizer (U : Set D))) ≤
      centralizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)) :=
    hX'R.trans (normalizer_le_centralizer_of_card_eq_two hR'card)
  have hU'syl := (isSylowOf_stageImg hN.le hN.Xp_le_normalizer_U
    hN.isSylowOf_sup_NX).exists_sylow_eq_subgroupOf
  have hRP : R ≤ P := le_sup_right.trans hS.V_le_P
  have hPW : P ≤ normalizer (((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓
      centralizer (U : Set D) : Subgroup D)) : Set D) :=
    (hN.P_le_Y.trans inf_le_left).trans hN.normalizer_V_le_normalizer_tr
  have hP'R : stageImg U ((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔
      P) ≤ normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U)) := by
    rw [hN.normalizer_R']
    exact stageImg_mono hN.trP_le_normalizer_V
  have hP'syl : ∃ T : Sylow 2 (normalizer ((stageImg U R : Subgroup (StageQuot U)) :
      Set (StageQuot U))), (T : Subgroup _) = (stageImg U ((normalizer ((U ⊔ R : Subgroup D) :
        Set D) ⊓ centralizer (U : Set D)) ⊔ P)).subgroupOf
          (normalizer ((stageImg U R : Subgroup (StageQuot U)) : Set (StageQuot U))) := by
    rw [hN.normalizer_R']
    exact (isSylowOf_stageImg (le_sup_left.trans (hN.V_le_tr.trans le_sup_left))
      hN.normalizer_V_le hN.isSylowOf_tr_sup_P).exists_sylow_eq_subgroupOf
  have hP'U : stageImg U ((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔
      P) ≤ normalizer ((stageImg U Up : Subgroup (StageQuot U)) : Set (StageQuot U)) := by
    rw [normalizer_stageImg hN.le hN.Up_le_normalizer_U]
    exact stageImg_mono (sup_le hN.tr_le_normalizer_Up (hN.P_le_Y.trans h5))
  have hUR' : stageImg U Up ⊓ stageImg U R = ⊥ := by
    rw [hN.stageImg_R_eq, ← stageImg_inf hN.le le_sup_left, h3', stageImg_self]
  have hV'n : ((stageImg U Up ⊔ stageImg U R).subgroupOf (stageImg U
      ((normalizer ((U ⊔ R : Subgroup D) : Set D) ⊓ centralizer (U : Set D)) ⊔ P))).Normal := by
    rw [← hN.stageImg_tr_eq, normal_subgroupOf_iff_le_normalizer (stageImg_mono le_sup_left),
      normalizer_stageImg (le_sup_left.trans hN.V_le_tr) SmallRootNextData.tr_le_normalizer_U]
    exact stageImg_mono (sup_le le_normalizer hPW)
  refine ⟨⟨⟨h.three_le, hJ, ⟨hN.isElementaryAbelian_R', le_rfl, hRsyl⟩, ⟨hX'R, hX'n, hX'C⟩,
    ⟨hN.isElementaryAbelian_U', stageImg_mono le_sup_left, hU'syl, hN.card_U'⟩, hN.singer',
    ⟨hP'R, hP'syl, stageImg_mono (hN.le_tr.trans le_sup_left),
      stageImg_mono (hRP.trans le_sup_right), hP'U, hUR', hN.P'_inf_centralizer, hV'n⟩⟩,
    hR'card, hN.normalizer_R'_inf_centralizer⟩, ?_⟩
  rw [hN.normalizer_R'_eq, sup_comm]

end CFSG.SeitzReduction.RankOne
