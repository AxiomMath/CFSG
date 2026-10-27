module

public import CFSG.LocalAnalysis.EvenBN.Sp4.OneAxisClassSlice
public import CFSG.LocalAnalysis.EvenBN.Sp4.SliceSylowBootstrap
public import CFSG.LocalAnalysis.SteinbergSFOneAxisElementaryOvergroupBase

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore OneAxisRadical OneAxisSecond OneAxisHeisenberg
  OneAxisRadicalStructure OneAxisSecondAxis OneAxisWeakClosure
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open scoped Pointwise

theorem isCyclic_outer_antiSp {K : Type} [Field K] [CharP K 2] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : IsCyclic (Outer (antiSp K)) := by
  obtain ⟨Fr, hFr, hord, hzp⟩ := exists_frobenius_data hn hK
  obtain ⟨-, -, -, -, hcyc, -⟩ := exceptionalAut_structure hn hFr hord hzp
  exact isCyclic_of_surjective (hH := hcyc)
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence (antiProjEquiv K)).symm
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence (antiProjEquiv K)).symm.surjective

theorem exists_sylow_pull {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] (φ : L ≃* antiSp K) :
    ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype = pull φ (antiUnipotent K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hU2, hUodd⟩ := card_and_isSylowTwoOf_antiUnipotent (K := K)
  rw [show ((antiUnipotent K).subgroupOf ⊤).index = (antiUnipotent K).index from
    relIndex_top_right _] at hUodd
  have hP₀2 : IsPGroup 2 ((antiUnipotent K).comap φ.toMonoidHom) :=
    hU2.comap_of_injective _ φ.injective
  have hP₀i : ¬ 2 ∣ ((antiUnipotent K).comap φ.toMonoidHom).index := by
    rwa [index_comap_of_surjective _ φ.surjective]
  exact ⟨hP₀2.toSylow hP₀i, rfl⟩

namespace OneAxisData

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ}
  {φ : L ≃* antiSp K} {TG : Subgroup G} {t : G} {M : Subgroup G}

local notation "𝐏" => pull φ (antiUnipotent K)
local notation "𝐙" => pull φ (antiUnipotentCenter K)
local notation "𝐐" => (pull φ (antiUnipotent K) ⊔ TG : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐃₁" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.one) :
  Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐃₂" => (CFSG.pCore 2 (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G))).map (normalizer ((zpowers t ⊔ pull φ (rootA K Axis.two) :
  Subgroup G) : Set G)).subtype

theorem normalizer_Q_le [Finite G] (h : OneAxisData L K n φ TG t M) :
    normalizer (𝐐 : Set G) ≤ normalizer (h.T₁ : Set G) :=
  le_normalizer_sup le_rfl fun _ hg => le_normalizer_pCore_map (h.heis.normQ hg).2

theorem isPGroup_T₁ [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    IsPGroup 2 h.T₁ :=
  IsPGroup.of_card ((card_S h.heis).trans (by rw [← pow_mul, ← pow_succ']))

theorem exists_mul_inv_mem_centralizer [Finite G] [Finite K]
    (h : OneAxisData L K n φ TG t M) {g : G} (hg : g ∈ normalizer (h.T₁ : Set G)) :
    ∃ v ∈ h.V₁, g * v⁻¹ ∈ 𝐂 := by
  have hmem : g⁻¹ * t * g ∈ {x : G | ∃ g : G, x = g⁻¹ * t * g} ∩ (h.T₁ : Set G) :=
    ⟨⟨g, rfl⟩, (mem_normalizer_iff''.mp hg t).mp h.t_mem_T₁⟩
  rw [h.class_slice] at hmem
  obtain ⟨v, hv, hgv⟩ := hmem
  refine ⟨v, hv, mem_centralizer_singleton_iff.mpr ?_⟩
  calc g * v⁻¹ * t = g * (v⁻¹ * t * v) * v⁻¹ := by group
    _ = g * (g⁻¹ * t * g) * v⁻¹ := by rw [hgv]
    _ = t * (g * v⁻¹) := by group

theorem centralizer_inf_normalizer_le [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    𝐂 ⊓ normalizer (h.T₁ : Set G) ≤ normalizer (𝐐 : Set G) := by
  rintro c ⟨hcC, hcN⟩
  refine mem_normalizer_of_conj_le fun q hq => ?_
  have hcq : c * q * c⁻¹ ∈ h.T₁ := (mem_normalizer_iff.mp hcN q).mp (mem_sup_left hq)
  have hc : Commute c t := mem_centralizer_singleton_iff.mp hcC
  have hq' : Commute q t := mem_centralizer_singleton_iff.mp (h.heis.hyp.setup.Q_le_C hq)
  exact mem_Q_of_comm h.heis hcq ((hc.mul_left hq').mul_left hc.inv_left).eq

theorem sup_zpowers_eq [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    M ⊔ zpowers t = 𝐃₁ ⊓ 𝐃₂ := by
  refine le_antisymm (sup_le (le_inf h.le_D₁ h.le_D₂)
    (zpowers_le.mpr ⟨t_mem_D₁ h.heis, t_mem_D₂ h.heis⟩)) fun x hx => ?_
  obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
  rw [← h.sup_t₁, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
    (zpowers_le.mpr h.t_mem_normalizer_M₁)] at hx₁
  obtain ⟨m, hm, c, hc, rfl⟩ := Set.mem_mul.mp hx₁
  have hcD : c ∈ 𝐃₂ := zpowers_le.mpr (t_mem_D₂ h.heis) hc
  have hmM : m ∈ M := by
    rw [← h.M₁_inf_D₂]
    exact mem_inf.mpr ⟨hm, by simpa using mul_mem hx₂ (inv_mem hcD)⟩
  exact mul_mem (mem_sup_left hmM) (mem_sup_right hc)

theorem inf_zpowers_sup_ZP (h : OneAxisData L K n φ TG t M) : M ⊓ (zpowers t ⊔ 𝐙) = 𝐙 := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.ZP_le le_sup_right)
  obtain ⟨hxM, hxB⟩ := mem_inf.mp hx
  rcases (mem_zpowers_sup_iff h.t_mul_t (TwoCoreSetup.comm_pull φ h.heis.sec.two)).mp hxB with
    hZ | hZ
  · exact hZ
  · exfalso
    apply h.t_not_mem
    have := mul_mem (h.ZP_le hZ) (inv_mem hxM)
    rwa [mul_inv_cancel_right] at this

theorem compHyp [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    OneAxisComplement.CompHyp φ t M :=
  ⟨le_inf h.le_D₁ h.le_D₂, h.torus, h.ZP_le, h.sup_zpowers_eq, h.inf_zpowers_sup_ZP⟩

theorem normalizer_D₁_le [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    normalizer (𝐃₁ : Set G) ≤ normalizer (h.M₁ : Set G) :=
  OneAxisOvergroup.OvHyp.normalizer_D₁_le ⟨h.heis, h.compHyp⟩

theorem centralizer_inf_normalizer_le_V₁ [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M) :
    𝐂 ⊓ normalizer (h.T₁ : Set G) ≤ normalizer (h.V₁ : Set G) :=
  le_normalizer_sup
    (fun _ hc => h.normalizer_D₁_le
      (le_normalizer_pCore_map (h.heis.normQ (h.centralizer_inf_normalizer_le hc)).1))
    fun _ hc => h.normalizer_D₂_le
      (le_normalizer_pCore_map (h.heis.normQ (h.centralizer_inf_normalizer_le hc)).2)

theorem normalizer_T₁_le [Finite G] [Finite K]
    (h : OneAxisData L K n φ TG t M) :
    normalizer (h.T₁ : Set G) ≤ normalizer (h.V₁ : Set G) := by
  intro g hg
  obtain ⟨v, hv, hgv⟩ := h.exists_mul_inv_mem_centralizer hg
  have hc : g * v⁻¹ ∈ 𝐂 ⊓ normalizer (h.T₁ : Set G) :=
    mem_inf.mpr ⟨hgv, mul_mem hg (inv_mem (le_normalizer (h.V₁_le_T₁ hv)))⟩
  have := mul_mem (h.centralizer_inf_normalizer_le_V₁ hc) (le_normalizer hv)
  rwa [inv_mul_cancel_right] at this

theorem mem_Q_of_inner [Finite G] [Finite K] (h : OneAxisData L K n φ TG t M)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hTW : h.T₁ ≤ W) {x : G} (hxW : x ∈ W) (hxC : x ∈ 𝐂)
    (hinn : normAct φ ⟨x, h.heis.hyp.setup.cent_le hxC⟩ ∈ inner (antiSp K)) : x ∈ 𝐐 := by
  have hS := h.heis.hyp.setup
  obtain ⟨a, ha⟩ := hinn
  set l : G := ((φ.symm a : L) : G)
  have hlL : l ∈ L := (φ.symm a).2
  have h0 : l⁻¹ * x ∈ centralizer (L : Set G) :=
    inv_mul_mem_centralizer φ _ (φ.symm a) (by rw [MulEquiv.apply_symm_apply]; exact ha.symm)
  have hc : l⁻¹ * x ∈ TG := hS.mem_T h0 (mul_mem (inv_mem (hS.L_le hlL)) hxC)
  have hcW : l⁻¹ * x ∈ W := hTW (mem_sup_left (mem_sup_right hc))
  have hlW : l ∈ W := by simpa using mul_mem hxW (inv_mem hcW)
  obtain ⟨R, hR⟩ := exists_sylow_pull (G := G) φ
  have hWL : W ⊓ L = 𝐏 := eq_of_le_of_sylow_map ⟨R, hR⟩ hW.to_inf_left
    (le_inf (le_sup_left.trans (le_sup_left.trans hTW)) (pull_le φ _)) inf_le_right
  have hlP : l ∈ 𝐏 := hWL ▸ mem_inf.mpr ⟨hlW, hlL⟩
  simpa using mul_mem (mem_sup_left hlP : l ∈ 𝐐) (mem_sup_right hc)

theorem comm_mem_P [Finite G] [Finite K]
    (h : OneAxisData L K n φ TG t M) {W : Subgroup G} (hW : IsPGroup 2 W) (hTW : h.T₁ ≤ W)
    (hWN : W ≤ normalizer (h.T₁ : Set G)) {x y : G} (hx : x ∈ W ⊓ 𝐂) (hy : y ∈ W ⊓ 𝐂) :
    (x * y)⁻¹ * (y * x) ∈ 𝐏 := by
  have hS := h.heis.hyp.setup
  have hHN : W ⊓ 𝐂 ≤ normalizer (L : Set G) := inf_le_right.trans hS.cent_le
  have hnorm : ((𝐏).subgroupOf (W ⊓ 𝐂)).Normal := by
    refine ⟨fun p hp g => ?_⟩
    rw [mem_subgroupOf] at hp ⊢
    obtain ⟨hgW, hgC⟩ := mem_inf.mp g.2
    have hgV : (g : G) ∈ normalizer (h.V₁ : Set G) := h.normalizer_T₁_le (hWN hgW)
    rw [← h.V₁_inf_centralizer] at hp ⊢
    obtain ⟨hpV, hpC⟩ := mem_inf.mp hp
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hgV _).mp hpV,
      mul_mem (mul_mem hgC hpC) (inv_mem hgC)⟩
  have := isCyclic_outer_antiSp (K := K) (by have := h.heis.sec.two.two_le; omega)
    h.heis.sec.two.card_K
  let ψ : (W ⊓ 𝐂 : Subgroup G) →* Outer (antiSp K) :=
    (QuotientGroup.mk' (inner (antiSp K))).comp (subAct φ hHN)
  have hker : (𝐏).subgroupOf (W ⊓ 𝐂) ≤ ψ.ker := by
    intro p hp
    rw [mem_subgroupOf] at hp
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, subAct_of_eq φ hHN (l := ⟨p, pull_le φ _ hp⟩) rfl]
    exact ⟨_, rfl⟩
  let f := QuotientGroup.lift ((𝐏).subgroupOf (W ⊓ 𝐂)) ψ hker
  have hf : f.ker ≤ center ((W ⊓ 𝐂 : Subgroup G) ⧸ (𝐏).subgroupOf (W ⊓ 𝐂)) := by
    intro q hq
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hq
    obtain ⟨hzW, hzC⟩ := mem_inf.mp z.2
    have hzQ := h.mem_Q_of_inner hW hTW hzW hzC hq
    obtain ⟨p, hp, c, hc, hpc⟩ := hS.mem_Q.mp hzQ
    have hcH : c ∈ W ⊓ 𝐂 := mem_inf.mpr ⟨hTW (mem_sup_left (mem_sup_right hc)), hS.T_le_C hc⟩
    have hzc : (QuotientGroup.mk z : (W ⊓ 𝐂 : Subgroup G) ⧸ (𝐏).subgroupOf (W ⊓ 𝐂)) =
        QuotientGroup.mk ⟨c, hcH⟩ := by
      rw [QuotientGroup.eq, mem_subgroupOf]
      have hpc' : p * c = c * p := hS.comm_L_T (pull_le φ _ hp) hc
      have e : ((z⁻¹ * ⟨c, hcH⟩ : (W ⊓ 𝐂 : Subgroup G)) : G) = p⁻¹ := by
        rw [coe_mul, coe_inv, ← hpc, hpc']
        group
      rw [e]
      exact inv_mem hp
    rw [hzc, mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    rw [h.heis.hyp.T_eq] at hc
    obtain ⟨j, rfl⟩ := hc
    have hg't : Commute (g' : G) t := mem_centralizer_singleton_iff.mp (mem_inf.mp g'.2).2
    exact (hg't.zpow_right j).eq
  have hcomm := f.isMulCommutative_of_isCyclic_of_ker_le_center hf
  have e := hcomm.is_comm.comm (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at e
  simpa using e

theorem isMulCommutative_quot [Finite G] [Finite K]
    (h : OneAxisData L K n φ TG t M) {W : Subgroup G} (hW : IsPGroup 2 W) (hTW : h.T₁ ≤ W)
    (hWN : W ≤ normalizer (h.T₁ : Set G)) :
    ∃ _ : (h.V₁.subgroupOf W).Normal, IsMulCommutative (W ⧸ h.V₁.subgroupOf W) := by
  have hVW : h.V₁ ≤ W := h.V₁_le_T₁.trans hTW
  have hn : (h.V₁.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVW).mpr (hWN.trans h.normalizer_T₁_le)
  refine ⟨hn, ⟨⟨fun a b => ?_⟩⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have key : ∀ z : W, ∃ c ∈ W ⊓ 𝐂, ∃ hc : c ∈ W,
      (QuotientGroup.mk z : W ⧸ h.V₁.subgroupOf W) = QuotientGroup.mk ⟨c, hc⟩ := by
    intro z
    obtain ⟨v, hv, hzv⟩ := h.exists_mul_inv_mem_centralizer (hWN z.2)
    have hc : (z : G) * v⁻¹ ∈ W := mul_mem z.2 (inv_mem (hVW hv))
    refine ⟨_, mem_inf.mpr ⟨hc, hzv⟩, hc, ?_⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa using inv_mem hv
  obtain ⟨c₁, hc₁, hc₁W, e₁⟩ := key x
  obtain ⟨c₂, hc₂, hc₂W, e₂⟩ := key y
  rw [e₁, e₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
  have hP := h.comm_mem_P hW hTW hWN hc₁ hc₂
  exact (le_sup_right.trans h.E_le_V) (by simpa using hP)

end OneAxisData

open OneAxisData

end CFSG.LocalAnalysis.EvenBN.Sp4
