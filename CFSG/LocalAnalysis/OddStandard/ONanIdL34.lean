module

public import CFSG.LocalAnalysis.OddStandard.ONanIdOne
public import CFSG.LocalAnalysis.OddStandard.ThmCConcl
public import CFSG.LocalAnalysis.OddStandard.ONanEndPGLCert
public import CFSG.LocalAnalysis.OddStandard.ONanSylowCert
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.OddStandard.ThmCTSub
public import CFSG.LocalAnalysis.OddStandard.ThmCTWr
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open scoped commutatorElement

theorem lieModel_PSL_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSL n p f) : CFSG.Blueprint.LieModel Y .PSL n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem isSimpleGroup_of_lieModel_PSL {X : Type} [Group X] {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSL n p f) : IsSimpleGroup X :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ _ _ _ (h.statedClassicalModel (by decide))).2

theorem v1sqE_notMem : gen 0 ^ 2 ≠ 1 ∧ gen 0 ^ 2 ≠ xE ∧ gen 0 ^ 2 ≠ zc ∧ gen 0 ^ 2 ≠ xE⁻¹ := by
  decide

theorem y0E_notMem : y0E ≠ 1 ∧ y0E ≠ xE ∧ y0E ≠ zc ∧ y0E ≠ xE⁻¹ := by decide

theorem tv1E_notMem : (gen 4 * gen 0)⁻¹ * (gen 0 * gen 4) ≠ 1 ∧
    (gen 4 * gen 0)⁻¹ * (gen 0 * gen 4) ≠ xE ∧ (gen 4 * gen 0)⁻¹ * (gen 0 * gen 4) ≠ zc ∧
    (gen 4 * gen 0)⁻¹ * (gen 0 * gen 4) ≠ xE⁻¹ := by decide

theorem xE_eq_comm : xE = (gen 0 * gen 2 ^ 2)⁻¹ * s2E⁻¹ * (gen 0 * gen 2 ^ 2) * s2E *
    ((gen 1)⁻¹ * tE⁻¹ * gen 1 * tE) := by decide

theorem comm_xE_gens : (gen 0 * gen 2 ^ 2) * xE = xE * (gen 0 * gen 2 ^ 2) ∧
    s2E * xE = xE * s2E ∧ gen 1 * xE = xE * gen 1 ∧ tE * xE = xE * tE := by decide

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0

theorem Cx_le_Cz : centralizer ({𝔵} : Set G) ≤ centralizer ({𝔷} : Set G) := by
  intro y hy
  have h := mem_centralizer_singleton_iff.1 hy
  rw [mem_centralizer_singleton_iff, ← D.xel_sq]
  calc y * (𝔵 * 𝔵) = y * 𝔵 * 𝔵 := by group
    _ = 𝔵 * 𝔵 * y := by rw [h, mul_assoc, h, ← mul_assoc]

theorem conj_mem_Cx (hone : OneClass G) (hbal : Balanced G) {c y : G}
    (hc : c ∈ centralizer ({𝔷} : Set G)) (hy : y ∈ centralizer ({𝔵} : Set G)) :
    c * y * c⁻¹ ∈ centralizer ({𝔵} : Set G) := by
  rw [mem_centralizer_x_iff]
  have hy' := mem_centralizer_x_iff.1 hy
  have hyinv : y * 𝔵⁻¹ * y⁻¹ = 𝔵⁻¹ := by
    rw [show y * 𝔵⁻¹ * y⁻¹ = (y * 𝔵 * y⁻¹)⁻¹ by group, hy']
  rcases D.conj_x_of_mem_centralizer_z hone hbal (inv_mem hc) with h | h
  · rw [inv_inv] at h
    calc c * y * c⁻¹ * 𝔵 * (c * y * c⁻¹)⁻¹ = c * (y * (c⁻¹ * 𝔵 * c) * y⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * 𝔵 * c) * c⁻¹ := by rw [h, hy']
      _ = 𝔵 := by group
  · rw [inv_inv] at h
    calc c * y * c⁻¹ * 𝔵 * (c * y * c⁻¹)⁻¹ = c * (y * (c⁻¹ * 𝔵 * c) * y⁻¹) * c⁻¹ := by group
      _ = c * 𝔵⁻¹ * c⁻¹ := by rw [h, hyinv]
      _ = c * (c⁻¹ * 𝔵 * c) * c⁻¹ := by rw [h]
      _ = 𝔵 := by group

theorem pPrimeCore_Cx_eq_bot (hone : OneClass G) (hbal : Balanced G) :
    pPrimeCore 2 (centralizer ({𝔵} : Set G)) = ⊥ := by
  have hle : (pPrimeCore 2 (centralizer ({𝔵} : Set G))).map
      (centralizer ({𝔵} : Set G)).subtype ≤ centralizer ({𝔷} : Set G) :=
    (map_subtype_le _).trans D.Cx_le_Cz
  have hn : ((pPrimeCore 2 (centralizer ({𝔵} : Set G))).map
      (centralizer ({𝔵} : Set G)).subtype).subgroupOf (centralizer ({𝔷} : Set G)) |>.Normal := by
    refine ⟨fun o ho g => ?_⟩
    rw [mem_subgroupOf] at ho ⊢
    obtain ⟨o₀, ho₀, hoo⟩ := ho
    let α : centralizer ({𝔵} : Set G) ≃* centralizer ({𝔵} : Set G) :=
      { toFun := fun y => ⟨(g : G) * y * (g : G)⁻¹, D.conj_mem_Cx hone hbal g.2 y.2⟩
        invFun := fun y => ⟨(g : G)⁻¹ * y * g, by
          simpa using D.conj_mem_Cx hone hbal (inv_mem g.2) y.2⟩
        left_inv := by intro y; ext; simp [mul_assoc]
        right_inv := by intro y; ext; simp [mul_assoc]
        map_mul' := by
          intro a b
          ext
          change (g : G) * ↑(a * b) * (g : G)⁻¹ =
            (g : G) * a * (g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹)
          rw [Subgroup.coe_mul]
          group }
    have hmap : (pPrimeCore 2 (centralizer ({𝔵} : Set G))).map α.toMonoidHom =
        pPrimeCore 2 (centralizer ({𝔵} : Set G)) :=
      (Subgroup.characteristic_iff_map_eq.mp inferInstance) α
    have hαo : α o₀ ∈ pPrimeCore 2 (centralizer ({𝔵} : Set G)) := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ ho₀
    refine ⟨α o₀, hαo, ?_⟩
    show (g : G) * o₀ * (g : G)⁻¹ = ((g * o * g⁻¹ : centralizer ({𝔷} : Set G)) : G)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    simp only [Subgroup.coe_subtype] at hoo
    rw [hoo]
  have hcop : Nat.Coprime 2 (Nat.card (((pPrimeCore 2 (centralizer ({𝔵} : Set G))).map
      (centralizer ({𝔵} : Set G)).subtype).subgroupOf (centralizer ({𝔷} : Set G)))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective (centralizer ({𝔵} : Set G)).subtype_injective]
    exact pPrimeCore_coprime_card
  have hbot := le_sSup (s := {K : Subgroup (centralizer ({𝔷} : Set G)) |
    K.Normal ∧ Nat.Coprime 2 (Nat.card K)}) ⟨hn, hcop⟩
  have hO : pPrimeCore 2 (centralizer ({𝔷} : Set G)) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two']
    exact hbal _ (D.orderOf_rep 0)
  change _ ≤ pPrimeCore 2 (centralizer ({𝔷} : Set G)) at hbot
  rw [hO] at hbot
  rw [eq_bot_iff]
  intro o ho
  have h1 : (⟨(o : G), hle ⟨o, ho, rfl⟩⟩ : centralizer ({𝔷} : Set G)) ∈
      ((pPrimeCore 2 (centralizer ({𝔵} : Set G))).map
        (centralizer ({𝔵} : Set G)).subtype).subgroupOf (centralizer ({𝔷} : Set G)) :=
    mem_subgroupOf.2 ⟨o, ho, rfl⟩
  have h2 := hbot h1
  rw [mem_bot] at h2
  have h3 : (o : G) = 1 := by
    have := congrArg (fun y : centralizer ({𝔷} : Set G) => (y : G)) h2
    simpa using this
  exact mem_bot.2 (Subtype.ext h3)

theorem isPGroup_zpowers_zIn_x : IsPGroup 2 (zpowers (zIn 𝔵)) := by
  refine IsPGroup.of_card (n := 2) ?_
  rw [Nat.card_zpowers, ← Subgroup.orderOf_coe]
  show orderOf 𝔵 = 2 ^ 2
  rw [D.x_eq, orderOf_injective D.E.φ D.E.inj, xE_orderOf]
  rfl

theorem pPrimeCore_quot_eq_bot (hone : OneClass G) (hbal : Balanced G) :
    pPrimeCore 2 (KQ 𝔵) = ⊥ := by
  have hcen : zpowers (zIn 𝔵) ≤ center (centralizer ({𝔵} : Set G)) :=
    zpowers_le.2 (Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (mem_centralizer_singleton_iff.1 y.2))
  rw [CFSG.central_p_subgroup_prime_core_quotient _ hcen D.isPGroup_zpowers_zIn_x,
    D.pPrimeCore_Cx_eq_bot hone hbal, Subgroup.map_bot]

theorem v1_mem_Cx : v1 ∈ centralizer ({𝔵} : Set G) :=
  mem_centralizer_singleton_iff.2 (D.comm_V (D.mem_V_phi (gen 0) |>.2 rfl |> fun h => by
    rwa [AlpEmb.φ_v1 D.E] at h) D.x_mem_V)

theorem s2_mem_Cx : s ^ 2 ∈ centralizer ({𝔵} : Set G) :=
  mem_centralizer_x_iff.2 D.s2_fix_x

theorem t_mem_Cx : t ∈ centralizer ({𝔵} : Set G) :=
  mem_centralizer_x_iff.2 D.t_fix_x

theorem notMem_zpowers_x_of_phi {e : AlpE} (h : e ≠ 1 ∧ e ≠ xE ∧ e ≠ zc ∧ e ≠ xE⁻¹) :
    D.E.φ e ∉ zpowers 𝔵 := by
  rw [D.mem_zpowers_x, D.x_eq, D.z_eq, ← map_inv]
  rintro (h1 | h1 | h1 | h1)
  · exact h.1 (D.E.inj (by rw [h1, map_one]))
  · exact h.2.1 (D.E.inj h1)
  · exact h.2.2.1 (D.E.inj h1)
  · exact h.2.2.2 (D.E.inj h1)

theorem orderOf_v1_quot : orderOf (πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, ← map_pow, πQ_eq_one_iff]
    show v1 ^ 2 ∈ zpowers 𝔵 → False
    have hv : v1 ^ 2 = D.E.φ (gen 0 ^ 2) := by rw [map_pow, AlpEmb.φ_v1]
    rw [hv]
    exact D.notMem_zpowers_x_of_phi v1sqE_notMem
  · rw [← map_pow, πQ_eq_one_iff]
    show v1 ^ 2 ^ (1 + 1) ∈ zpowers 𝔵
    rw [show 2 ^ (1 + 1) = 4 by norm_num, D.fr.v1_four]
    exact one_mem _

theorem s_pow_eight_z : s ^ 8 = 𝔷 := by
  rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, D.fr.s_four, pow_two, D.y0_sq]

theorem orderOf_s2_quot : orderOf (πQ 𝔵 ⟨s ^ 2, D.s2_mem_Cx⟩) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, ← map_pow, πQ_eq_one_iff]
    show (s ^ 2) ^ 2 ∈ zpowers 𝔵 → False
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, D.fr.s_four, D.y0_eq]
    exact D.notMem_zpowers_x_of_phi y0E_notMem
  · rw [← map_pow, πQ_eq_one_iff]
    show (s ^ 2) ^ 2 ^ (1 + 1) ∈ zpowers 𝔵
    rw [← pow_mul, show 2 * 2 ^ (1 + 1) = 8 by norm_num, D.s_pow_eight_z, ← D.xel_sq]
    exact mul_mem (mem_zpowers _) (mem_zpowers _)

theorem not_isConj_v1_s2 :
    ¬ IsConj (πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩) (πQ 𝔵 ⟨s ^ 2, D.s2_mem_Cx⟩) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨k, rfl⟩ := πQ_surjective 𝔵 c
  rw [← map_inv, ← map_mul, ← map_mul, πQ_eq_iff] at hc
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hc
  have hkv : (k : G) * v1 * (k : G)⁻¹ ∈ centralizer ({𝔵} : Set G) :=
    mul_mem (mul_mem k.2 D.v1_mem_Cx) (inv_mem k.2)
  have hs2 : s ^ 2 = (k : G) * v1 * (k : G)⁻¹ * 𝔵 ^ m := by
    have e : ((k * ⟨v1, D.v1_mem_Cx⟩ * k⁻¹ : centralizer ({𝔵} : Set G)) : G) =
        (k : G) * v1 * (k : G)⁻¹ := rfl
    rw [e] at hm
    rw [hm]
    group
  have hcomm : Commute ((k : G) * v1 * (k : G)⁻¹) (𝔵 ^ m) := by
    refine Commute.zpow_right ?_ m
    exact mem_centralizer_singleton_iff.1 hkv
  have h4 : (s ^ 2) ^ 4 = 1 := by
    rw [hs2, hcomm.mul_pow, conj_pow, D.fr.v1_four, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, D.x_pow_four, one_zpow]
    group
  apply D.rep_ne_one 0
  rw [← D.s_pow_eight_z, show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, h4]

theorem lieModel_quot
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    CFSG.Blueprint.LieModel (KQ 𝔵) .PSL 3 2 2 := by
  have hO := D.pPrimeCore_quot_eq_bot hone hbal
  obtain ⟨T, hT⟩ := D.exists_sylow_quot f2QuotCheck_cert
  obtain ⟨K, hKn, hKL, -, hidx⟩ :=
    ThmC.onan_use_of_full hF ThmC.conclTwoClasses hO T hT (D.oneClass_quot hone)
  have hK := eq_top_of_not_isConj_order_four_cert hO hKn hKL hidx D.orderOf_v1_quot
    D.orderOf_s2_quot D.not_isConj_v1_s2
  subst hK
  exact lieModel_PSL_of_mulEquiv Subgroup.topEquiv hKL

theorem x_eq_comm : 𝔵 = (v1 * v3 ^ 2)⁻¹ * (s ^ 2)⁻¹ * (v1 * v3 ^ 2) * s ^ 2 *
    (v2⁻¹ * t⁻¹ * v2 * t) := by
  have h := congrArg D.E.φ xE_eq_comm
  simp only [map_mul, map_inv, map_pow, AlpEmb.φ_v1, AlpEmb.φ_v2, AlpEmb.φ_v3] at h
  rw [D.x_eq, h, D.phi_s2, D.phi_t]

theorem v13_mem_Cx : v1 * v3 ^ 2 ∈ centralizer ({𝔵} : Set G) := by
  have h := congrArg D.E.φ comm_xE_gens.1
  simp only [map_mul, map_pow, AlpEmb.φ_v1, AlpEmb.φ_v3] at h
  rw [← D.x_eq] at h
  exact mem_centralizer_singleton_iff.2 h

theorem v2_mem_Cx : v2 ∈ centralizer ({𝔵} : Set G) := by
  have h := congrArg D.E.φ comm_xE_gens.2.2.1
  simp only [map_mul, AlpEmb.φ_v2] at h
  rw [← D.x_eq] at h
  exact mem_centralizer_singleton_iff.2 h

theorem x_mem_commutator :
    (⟨𝔵, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({𝔵} : Set G)) ∈
      commutator (centralizer ({𝔵} : Set G)) := by
  set a : centralizer ({𝔵} : Set G) := ⟨(v1 * v3 ^ 2)⁻¹, inv_mem D.v13_mem_Cx⟩
  set b : centralizer ({𝔵} : Set G) := ⟨(s ^ 2)⁻¹, inv_mem D.s2_mem_Cx⟩
  set c : centralizer ({𝔵} : Set G) := ⟨v2⁻¹, inv_mem D.v2_mem_Cx⟩
  set d : centralizer ({𝔵} : Set G) := ⟨t⁻¹, inv_mem D.t_mem_Cx⟩
  have e : (⟨𝔵, mem_centralizer_singleton_iff.2 rfl⟩ : centralizer ({𝔵} : Set G)) =
      ⁅a, b⁆ * ⁅c, d⁆ := by
    apply Subtype.ext
    show 𝔵 = (v1 * v3 ^ 2)⁻¹ * (s ^ 2)⁻¹ * (v1 * v3 ^ 2)⁻¹⁻¹ * (s ^ 2)⁻¹⁻¹ *
      (v2⁻¹ * t⁻¹ * v2⁻¹⁻¹ * t⁻¹⁻¹)
    rw [inv_inv, inv_inv, inv_inv, inv_inv]
    exact D.x_eq_comm
  rw [e, _root_.commutator_def]
  exact mul_mem (commutator_mem_commutator (mem_top _) (mem_top _))
    (commutator_mem_commutator (mem_top _) (mem_top _))

theorem isPerfect_Cx
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    commutator (centralizer ({𝔵} : Set G)) = ⊤ := by
  have hS := isSimpleGroup_of_lieModel_PSL (D.lieModel_quot hF hone hbal)
  have hnc : πQ 𝔵 ⟨t, D.t_mem_Cx⟩ * πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩ ≠
      πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩ * πQ 𝔵 ⟨t, D.t_mem_Cx⟩ := by
    rw [← map_mul, ← map_mul, Ne, πQ_eq_iff]
    show (t * v1)⁻¹ * (v1 * t) ∈ zpowers 𝔵 → False
    have hv : (t * v1)⁻¹ * (v1 * t) = D.E.φ ((gen 4 * gen 0)⁻¹ * (gen 0 * gen 4)) := by
      simp only [map_mul, map_inv, AlpEmb.φ_t, AlpEmb.φ_v1]
    rw [hv]
    exact D.notMem_zpowers_x_of_phi tv1E_notMem
  have hQ : commutator (KQ 𝔵) = ⊤ := by
    rcases (inferInstance : (commutator (KQ 𝔵)).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      apply hnc
      have hm : ⁅πQ 𝔵 ⟨t, D.t_mem_Cx⟩, πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩⁆ ∈ commutator (KQ 𝔵) := by
        rw [_root_.commutator_def]
        exact commutator_mem_commutator (mem_top _) (mem_top _)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · exact h
  rw [eq_top_iff]
  intro y _
  have hy : πQ 𝔵 y ∈ (commutator (centralizer ({𝔵} : Set G))).map (πQ 𝔵) := by
    rw [_root_.commutator_def, map_commutator, map_top_of_surjective _ (πQ_surjective 𝔵),
      ← _root_.commutator_def,
      hQ]
    exact mem_top _
  obtain ⟨y', hy', hyy⟩ := hy
  have hz : y'⁻¹ * y ∈ commutator (centralizer ({𝔵} : Set G)) := by
    have h1 : y'⁻¹ * y ∈ zpowers (zIn 𝔵) := by
      rw [← QuotientGroup.eq]
      exact hyy
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 h1
    rw [← hm]
    exact zpow_mem D.x_mem_commutator m
  have e : y = y' * (y'⁻¹ * y) := by group
  rw [e]
  exact mul_mem hy' hz

end FusCtx

end CFSG.OddStandard.ONanRec
