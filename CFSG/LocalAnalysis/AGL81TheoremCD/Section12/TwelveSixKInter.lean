module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKInterSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.GroupTheory.CardMapInfKer
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private noncomputable abbrev kbarMap (M H : Subgroup G) :
    ↥(kSub 3 M H) →* modTwoCore (kSub 3 M H) :=
  QuotientGroup.mk' (pCore 2 ↥(kSub 3 M H))

private theorem le_normalizer_kSub (hKH : ((kSub p M H).subgroupOf H).Normal) :
    H ≤ Subgroup.normalizer (kSub p M H : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le p M H)).mp hKH

private theorem kbarConj_coe_eq_conj (hKH : ((kSub p M H).subgroupOf H).Normal)
    {y : ↥(kSub p M H)} (hyH : (y : G) ∈ H) :
    kbarConj hKH ⟨(y : G), hyH⟩ =
      MulAut.conj (QuotientGroup.mk' (pCore 2 ↥(kSub p M H)) y) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  rw [kbarConj_mk, MulAut.conj_apply]
  show (QuotientGroup.mk (⟨(y:G) * (z:G) * (y:G)⁻¹, _⟩ : ↥(kSub p M H)) :
      modTwoCore (kSub p M H)) =
    (QuotientGroup.mk y : modTwoCore (kSub p M H)) * QuotientGroup.mk z *
      (QuotientGroup.mk y : modTwoCore (kSub p M H))⁻¹
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

private theorem conj_map_mem_of_mem_normalizer
    (hKH : ((kSub p M H).subgroupOf H).Normal) {V : Subgroup G}
    {z : ↥H} {a : modTwoCore (kSub p M H)}
    (ha : MulAut.conj a = kbarConj hKH z)
    (hz : (z : G) ∈ Subgroup.normalizer (V : Set G))
    {v : ↥(kSub p M H)} (hv : (v : G) ∈ V) :
    a * QuotientGroup.mk v * a⁻¹ ∈
      (V.subgroupOf (kSub p M H)).map (QuotientGroup.mk' (pCore 2 ↥(kSub p M H))) := by
  have hmemV : (z : G) * (v : G) * (z : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hz (v : G)).mp hv
  have hmemK : (z : G) * (v : G) * (z : G)⁻¹ ∈ kSub p M H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kSub hKH z.2) (v : G)).mp v.2
  have h1 : a * QuotientGroup.mk v * a⁻¹ = kbarConj hKH z (QuotientGroup.mk v) := by
    rw [← MulAut.conj_apply, ha]
  rw [h1, kbarConj_mk hKH]
  exact Subgroup.mem_map.mpr ⟨⟨_, hmemK⟩, Subgroup.mem_subgroupOf.mpr hmemV, rfl⟩

private theorem mem_normalizer_of_conj_eq
    (hKH : ((kSub p M H).subgroupOf H).Normal) {V : Subgroup G}
    {z : ↥H} {a : modTwoCore (kSub p M H)}
    (ha : MulAut.conj a = kbarConj hKH z)
    (hz : (z : G) ∈ Subgroup.normalizer (V : Set G)) :
    a ∈ Subgroup.normalizer
      (((V.subgroupOf (kSub p M H)).map
        (QuotientGroup.mk' (pCore 2 ↥(kSub p M H)))) : Set (modTwoCore (kSub p M H))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact conj_map_mem_of_mem_normalizer hKH ha hz (Subgroup.mem_subgroupOf.mp hv)
  · intro hw
    obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw
    have hz' : ((z⁻¹ : ↥H) : G) ∈ Subgroup.normalizer (V : Set G) := by
      simpa using Subgroup.inv_mem (Subgroup.normalizer (V : Set G)) hz
    have ha' : MulAut.conj a⁻¹ = kbarConj hKH z⁻¹ := by
      simp only [map_inv, ha]
    have hmem := conj_map_mem_of_mem_normalizer hKH ha' hz'
      (Subgroup.mem_subgroupOf.mp hv)
    have hvw' : (QuotientGroup.mk v : modTwoCore (kSub p M H)) = a * w * a⁻¹ := hvw
    have heq : w = a⁻¹ * (QuotientGroup.mk v) * (a⁻¹)⁻¹ := by
      rw [hvw']
      group
    rw [heq]
    exact hmem

private theorem mem_centralizer_of_conj_eq
    (hKH : ((kSub p M H).subgroupOf H).Normal) {V : Subgroup G}
    {z : ↥H} {a : modTwoCore (kSub p M H)}
    (ha : MulAut.conj a = kbarConj hKH z)
    (hz : (z : G) ∈ Subgroup.centralizer (V : Set G)) :
    a ∈ Subgroup.centralizer
      (((V.subgroupOf (kSub p M H)).map
        (QuotientGroup.mk' (pCore 2 ↥(kSub p M H)))) : Set (modTwoCore (kSub p M H))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
  have hcomm := Subgroup.mem_centralizer_iff.mp hz (v : G) (Subgroup.mem_subgroupOf.mp hv)
  have hmemK : (z : G) * (v : G) * (z : G)⁻¹ ∈ kSub p M H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kSub hKH z.2) (v : G)).mp v.2
  have hzv : (z : G) * (v : G) * (z : G)⁻¹ = (v : G) := by
    rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : kbarConj hKH z (QuotientGroup.mk v) = QuotientGroup.mk v := by
    rw [kbarConj_mk hKH]
    exact congrArg QuotientGroup.mk (Subtype.ext hzv)
  have hconj : MulAut.conj a (QuotientGroup.mk v) = QuotientGroup.mk v := by
    rw [ha]
    exact hfix
  rw [MulAut.conj_apply] at hconj
  calc QuotientGroup.mk v * a = (a * QuotientGroup.mk v * a⁻¹) * a := by rw [hconj]
    _ = a * QuotientGroup.mk v := by group

private theorem conj_eq_of_conj_mk_eq
    (hKH : ((kSub p M H).subgroupOf H).Normal) {V : Subgroup G}
    (hbot : V.subgroupOf (kSub p M H) ⊓ pCore 2 ↥(kSub p M H) = ⊥)
    {z : ↥H} {a : modTwoCore (kSub p M H)}
    (ha : MulAut.conj a = kbarConj hKH z)
    (hzN : (z : G) ∈ Subgroup.normalizer (V : Set G))
    {v : ↥(kSub p M H)} (hv : (v : G) ∈ V)
    (hfix : a * (QuotientGroup.mk v : modTwoCore (kSub p M H)) * a⁻¹ =
      (QuotientGroup.mk v : modTwoCore (kSub p M H))) :
    (z : G) * (v : G) * (z : G)⁻¹ = (v : G) := by
  have hzvK : (z : G) * (v : G) * (z : G)⁻¹ ∈ kSub p M H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_kSub hKH z.2) (v : G)).mp v.2
  have hconj : kbarConj hKH z (QuotientGroup.mk v) =
      (QuotientGroup.mk v : modTwoCore (kSub p M H)) := by
    rw [← ha]
    exact hfix
  rw [kbarConj_mk hKH] at hconj
  have hdiv : (⟨(z : G) * (v : G) * (z : G)⁻¹, hzvK⟩ : ↥(kSub p M H)) / v ∈
      pCore 2 ↥(kSub p M H) :=
    QuotientGroup.eq_iff_div_mem.mp hconj
  have hdivV : (⟨(z : G) * (v : G) * (z : G)⁻¹, hzvK⟩ : ↥(kSub p M H)) / v ∈
      V.subgroupOf (kSub p M H) := by
    rw [Subgroup.mem_subgroupOf]
    have hcoe : (((⟨(z : G) * (v : G) * (z : G)⁻¹, hzvK⟩ : ↥(kSub p M H)) / v :
        ↥(kSub p M H)) : G) = (z : G) * (v : G) * (z : G)⁻¹ * (v : G)⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc]
    rw [hcoe]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp hzN (v : G)).mp hv) (V.inv_mem hv)
  have hone : (⟨(z : G) * (v : G) * (z : G)⁻¹, hzvK⟩ : ↥(kSub p M H)) / v = 1 := by
    rw [← Subgroup.mem_bot, ← hbot]
    exact ⟨hdivV, hdiv⟩
  have h2 : (z : G) * (v : G) * (z : G)⁻¹ * (v : G)⁻¹ = 1 := by
    simpa [div_eq_mul_inv, mul_assoc] using congrArg Subtype.val hone
  calc (z : G) * (v : G) * (z : G)⁻¹ =
        ((z : G) * (v : G) * (z : G)⁻¹ * (v : G)⁻¹) * (v : G) := by group
    _ = (v : G) := by rw [h2, one_mul]

private theorem not_mem_centralizer_of_conj_eq
    (hKH : ((kSub p M H).subgroupOf H).Normal) {V : Subgroup G}
    (hVK : V ≤ kSub p M H)
    (hbot : V.subgroupOf (kSub p M H) ⊓ pCore 2 ↥(kSub p M H) = ⊥)
    {z : ↥H} {a : modTwoCore (kSub p M H)}
    (ha : MulAut.conj a = kbarConj hKH z)
    (hzN : (z : G) ∈ Subgroup.normalizer (V : Set G))
    (hzC : (z : G) ∉ Subgroup.centralizer (V : Set G)) :
    a ∉ Subgroup.centralizer
      (((V.subgroupOf (kSub p M H)).map
        (QuotientGroup.mk' (pCore 2 ↥(kSub p M H)))) : Set (modTwoCore (kSub p M H))) := by
  intro hcent
  apply hzC
  rw [Subgroup.mem_centralizer_iff]
  intro v hvV
  have hvK : v ∈ kSub p M H := hVK hvV
  have hmemVbar : (QuotientGroup.mk (⟨v, hvK⟩ : ↥(kSub p M H)) : modTwoCore (kSub p M H)) ∈
      (V.subgroupOf (kSub p M H)).map (QuotientGroup.mk' (pCore 2 ↥(kSub p M H))) :=
    Subgroup.mem_map.mpr ⟨⟨v, hvK⟩, Subgroup.mem_subgroupOf.mpr hvV, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hcent _ hmemVbar
  have hfix : a * (QuotientGroup.mk (⟨v, hvK⟩ : ↥(kSub p M H)) : modTwoCore (kSub p M H)) * a⁻¹ =
      (QuotientGroup.mk (⟨v, hvK⟩ : ↥(kSub p M H)) : modTwoCore (kSub p M H)) := by
    rw [← hcomm]
    group
  have hzv := conj_eq_of_conj_mk_eq hKH hbot ha hzN hvV hfix
  have hzv' : z * v = v * z := by
    have h := congrArg (fun t => t * (z : G)) hzv
    simpa [mul_assoc] using h
  exact hzv'.symm

private theorem isSylowOf_subgroupOf_top {P : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 P (kSub 3 M H)) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf (kSub 3 M H)) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hP, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hSyl
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hP.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.le).symm, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact hdvd

private theorem isSylowOf_map_quotient {P : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 P (kSub 3 M H)) :
    CFSG.ABGLocalTools.IsSylowOf 3
      ((P.subgroupOf (kSub 3 M H)).map (kbarMap M H)) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPK := isSylowOf_subgroupOf_top hSyl
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hPK.isPGroup.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro h
  have h1 : 3 ∣ (P.subgroupOf (kSub 3 M H)).index :=
    h.trans ((P.subgroupOf (kSub 3 M H)).index_map_dvd (QuotientGroup.mk'_surjective _))
  have h2 := (CFSG.ABGLocalTools.isSylowOf_iff.1 hPK).2.2
  rw [Subgroup.relIndex_top_right] at h2
  exact h2 h1

private theorem pCoreOf_kSub_le_M
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub 3 M H).subgroupOf H).Normal) :
    pCoreOf 2 (kSub 3 M H) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKleH : kSub 3 M H ≤ H :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H
  have h1 : pCoreOf 2 (kSub 3 M H) ≤ pCoreOf 2 H :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hKleH (le_normalizer_kSub hKH)
  have h2 : pCoreOf 2 H ≤ relPPrimeCore 3 H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore
      (by norm_num) H
  exact (h1.trans h2).trans (relPPrimeCore_le_M_of_twelveCtx hc.ctx)

private theorem map_subgroupOf_inf_ne_top
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub 3 M H).subgroupOf H).Normal) :
    ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) ≠ ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO2M : pCoreOf 2 (kSub 3 M H) ≤ M := pCoreOf_kSub_le_M hc hKH
  intro htop
  refine not_kSub_le_M_of_nineNineOne hc.ctx hc.hI fun x hx => ?_
  have hx' : kbarMap M H ⟨x, hx⟩ ∈
      ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hπm⟩ := Subgroup.mem_map.mp hx'
  have hker : m⁻¹ * ⟨x, hx⟩ ∈ (kbarMap M H).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπm, inv_mul_cancel]
  rw [show (kbarMap M H).ker = pCore 2 ↥(kSub 3 M H) from QuotientGroup.ker_mk' _] at hker
  have hxeq : (⟨x, hx⟩ : ↥(kSub 3 M H)) = m * (m⁻¹ * ⟨x, hx⟩) := by group
  have hxG : x = (m : G) * (((m⁻¹ * ⟨x, hx⟩ : ↥(kSub 3 M H)) : G)) := by
    simpa using congrArg Subtype.val hxeq
  rw [hxG]
  refine M.mul_mem (Subgroup.mem_subgroupOf.mp hm).2 ?_
  exact hO2M (Subgroup.mem_map.mpr ⟨_, hker, rfl⟩)

private theorem normalizer_map_le_inf
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub 3 M H ≤ M)
    (hKH : ((kSub 3 M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub 3 M H) H)
    (hZ : center (modTwoCore (kSub 3 M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub 3 M H))) ≤
      2 * Nat.card (modTwoCore (kSub 3 M H)))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (kSub 3 M H ⊓ M)) :
    Subgroup.normalizer
        (((P.subgroupOf (kSub 3 M H)).map (kbarMap M H)) :
          Set (modTwoCore (kSub 3 M H))) ≤
      ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hSylK, hNM⟩ := hc.sylow_kSub_inf D rfl hXM hKH hK hZ hAut hP
  have h3O : ¬ 3 ∣ Nat.card (pCore 2 ↥(kSub 3 M H)) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(kSub 3 M H))).exists_card_eq
    rw [hn]
    exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by decide)
  have hPKp : IsPGroup 3 (P.subgroupOf (kSub 3 M H)) :=
    hSylK.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSylK.le).symm
  have hnormEq := CFSG.GroupTheory.normal_coprime_quotient_normalizer 3
    (pCore 2 ↥(kSub 3 M H)) h3O (P.subgroupOf (kSub 3 M H)) hPKp
  have hnormSub : Subgroup.normalizer (P.subgroupOf (kSub 3 M H)) =
      (kSub 3 M H ⊓ Subgroup.normalizer (P : Set G)).subgroupOf (kSub 3 M H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hSylK.le]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, x.2, true_and]
  rw [← hnormEq, hnormSub]
  refine Subgroup.map_mono ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hNM (Subgroup.mem_subgroupOf.mp hx).2⟩

private theorem V_inf_pCore_eq_bot (M : Subgroup G)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.V.subgroupOf (kSub 3 M H) ⊓ pCore 2 ↥(kSub 3 M H) = ⊥ :=
  CFSG.ABGLocalTools.inf_eq_bot_of_isPGroup_two (p := 3) (by norm_num)
    (D.cfg.elem.subgroupOf (kSub 3 M H)).isPGroup
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(kSub 3 M H)))

private theorem Vbar_data
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub 3 M H ≤ M)
    (hKH : ((kSub 3 M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub 3 M H) H)
    (hZ : center (modTwoCore (kSub 3 M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub 3 M H))) ≤
      2 * Nat.card (modTwoCore (kSub 3 M H))) :
    IsElemAbelian 3 ((D.V.subgroupOf (kSub 3 M H)).map (kbarMap M H)) ∧
      Nat.card ((D.V.subgroupOf (kSub 3 M H)).map (kbarMap M H)) = 27 ∧
      ((D.V.subgroupOf (kSub 3 M H)).map (kbarMap M H)) ≤
        ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVK : D.V ≤ kSub 3 M H := hc.V_le_kSub D rfl hXM hKH hK hZ hAut
  have hVM : D.V ≤ M := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_right
  have hVKM : D.V ≤ kSub 3 M H ⊓ M := le_inf hVK hVM
  have hVKinfO := V_inf_pCore_eq_bot M D
  refine ⟨(D.cfg.elem.subgroupOf (kSub 3 M H)).map (kbarMap M H), ?_, ?_⟩
  · have hkerJ : D.V.subgroupOf (kSub 3 M H) ⊓ (kbarMap M H).ker = ⊥ := by
      rwa [show (kbarMap M H).ker = pCore 2 ↥(kSub 3 M H) from QuotientGroup.ker_mk' _]
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot (kbarMap M H) hkerJ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, D.cfg.card]
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hVKM)

private theorem sign_pair_data (M : Subgroup G)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) {u : G}
    (hu : u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ⊓ M ⊓ (kSub 3 M H ⊔ xSub 3 M H)) :
    u ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ ∧ u ∈ M ∧ u ∈ H ∧
      u ∈ (kSub 3 M H ⊔ xSub 3 M H : Subgroup G) :=
  ⟨((Subgroup.mem_inf.mp hu).1).1, ((Subgroup.mem_inf.mp hu).1).2,
    (sup_le (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H) (xSub_le_H 3 M H))
      (Subgroup.mem_inf.mp hu).2,
    (Subgroup.mem_inf.mp hu).2⟩

private theorem exists_conj_mem_inf_of_mem_sup
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub 3 M H ≤ M)
    (hKH : ((kSub 3 M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub 3 M H) H)
    (hZ : center (modTwoCore (kSub 3 M H)) = ⊥)
    {u : G} (huH : u ∈ H) (huM : u ∈ M)
    (huKX : u ∈ (kSub 3 M H ⊔ xSub 3 M H : Subgroup G)) :
    ∃ a ∈ ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H),
      MulAut.conj a = kbarConj hKH ⟨u, huH⟩ := by
  have hXNK : xSub 3 M H ≤ Subgroup.normalizer (kSub 3 M H : Set G) :=
    (xSub_le_H 3 M H).trans (le_normalizer_kSub hKH)
  change u ∈ ((kSub 3 M H ⊔ xSub 3 M H : Subgroup G) : Set G) at huKX
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (kSub 3 M H) (xSub 3 M H) hXNK] at huKX
  obtain ⟨k, hkK, x, hxX, hux⟩ := Set.mem_mul.mp huKX
  have hkH : k ∈ H := (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.kSub_le 3 M H) hkK
  have hxH : x ∈ H := xSub_le_H 3 M H hxX
  have hkM : k ∈ M := by
    have hkx : k = u * x⁻¹ := by rw [← hux]; group
    rw [hkx]
    exact M.mul_mem huM (M.inv_mem (hXM hxX))
  have hxker : kbarConj hKH ⟨x, hxH⟩ = 1 := by
    rw [← MonoidHom.mem_ker, TwelveCtx.ker_kbarConj hc.ctx hKH hK hZ]
    exact Subgroup.mem_subgroupOf.mpr hxX
  refine ⟨kbarMap M H ⟨k, hkK⟩,
    Subgroup.mem_map.mpr ⟨⟨k, hkK⟩, Subgroup.mem_subgroupOf.mpr ⟨hkK, hkM⟩, rfl⟩, ?_⟩
  have huk : (⟨u, huH⟩ : ↥H) = ⟨k, hkH⟩ * ⟨x, hxH⟩ := Subtype.ext hux.symm
  calc MulAut.conj (kbarMap M H ⟨k, hkK⟩) = kbarConj hKH ⟨k, hkH⟩ :=
        (kbarConj_coe_eq_conj hKH hkH).symm
    _ = kbarConj hKH ⟨k, hkH⟩ * kbarConj hKH ⟨x, hxH⟩ := by rw [hxker, mul_one]
    _ = kbarConj hKH (⟨k, hkH⟩ * ⟨x, hxH⟩) := (map_mul _ _ _).symm
    _ = kbarConj hKH ⟨u, huH⟩ := by rw [huk]

private theorem sq_mem_centralizer_map_of_conj
    (hKH : ((kSub p M H).subgroupOf H).Normal) {V : Subgroup G}
    {z : ↥H} {a : modTwoCore (kSub p M H)}
    (ha : MulAut.conj a = kbarConj hKH z)
    (hz : (z : G) ^ 2 ∈ Subgroup.centralizer (V : Set G)) :
    a ^ 2 ∈ Subgroup.centralizer
      (((V.subgroupOf (kSub p M H)).map
        (QuotientGroup.mk' (pCore 2 ↥(kSub p M H)))) : Set (modTwoCore (kSub p M H))) := by
  have hconj : MulAut.conj (a ^ 2) = kbarConj hKH (z ^ 2) := by
    rw [map_pow, ha, ← map_pow]
  exact mem_centralizer_of_conj_eq hKH hconj (by simpa using hz)

private theorem commutator_mem_centralizer_map_of_conj
    (hKH : ((kSub p M H).subgroupOf H).Normal) {V : Subgroup G}
    {z z' : ↥H} {a b : modTwoCore (kSub p M H)}
    (ha : MulAut.conj a = kbarConj hKH z) (hb : MulAut.conj b = kbarConj hKH z')
    (hz : (z : G) * (z' : G) * (z : G)⁻¹ * (z' : G)⁻¹ ∈
      Subgroup.centralizer (V : Set G)) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer
      (((V.subgroupOf (kSub p M H)).map
        (QuotientGroup.mk' (pCore 2 ↥(kSub p M H)))) : Set (modTwoCore (kSub p M H))) := by
  have hconj : MulAut.conj (a * b * a⁻¹ * b⁻¹) =
      kbarConj hKH (z * z' * z⁻¹ * z'⁻¹) := by
    simp only [map_mul, map_inv, ha, hb]
  exact mem_centralizer_of_conj_eq hKH hconj (by simpa using hz)

private theorem four_dvd_relindex_klein
    (hc : TwelveSixKCtx G M 3 Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hXM : xSub 3 M H ≤ M)
    (hKH : ((kSub 3 M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub 3 M H) H)
    (hZ : center (modTwoCore (kSub 3 M H)) = ⊥)
    (hAut : Nat.card (MulAut (modTwoCore (kSub 3 M H))) ≤
      2 * Nat.card (modTwoCore (kSub 3 M H))) :
    4 ∣ (((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) ⊓
          Subgroup.centralizer
            (((D.V.subgroupOf (kSub 3 M H)).map (kbarMap M H)) :
              Set (modTwoCore (kSub 3 M H)))).relIndex
        (((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) ⊓
          Subgroup.normalizer
            (((D.V.subgroupOf (kSub 3 M H)).map (kbarMap M H)) :
              Set (modTwoCore (kSub 3 M H)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, u', hu, hu', huc, hu'c, huu'c⟩ := hc.exists_sign_pair D hKH hK hZ hAut
  obtain ⟨huTN, huM, huH, huKX⟩ := sign_pair_data M D hu
  obtain ⟨hu'TN, hu'M, hu'H, hu'KX⟩ := sign_pair_data M D hu'
  obtain ⟨a, haB, ha_conj⟩ :=
    exists_conj_mem_inf_of_mem_sup hc hXM hKH hK hZ huH huM huKX
  obtain ⟨b, hbB, hb_conj⟩ :=
    exists_conj_mem_inf_of_mem_sup hc hXM hKH hK hZ hu'H hu'M hu'KX
  have huu'TN : u * u' ∈ tripleNormalizer D.W₁ D.W₂ D.W₃ :=
    (tripleNormalizer D.W₁ D.W₂ D.W₃).mul_mem huTN hu'TN
  have hVK : D.V ≤ kSub 3 M H := hc.V_le_kSub D rfl hXM hKH hK hZ hAut
  have hVKinfO := V_inf_pCore_eq_bot M D
  have hzN : u ∈ Subgroup.normalizer (D.V : Set G) :=
    IsE27InvConfig.tripleNormalizer_le_normalizer D.cfg huTN
  have hz'N : u' ∈ Subgroup.normalizer (D.V : Set G) :=
    IsE27InvConfig.tripleNormalizer_le_normalizer D.cfg hu'TN
  have hzN' : u * u' ∈ Subgroup.normalizer (D.V : Set G) :=
    IsE27InvConfig.tripleNormalizer_le_normalizer D.cfg huu'TN
  have haa := sq_mem_centralizer_map_of_conj hKH ha_conj
    (IsE27InvConfig.sq_mem_centralizer D.cfg huTN)
  have hbb := sq_mem_centralizer_map_of_conj hKH hb_conj
    (IsE27InvConfig.sq_mem_centralizer D.cfg hu'TN)
  have hab := commutator_mem_centralizer_map_of_conj hKH ha_conj hb_conj
    (IsE27InvConfig.commutator_mem_centralizer D.cfg huTN hu'TN)
  have ha1 := not_mem_centralizer_of_conj_eq hKH hVK hVKinfO ha_conj hzN huc
  have hb1 := not_mem_centralizer_of_conj_eq hKH hVK hVKinfO hb_conj hz'N hu'c
  have hab1 : a * b ∉ Subgroup.centralizer
      (((D.V.subgroupOf (kSub 3 M H)).map (kbarMap M H)) : Set (modTwoCore (kSub 3 M H))) := by
    have hconj : MulAut.conj (a * b) = kbarConj hKH (⟨u, huH⟩ * ⟨u', hu'H⟩) := by
      rw [map_mul, ha_conj, hb_conj, map_mul]
    exact not_mem_centralizer_of_conj_eq hKH hVK hVKinfO hconj hzN' huu'c
  exact four_dvd_relindex_of_klein ⟨haB, mem_normalizer_of_conj_eq hKH ha_conj hzN⟩
    ⟨hbB, mem_normalizer_of_conj_eq hKH hb_conj hz'N⟩ haa hbb hab ha1 hb1 hab1

private theorem thompsonSubgroup_subgroupOf_eq {Q K : Subgroup G} (hQK : Q ≤ K) :
    (Open.thompsonSubgroup Q).subgroupOf K = Open.thompsonSubgroup (Q.subgroupOf K) := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr ((CFSG.ambientMaxCardThompson_le Q).trans hQK)]
  have h := CFSG.map_ambientMaxCardThompson_of_injective (G := ↥K) (H := G) K.subtype
    (Q.subgroupOf K) (K.subtype_injective.comp (Q.subgroupOf K).subtype_injective)
  rw [Subgroup.map_subgroupOf_eq_of_le hQK] at h
  exact h.symm

private theorem map_thompsonSubgroup_quotient {P : Subgroup G}
    (hPK : P ≤ kSub 3 M H)
    (hbot : (P.subgroupOf (kSub 3 M H)) ⊓ pCore 2 ↥(kSub 3 M H) = ⊥) :
    ((Open.thompsonSubgroup P).subgroupOf (kSub 3 M H)).map (kbarMap M H) =
      Open.thompsonSubgroup ((P.subgroupOf (kSub 3 M H)).map (kbarMap M H)) := by
  rw [thompsonSubgroup_subgroupOf_eq (Q := P) (K := kSub 3 M H) hPK]
  have hinj : Function.Injective
      ((kbarMap M H).comp (P.subgroupOf (kSub 3 M H)).subtype) := by
    intro a b hab
    have hmem : ((a : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) *
        (((b : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)))⁻¹ ∈
        pCore 2 ↥(kSub 3 M H) := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥(kSub 3 M H)), MonoidHom.mem_ker]
      have h : kbarMap M H ((a : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) =
          kbarMap M H ((b : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) := hab
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have hPK' : ((a : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) *
        (((b : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)))⁻¹ ∈
        P.subgroupOf (kSub 3 M H) :=
      (P.subgroupOf (kSub 3 M H)).mul_mem a.2 ((P.subgroupOf _).inv_mem b.2)
    have hone : ((a : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) *
        (((b : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)))⁻¹ = 1 := by
      rw [← Subgroup.mem_bot, ← hbot]
      exact ⟨hPK', hmem⟩
    apply Subtype.ext
    have h1 : ((a : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) =
        (((a : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) *
          (((b : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)))⁻¹) *
          ((b : ↥(P.subgroupOf (kSub 3 M H))) : ↥(kSub 3 M H)) := by group
    rw [h1, hone, one_mul]
  exact CFSG.map_ambientMaxCardThompson_of_injective (kbarMap M H) _ hinj

private theorem le_of_map_le_of_le_ker {A C : Subgroup ↥(kSub 3 M H)}
    (hC : pCore 2 ↥(kSub 3 M H) ≤ C)
    (h : A.map (kbarMap M H) ≤ C.map (kbarMap M H)) : A ≤ C := by
  intro x hx
  have hx' : kbarMap M H x ∈ C.map (kbarMap M H) := h (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
  have hmem : x * y⁻¹ ∈ pCore 2 ↥(kSub 3 M H) := by
    rw [← QuotientGroup.ker_mk' (pCore 2 ↥(kSub 3 M H)), MonoidHom.mem_ker]
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have heq : x = (x * y⁻¹) * y := by group
  rw [heq]
  exact C.mul_mem (hC hmem) hy

private theorem eq_of_map_eq_map_of_le_ker {A C : Subgroup ↥(kSub 3 M H)}
    (hA : pCore 2 ↥(kSub 3 M H) ≤ A) (hC : pCore 2 ↥(kSub 3 M H) ≤ C)
    (h : A.map (kbarMap M H) = C.map (kbarMap M H)) : A = C :=
  le_antisymm (le_of_map_le_of_le_ker hC h.le) (le_of_map_le_of_le_ker hA h.ge)

private theorem normalizer_map_thompson
    (hKH : ((kSub 3 M H).subgroupOf H).Normal)
    {P : Subgroup G} (hPK : P ≤ kSub 3 M H)
    (hbot : (P.subgroupOf (kSub 3 M H)) ⊓ pCore 2 ↥(kSub 3 M H) = ⊥)
    (hS3 : IsPGroup 3 ((Open.thompsonSubgroup P).subgroupOf (kSub 3 M H))) :
    ((kSub 3 M H ⊓ Subgroup.normalizer (Open.thompsonSubgroup P : Set G)).subgroupOf
        (kSub 3 M H)).map (kbarMap M H) =
      Subgroup.normalizer
        (Open.thompsonSubgroup ((P.subgroupOf (kSub 3 M H)).map (kbarMap M H)) :
          Set (modTwoCore (kSub 3 M H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3O : ¬ 3 ∣ Nat.card (pCore 2 ↥(kSub 3 M H)) := by
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(kSub 3 M H))).exists_card_eq
    rw [hn]
    exact fun h => absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by decide)
  have hmapJ := map_thompsonSubgroup_quotient hPK hbot
  have hnorm := CFSG.GroupTheory.normal_coprime_quotient_normalizer 3
    (pCore 2 ↥(kSub 3 M H)) h3O ((Open.thompsonSubgroup P).subgroupOf (kSub 3 M H)) hS3
  have hJle : Open.thompsonSubgroup P ≤ kSub 3 M H := (CFSG.ambientMaxCardThompson_le P).trans hPK
  have hS_eq : Subgroup.normalizer ((Open.thompsonSubgroup P).subgroupOf (kSub 3 M H)) =
      ((kSub 3 M H ⊓ Subgroup.normalizer (Open.thompsonSubgroup P : Set G))).subgroupOf
        (kSub 3 M H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hJle]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, x.2, true_and]
  rw [← hmapJ, ← hnorm, hS_eq]

private theorem k_inter_of_normalizer_eq
    (hKH : ((kSub 3 M H).subgroupOf H).Normal)
    (hO2M : pCoreOf 2 (kSub 3 M H) ≤ M)
    {P : Subgroup G} (hPK : P ≤ kSub 3 M H)
    (hbot : (P.subgroupOf (kSub 3 M H)) ⊓ pCore 2 ↥(kSub 3 M H) = ⊥)
    (hS3 : IsPGroup 3 ((Open.thompsonSubgroup P).subgroupOf (kSub 3 M H)))
    (hBN : ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) =
      Subgroup.normalizer
        (Open.thompsonSubgroup ((P.subgroupOf (kSub 3 M H)).map (kbarMap M H)) :
          Set (modTwoCore (kSub 3 M H)))) :
    kSub 3 M H ⊓ M =
      (kSub 3 M H ⊓ normalizer (Open.thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub 3 M H) := by
  have hNJKmap := normalizer_map_thompson hKH hPK hbot hS3
  have hOmap : (pCore 2 ↥(kSub 3 M H)).map (kbarMap M H) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff,
      show (kbarMap M H).ker = pCore 2 ↥(kSub 3 M H) from QuotientGroup.ker_mk' _]
  have hO_KM : pCore 2 ↥(kSub 3 M H) ≤ (kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H) := by
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr ⟨x.2, ?_⟩
    exact hO2M (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hmap : ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) =
      (((kSub 3 M H ⊓ Subgroup.normalizer (Open.thompsonSubgroup P : Set G)).subgroupOf
          (kSub 3 M H)) ⊔ pCore 2 ↥(kSub 3 M H)).map (kbarMap M H) := by
    rw [Subgroup.map_sup, hOmap, sup_bot_eq, hNJKmap]
    exact hBN
  have hKM := eq_of_map_eq_map_of_le_ker hO_KM le_sup_right hmap
  have hmapall := congrArg (Subgroup.map (kSub 3 M H).subtype) hKM
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype] at hmapall
  simpa [inf_eq_left.mpr (inf_le_left : kSub 3 M H ⊓ M ≤ kSub 3 M H),
    inf_eq_left.mpr (inf_le_left : kSub 3 M H ⊓
      Subgroup.normalizer (Open.thompsonSubgroup P : Set G) ≤ kSub 3 M H), pCoreOf]
    using hmapall

theorem TwelveSixKCtx.k_inter
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hXM : xSub p M H ≤ M) (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hty : LieModel (modTwoCore (kSub p M H)) .PSp 2 3 1 ∨
      Nonempty (modTwoCore (kSub p M H) ≃* alternatingGroup (Fin 9)))
    (hJ : KFactKbarThompsonNormalizer) :
    ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (kSub p M H ⊓ M) →
      kSub p M H ⊓ M =
        (kSub p M H ⊓ normalizer (Open.thompsonSubgroup P : Set G)) ⊔ pCoreOf 2 (kSub p M H) := by
  subst hp
  intro P hP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : center (modTwoCore (kSub 3 M H)) = ⊥ := center_eq_bot_of_kbarType hty
  have hAut : Nat.card (MulAut (modTwoCore (kSub 3 M H))) ≤
      2 * Nat.card (modTwoCore (kSub 3 M H)) := card_mulAut_le_two_mul_of_kbarType hty
  obtain ⟨hSylK, -⟩ := hc.sylow_kSub_inf D rfl hXM hKH hK hZ hAut hP
  have hO2M : pCoreOf 2 (kSub 3 M H) ≤ M := pCoreOf_kSub_le_M hc hKH
  have hPbarSylow : CFSG.ABGLocalTools.IsSylowOf 3
      ((P.subgroupOf (kSub 3 M H)).map (kbarMap M H)) ⊤ := isSylowOf_map_quotient hSylK
  have hBne : ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) ≠ ⊤ :=
    map_subgroupOf_inf_ne_top hc hKH
  have hNle := normalizer_map_le_inf hc D hXM hKH hK hZ hAut hP
  obtain ⟨hVbarElem, hVbarCard, hVbarLe⟩ := Vbar_data hc D hXM hKH hK hZ hAut
  have h4 := four_dvd_relindex_klein hc D hXM hKH hK hZ hAut
  have hBN : ((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H) =
      Subgroup.normalizer
        (Open.thompsonSubgroup ((P.subgroupOf (kSub 3 M H)).map (kbarMap M H)) :
          Set (modTwoCore (kSub 3 M H))) :=
    hJ (modTwoCore (kSub 3 M H)) hty ((P.subgroupOf (kSub 3 M H)).map (kbarMap M H))
      (((kSub 3 M H ⊓ M).subgroupOf (kSub 3 M H)).map (kbarMap M H))
      ((D.V.subgroupOf (kSub 3 M H)).map (kbarMap M H))
      hPbarSylow hBne hNle hVbarLe hVbarElem hVbarCard h4
  have hbot : (P.subgroupOf (kSub 3 M H)) ⊓ pCore 2 ↥(kSub 3 M H) = ⊥ :=
    CFSG.ABGLocalTools.inf_eq_bot_of_isPGroup_two (p := 3) (by norm_num)
      (hP.isPGroup.comap_subtype)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(kSub 3 M H)))
  have hS3 : IsPGroup 3 ((Open.thompsonSubgroup P).subgroupOf (kSub 3 M H)) :=
    (hP.isPGroup.comap_subtype).to_le
      (Subgroup.subgroupOf_mono _ (CFSG.ambientMaxCardThompson_le P))
  exact k_inter_of_normalizer_eq hKH hO2M hSylK.le hbot hS3 hBN

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
