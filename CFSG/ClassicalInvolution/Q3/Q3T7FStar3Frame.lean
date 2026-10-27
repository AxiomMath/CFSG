module

public import CFSG.ClassicalInvolution.Q3.Q3T7FStar3
public import CFSG.ClassicalInvolution.Q3.TA3FrameSplit
public import CFSG.ClassicalInvolution.Q3.Q3T6YFinal
public import CFSG.ClassicalInvolution.Q3.Q3T6XCore
public import CFSG.ClassicalInvolution.Q3.TL3TopRestrict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3T.MFS
open scoped MatrixGroups

section Quotient

variable {K : Type} [Group K] [Finite K]

theorem mem_sup_oddCore_of_sl2Three (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, ZMod 3))
    {P : Subgroup K} (hP : IsPGroup 2 P) (hP8 : Nat.card P = 8) {x : K}
    (hx : IsPGroup 2 (Subgroup.zpowers x)) : x ∈ P ⊔ classicalInvolutionOddCore K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := classicalInvolutionOddCore K with hOdef
  set φ : K →* K ⧸ O := QuotientGroup.mk' O with hφ
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card K
  have hinj : Function.Injective (φ.comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hqO : (q : K) ∈ O := (QuotientGroup.eq_one_iff _).mp hq
    obtain ⟨k, hk⟩ := hP q
    have hk' : (q : K) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subtype.ext (eq_one_of_odd_of_pow_two hOodd hqO hk')
  have hcard : Nat.card (P.map φ) = 8 := by
    have h1 : (φ.comp P.subtype).range = P.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hP8]
  have h24 : Nat.card (K ⧸ O) = 24 := by
    rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hidx : (P.map φ).index = 3 := by
    have h := (P.map φ).card_mul_index
    rw [hcard, h24] at h
    omega
  let S : Sylow 2 (K ⧸ O) := (hP.map φ).toSylow (by rw [hidx]; norm_num)
  obtain ⟨S', hS'⟩ := (hx.map φ).exists_le_sylow
  have hSS : (S' : Subgroup (K ⧸ O)) = S :=
    (sylow_eq_pCore_of_mulEquiv_sl2Three e S').trans (sylow_eq_pCore_of_mulEquiv_sl2Three e S).symm
  have hxS : φ x ∈ P.map φ := by
    have h1 : φ x ∈ (S' : Subgroup (K ⧸ O)) :=
      hS' (Subgroup.mem_map_of_mem φ (Subgroup.mem_zpowers x))
    rw [hSS] at h1
    exact h1
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hxS
  have hqO : q⁻¹ * x ∈ O := QuotientGroup.eq.mp hqx
  have hx' : x = q * (q⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hqO)

end Quotient

section Saturation

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_sup_of_isPGroup_satU {z : Y} {L : Subgroup Y} (hz : IsClassicalMember3 L z)
    (Q : Sylow 2 L) {x : Y} (hx : x ∈ satU (.sl2 3 1) L z) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    x ∈ (Q : Subgroup L).map L.subtype ⊔ oddCoreIn (Subgroup.centralizer ({z} : Set Y)) := by
  set K := satU (.sl2 3 1) L z with hKdef
  set Q' : Subgroup Y := (Q : Subgroup L).map L.subtype with hQ'def
  have hm : IsClassicalMemberU (.sl2 3 1) K z := (IsClassicalMemberU.ofQ3 hz).satU_member
  have hi : IsIntrinsicU (.sl2 3 1) K z := isIntrinsicU_satU _ _ _
  have hK3 : IsClassicalMember3 K z := hm.toQ3 (by norm_num)
  obtain ⟨e⟩ := hK3.nonempty_equiv
  have hQ'K : Q' ≤ K := (Subgroup.map_subtype_le _).trans le_satU
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map L.subtype
  have hP2 : IsPGroup 2 (Q'.subgroupOf K) := hQ'2.comap_of_injective K.subtype K.subtype_injective
  have hP8 : Nat.card (Q'.subgroupOf K) = 8 := by
    obtain ⟨eQ⟩ := Q3T6.quaternion_sylow_of_isClassicalMember3 hz Q
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'K).toEquiv, hQ'def,
      Subgroup.card_map_of_injective L.subtype_injective, Nat.card_congr eQ.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hx2' : IsPGroup 2 (Subgroup.zpowers (⟨x, hx⟩ : K)) :=
    (hx2.comap_of_injective K.subtype K.subtype_injective).to_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers x))
  have hmem := mem_sup_oddCore_of_sl2Three e hP2 hP8 hx2'
  have hOK : oddCoreIn K = oddCoreIn (Subgroup.centralizer ({z} : Set Y)) :=
    oddCoreIn_eq_of_intrinsic hm (hi U4.solvableType_three)
  have hmap : x ∈ (Q'.subgroupOf K ⊔ classicalInvolutionOddCore K).map K.subtype :=
    ⟨⟨x, hx⟩, hmem, rfl⟩
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hQ'K] at hmap
  rw [← hOK]
  exact hmap

theorem normal_sup_oddCoreIn_of_le_normalizer {z : Y} {L : Subgroup Y}
    (hz : IsClassicalMember3 L z) (Q : Sylow 2 L)
    (hN : Subgroup.centralizer ({z} : Set Y) ≤
      Subgroup.normalizer (satU (.sl2 3 1) L z : Set Y)) :
    (((Q : Subgroup L).map L.subtype ⊔
      oddCoreIn (Subgroup.centralizer ({z} : Set Y))).subgroupOf
      (Subgroup.centralizer ({z} : Set Y))).Normal := by
  set C := Subgroup.centralizer ({z} : Set Y) with hCdef
  set Q' : Subgroup Y := (Q : Subgroup L).map L.subtype with hQ'def
  have hLC : L ≤ C := isSubnormal_le hz.subnormal
  have hQ'L : Q' ≤ L := Subgroup.map_subtype_le _
  have hQ'C : Q' ≤ C := hQ'L.trans hLC
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map L.subtype
  refine ⟨fun n hn c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨q, hq, o, ho, hqo⟩ := mem_sup_oddCoreIn hQ'C hn
  have hqK : q ∈ satU (.sl2 3 1) L z := le_satU (hQ'L hq)
  have hcq : (c : Y) * q * (c : Y)⁻¹ ∈ satU (.sl2 3 1) L z :=
    (Subgroup.mem_normalizer_iff.mp (hN c.2) q).mp hqK
  have hq2 : IsPGroup 2 (Subgroup.zpowers ((c : Y) * q * (c : Y)⁻¹)) :=
    AscHypOmega.isPGroup_zpowers_conj (hQ'2.to_le (Subgroup.zpowers_le.mpr hq)) (c : Y)
  have h1 := mem_sup_of_isPGroup_satU hz Q hcq hq2
  have h2 : (c : Y) * o * (c : Y)⁻¹ ∈ oddCoreIn C := conj_mem_oddCoreIn c.2 ho
  have he : ((c * n * c⁻¹ : C) : Y) = ((c : Y) * q * (c : Y)⁻¹) * ((c : Y) * o * (c : Y)⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hqo]
    group
  rw [he]
  exact Subgroup.mul_mem _ h1 (Subgroup.mem_sup_right h2)

theorem hypOmegaModU_satU {L : Subgroup Y} {z : Y} (hz : IsClassicalMember3 L z) :
    HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass (satU (.sl2 3 1) L z)) := by
  have hm : IsClassicalMemberU (.sl2 3 1) (satU (.sl2 3 1) L z) z :=
    (IsClassicalMemberU.ofQ3 hz).satU_member
  have hi : IsIntrinsicU (.sl2 3 1) (satU (.sl2 3 1) L z) z := isIntrinsicU_satU _ _ _
  exact hypOmegaModU_conjClass (MemberType.cert_sl2 3 1) hm hi
    (omega5At_of_twoElementsNormalize hm (Q3T6X.twoElementsNormalize_of_min ⟨hm, hi⟩
      (Q3T6X.fusion3MinOn_of_min _ (Q3T6Y.fusion3Min_all Y))))

end Saturation

section Frame

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T.MFS.Setting.thm7_family {Y : Type} [Group Y]
    [Finite Y] {z : Y} {L T : Subgroup Y}
    (hS : Setting z L T) (hQ : ∀ Q : Sylow 2 L, ¬ QOddNormalInT z L T Q) :
    genFittingFStar Y = T ∧
      HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass (satU (.sl2 3 1) L z)) ∧
      (⨆ J ∈ CoreAssembly.conjClass (satU (.sl2 3 1) L z), J) = ⊤ ∧
      ∃ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 3 1) L z)) (satU (.sl2 3 1) L z),
        K' ≠ satU (.sl2 3 1) L z := by
  have hTn : T.Normal := hS.normal
  obtain ⟨hTs, hTnab⟩ := simple_of_isComponentOf_cent hS.comp hS.cent
  set K := satU (.sl2 3 1) L z with hKdef
  have hm : IsClassicalMemberU (.sl2 3 1) K z := (IsClassicalMemberU.ofQ3 hS.member).satU_member
  have hi : IsIntrinsicU (.sl2 3 1) K z := isIntrinsicU_satU _ _ _
  have hM : U4.Mem3 K z := ⟨hm, hi⟩
  have hgenK : Subgroup.normalClosure (K : Set Y) = ⊤ := by
    rw [eq_top_iff, ← hS.gen]
    exact Subgroup.normalClosure_mono (fun x hx => le_satU hx)
  refine ⟨genFittingFStar_eq_of_normal_simple T hTnab hS.cent, hypOmegaModU_satU hS.member,
    Q3B.conjClass_generated hgenK, ?_⟩
  by_contra hno
  push Not at hno
  have hN : Subgroup.centralizer ({z} : Set Y) ≤ Subgroup.normalizer (K : Set Y) := by
    intro c hc
    have hcz : c * z * c⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have hKc : IsUniqueInvolution (conjSub c K) z := by
      have := (hM.conj c).isUniqueInvolution
      rwa [hcz] at this
    exact mem_normalizer_iff_conjSub_eq.mpr (hno _ ⟨⟨c, rfl⟩, z, hM.isUniqueInvolution, hKc⟩)
  obtain ⟨Q⟩ : Nonempty (Sylow 2 L) := inferInstance
  exact hQ Q (QOddNormalInT.of_normal (normal_sup_oddCoreIn_of_le_normalizer hS.member Q hN))

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T.MFS.Setting.not_isSimpleGroup {Y : Type}
    [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}
    (hS : Setting z L T) (h3 : memberIndex L T = 3) : ¬ IsSimpleGroup Y := by
  intro hYs
  have hTn : T.Normal := hS.normal
  obtain ⟨hTs, -⟩ := simple_of_isComponentOf_cent hS.comp hS.cent
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hbot | htop
  · exact (Subgroup.nontrivial_iff_ne_bot T).mp inferInstance hbot
  · rw [htop] at h3
    simp [memberIndex] at h3

theorem residualCFrameLarge_of_thm7FStar3Large (h7 : Thm7FStar3Large) :
    TA3.ResidualCFrameLarge := by
  intro Y _ _ hB z L T hS _ h3 hQ hlarge
  obtain ⟨hF, hΩ, hgen, htwin⟩ := hS.thm7_family hQ
  obtain ⟨hTs, hTnab⟩ := simple_of_isComponentOf_cent hS.comp hS.cent
  let eF : ↥(genFittingFStar Y) ≃* ↥T := MulEquiv.subgroupCongr hF
  have : IsSimpleGroup ↥(genFittingFStar Y) := eF.isSimpleGroup
  have hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hTnab
    refine ⟨eF.symm a, eF.symm b, fun h => hab ?_⟩
    simpa using congrArg eF h
  have hZ : Subgroup.center ↥T = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥T) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hTnab
      have ha : a ∈ Subgroup.center ↥T := by
        rw [h]
        exact Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  have hTT : genFittingFStar ↥T = ⊤ := by
    have : IsSimpleGroup ↥(⊤ : Subgroup ↥T) := Subgroup.topEquiv.isSimpleGroup
    refine genFittingFStar_eq_of_normal_simple (⊤ : Subgroup ↥T) ?_ ?_
    · obtain ⟨a, b, hab⟩ := hTnab
      exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩,
        fun h => hab (congrArg Subtype.val h)⟩
    · rw [Subgroup.coe_top, Subgroup.centralizer_univ]
      exact hZ
  have hlargeY : ¬ TwoSubgroupsFourGenerated ↥(genFittingFStar Y) := by
    intro h4
    apply hlarge
    exact twoSubgroupsFourGenerated_of_mulEquiv
      ((MulEquiv.subgroupCongr hTT).trans (Subgroup.topEquiv.trans eF.symm)).symm h4
  exact hS.not_isSimpleGroup h3 (h7 Y hnab hlargeY hB _ _ hΩ (CoreAssembly.mem_conjClass_self _)
    (fun J hJ => hJ) hgen htwin)

end Frame

end CFSG.ClassicalInvolution.Q3
