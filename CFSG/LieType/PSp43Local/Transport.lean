module

import CFSG.LieType.PSp43Local.Parabolic
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.PSp43Centralizer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.AltCase
import CFSG.GroupTheory.SylowCentralCoprimeQuotient
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GroupTheory.QuasiDihedralFusion.Transport
import CFSG.ClassicalInvolution.RouteD.TypeABridge
import CFSG.Holt.H78.Prelim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LieType.PSp43Local

open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435 CFSG.GH74.Exceptional

private theorem not_three_dvd_card_pCore_two {X : Type*} [Group X] [Finite X] :
    ¬ 3 ∣ Nat.card (CFSG.pCore 2 X) := by
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  rw [hn]
  intro h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by decide)

private theorem thompsonSubgroup_subgroupOf_eq {G : Type*} [Group G] {Q K : Subgroup G}
    (hQK : Q ≤ K) :
    (CFSG.Open.thompsonSubgroup Q).subgroupOf K =
      CFSG.Open.thompsonSubgroup (Q.subgroupOf K) := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr ((CFSG.ambientMaxCardThompson_le Q).trans hQK)]
  have h := CFSG.map_ambientMaxCardThompson_of_injective (G := ↥K) (H := G) K.subtype
    (Q.subgroupOf K) (K.subtype_injective.comp (Q.subgroupOf K).subtype_injective)
  rw [Subgroup.map_subgroupOf_eq_of_le hQK] at h
  exact h.symm

private theorem isMulCommutative_map_iff_of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) {D : Subgroup G} (hf : Function.Injective (f.comp D.subtype)) :
    IsMulCommutative (D.map f) ↔ IsMulCommutative D := by
  have hbij : Function.Bijective (f.subgroupMap D) :=
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.subgroupMap_surjective D⟩
  let e := MulEquiv.ofBijective (f.subgroupMap D) hbij
  exact ⟨CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv e.symm,
    CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv e⟩

private theorem le_centerIn_of_map_le_centerIn {G H : Type*} [Group G] [Group H]
    (f : G →* H) {D B : Subgroup G} (hBD : B ≤ D)
    (hf : Function.Injective (f.comp D.subtype))
    (h : B.map f ≤ CFSG.centerIn (D.map f)) : B ≤ CFSG.centerIn D := by
  intro b hb
  have hbD : b ∈ D := hBD hb
  refine Subgroup.mem_inf.mpr ⟨hbD, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hcent := h (Subgroup.mem_map_of_mem f hb)
  have hcommH : f d * f b = f b * f d :=
    Subgroup.mem_centralizer_iff.mp hcent.2 (f d) (Subgroup.mem_map_of_mem f hd)
  have hcommD : (⟨d, hd⟩ : ↥D) * ⟨b, hbD⟩ = ⟨b, hbD⟩ * ⟨d, hd⟩ := by
    apply hf
    simpa using hcommH
  exact congrArg Subtype.val hcommD

private theorem le_centerIn_of_subgroupOf_le {G : Type*} [Group G] {K D B : Subgroup G}
    (hBK : B ≤ K) (hBD : B ≤ D) (hDK : D ≤ K)
    (h : B.subgroupOf K ≤ CFSG.centerIn (D.subgroupOf K)) : B ≤ CFSG.centerIn D := by
  intro b hb
  have hbK : (⟨b, hBK hb⟩ : ↥K) ∈ CFSG.centerIn (D.subgroupOf K) :=
    h (Subgroup.mem_subgroupOf.mpr hb)
  refine Subgroup.mem_inf.mpr ⟨hBD hb, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hdK : (⟨d, hDK hd⟩ : ↥K) ∈ (D.subgroupOf K : Subgroup ↥K) := hd
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hbK.2 ⟨d, hDK hd⟩ hdK)

private theorem map_normalizer_mk_comp_equiv_eq {G H : Type*} [Group G] [Finite G] [Group H]
    {N : Subgroup G} [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (ψ : G ⧸ N ≃* H)
    {X : Subgroup G} (hX : IsPGroup 3 X) :
    (Subgroup.normalizer (X : Set G)).map (ψ.toMonoidHom.comp (QuotientGroup.mk' N)) =
      Subgroup.normalizer ((X.map (ψ.toMonoidHom.comp (QuotientGroup.mk' N)) :
        Subgroup H) : Set H) := by
  rw [← Subgroup.map_map, CFSG.Holt.H78.lemma_1_8_normalizer N hN hX,
    Subgroup.map_equiv_normalizer_eq, Subgroup.map_map]

private theorem mem_sup_normalizer_of_map_normalizer_eq {G H : Type*} [Group G] [Group H]
    {φ : G →* H} {N : Subgroup G} (hker : φ.ker = N) {Y : Subgroup G} {x : G}
    (hmap : (Subgroup.normalizer (Y : Set G)).map φ =
      Subgroup.normalizer (Y.map φ : Set H))
    (hx : φ x ∈ Subgroup.normalizer (Y.map φ : Set H)) :
    x ∈ Subgroup.normalizer (Y : Set G) ⊔ N := by
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hmem : y⁻¹ * x ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  rw [hker] at hmem
  have hx_eq : x = y * (y⁻¹ * x) := by group
  rw [hx_eq]
  exact Subgroup.mul_mem_sup hy hmem

private theorem injective_comp_subtype_of_le {G H : Type*} [Group G] [Group H]
    {f : G →* H} {X Y : Subgroup G} (hXY : X ≤ Y)
    (h : Function.Injective (f.comp Y.subtype)) :
    Function.Injective (f.comp X.subtype) := by
  intro a b hab
  have hY : (⟨a, hXY a.2⟩ : ↥Y) = ⟨b, hXY b.2⟩ := h (by exact hab)
  exact Subtype.ext (congrArg (fun z : ↥Y => (z : G)) hY)

theorem nonempty_mulEquiv_W3_of_lieModel {S : Type} [Group S]
    (h : CFSG.Blueprint.LieModel S .PSp 2 3 1) (Q : Sylow 3 S) :
    Nonempty (↥(Q : Subgroup S) ≃* W3) := by
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.psp43_equiv_of_lieModel h
  haveI : Finite S := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr φ.toEquiv, card_PSp43]
    norm_num)
  let Q' : Sylow 3 PSp43 := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective Q
  obtain ⟨e⟩ := nonempty_mulEquiv_W3_of_sylow Q'
  exact ⟨(MulEquiv.subgroupMap φ (Q : Subgroup S)).trans e⟩

theorem nonempty_mulEquiv_W3_of_quotient_pCore_two {G : Type} [Group G] [Finite G]
    {K Q : Subgroup G}
    (hK : CFSG.Blueprint.LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 3 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 9)))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) : Nonempty (↥Q ≃* W3) := by
  obtain ⟨Qs, hQs⟩ := hQ.exists_sylow_eq_subgroupOf
  have hQK : IsPGroup 3 (Q.subgroupOf K) := hQ.isPGroup.comap_subtype
  obtain ⟨e1⟩ := CFSG.GroupTheory.nonempty_mulEquiv_map_mk_of_isPGroup
    (p := 3) (N := CFSG.pCore 2 ↥K) not_three_dvd_card_pCore_two hQK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Qπ : Sylow 3 (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)) Qs
  have hQπ : (Qπ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) =
      (Q.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
    rw [Sylow.coe_mapSurjective, ← hQs]
  let eQ : ↥Q ≃* ↥(Qs : Subgroup ↥K) :=
    (Subgroup.subgroupOfEquivOfLe hQ.le).symm.trans (MulEquiv.subgroupCongr hQs.symm)
  let e1' : ↥(Qs : Subgroup ↥K) ≃* ↥Qπ :=
    (MulEquiv.subgroupCongr hQs).trans
      (e1.trans (MulEquiv.subgroupCongr hQπ.symm))
  let eAll : ↥Q ≃* ↥Qπ := eQ.trans e1'
  rcases hK with hLie | hA
  · obtain ⟨e2⟩ := nonempty_mulEquiv_W3_of_lieModel hLie Qπ
    exact ⟨eAll.trans e2⟩
  · obtain ⟨ψA⟩ := hA
    let Q9 : Sylow 3 (alternatingGroup (Fin 9)) :=
      Qπ.mapSurjective (f := ψA.toMonoidHom) ψA.surjective
    have hQ9 : (Q9 : Subgroup (alternatingGroup (Fin 9))) =
        (Qπ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)).map ψA.toMonoidHom :=
      Sylow.coe_mapSurjective (f := ψA.toMonoidHom) ψA.surjective Qπ
    obtain ⟨e2⟩ := sylow_alt_W3 (n := 9) (by norm_num) (by norm_num) Q9
    exact ⟨eAll.trans ((MulEquiv.subgroupMap ψA (Qπ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))).trans
      ((MulEquiv.subgroupCongr hQ9.symm).trans e2))⟩


private theorem map_normalizer_le_of_le_of_quotient_pCore_two {G : Type} [Group G] [Finite G]
    {K M Q D : Subgroup G} (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* PSp43)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q)
    (hNM : K ⊓ Subgroup.normalizer (D : Set G) ≤ M)
    (hKM : K ⊓ M ≤ (K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
      CFSG.Open.pCoreOf 2 K) :
    (Subgroup.normalizer (D.subgroupOf K : Set ↥K)).map
        (ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) ≤
      (Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map
        (ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) := by
  let N : Subgroup ↥K := CFSG.pCore 2 ↥K
  haveI hNnormal : N.Normal := CFSG.pCore_normal
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_pCore_two
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N
  let φ : ↥K →* PSp43 := ψ.toMonoidHom.comp π
  have hQK : IsPGroup 3 (Q.subgroupOf K) := hQ.isPGroup.comap_subtype
  have hDK : D ≤ K := hDQ.trans hQ.le
  have hJQK : CFSG.Open.thompsonSubgroup Q ≤ K :=
    (CFSG.ambientMaxCardThompson_le Q).trans hQ.le
  have hnormD : (Subgroup.normalizer (D.subgroupOf K : Set ↥K)).map φ =
      Subgroup.normalizer ((D.subgroupOf K).map φ : Set PSp43) :=
    map_normalizer_mk_comp_equiv_eq hN3 ψ (hQK.to_le (Subgroup.subgroupOf_mono K hDQ))
  have hnormJ : (Subgroup.normalizer
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map φ =
      Subgroup.normalizer (((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ :
        Set PSp43) :=
    map_normalizer_mk_comp_equiv_eq hN3 ψ
      (hQK.to_le (Subgroup.subgroupOf_mono K (CFSG.ambientMaxCardThompson_le Q)))
  have hsub : (K ⊓ Subgroup.normalizer (D : Set G)).subgroupOf K ≤
      ((K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
        CFSG.Open.pCoreOf 2 K).subgroupOf K :=
    Subgroup.subgroupOf_mono K ((le_inf inf_le_left hNM).trans hKM)
  have hleft : (K ⊓ Subgroup.normalizer (D : Set G)).subgroupOf K =
      Subgroup.normalizer (D.subgroupOf K : Set ↥K) := by
    rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hDK]
  have hright : ((K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
        CFSG.Open.pCoreOf 2 K).subgroupOf K =
      Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K) ⊔ N := by
    rw [show CFSG.Open.pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype from rfl,
      Subgroup.subgroupOf_sup inf_le_left (Subgroup.map_subtype_le _)]
    congr 1
    · rw [Subgroup.inf_subgroupOf_left, Subgroup.subgroupOf_normalizer_eq hJQK]
    · exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective (CFSG.pCore 2 ↥K)
  have hnorm : Subgroup.normalizer (D.subgroupOf K : Set ↥K) ≤
      Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K) ⊔ N := by
    have := hsub
    rwa [hleft, hright] at this
  have hNmap : N.map φ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_bot, MonoidHom.comp_apply]
    have hπn : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [hπn, map_one]
  have h1 : (Subgroup.normalizer (D.subgroupOf K : Set ↥K)).map φ ≤
      (Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K) ⊔
        N).map φ :=
    Subgroup.map_mono (f := φ) hnorm
  rw [Subgroup.map_sup, hNmap, sup_bot_eq] at h1
  simpa only [φ, N, π] using h1

private theorem false_of_map_normalizer_le {G : Type} [Group G] [Finite G]
    {K Q D : Subgroup G} (ψ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* PSp43)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q) (hD : Nat.card D = 27)
    (h3 : ∀ x ∈ D, x ^ 3 = 1) (hnc : ¬ IsMulCommutative D)
    (hmap : (Subgroup.normalizer (D.subgroupOf K : Set ↥K)).map
        (ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) ≤
      (Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map
        (ψ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))) : False := by
  let N : Subgroup ↥K := CFSG.pCore 2 ↥K
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_pCore_two
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψm : ↥K ⧸ N →* PSp43 := ψ.toMonoidHom
  have hψinj : Function.Injective ψm := ψ.injective
  have hψsurj : Function.Surjective ψm := ψ.surjective
  let π : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N
  let φ : ↥K →* PSp43 := ψm.comp π
  obtain ⟨Qs, hQs⟩ := hQ.exists_sylow_eq_subgroupOf
  have hQK : IsPGroup 3 (Q.subgroupOf K) := hQ.isPGroup.comap_subtype
  have hπinj : Function.Injective (π.comp (Q.subgroupOf K).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hN3 hQK
  have hφinjQ : Function.Injective (φ.comp (Q.subgroupOf K).subtype) := by
    intro a b hab
    exact hπinj (hψinj (by simpa only [φ, ψm, MonoidHom.comp_apply] using hab))
  have hDK : D ≤ K := hDQ.trans hQ.le
  have hφinjD : Function.Injective (φ.comp (D.subgroupOf K).subtype) :=
    injective_comp_subtype_of_le (Subgroup.subgroupOf_mono K hDQ) hφinjQ
  let Q' : Sylow 3 PSp43 :=
    (Sylow.mapSurjective (QuotientGroup.mk'_surjective N) Qs).mapSurjective
      (f := ψm) hψsurj
  have hQ'coe : (Q' : Subgroup PSp43) = (Q.subgroupOf K).map φ := by
    dsimp only [Q']
    rw [Sylow.coe_mapSurjective, Sylow.coe_mapSurjective, ← hQs, Subgroup.map_map]
  have hJQeq : ((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ =
      CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) := by
    have h2 := CFSG.map_ambientMaxCardThompson_of_injective φ (Q.subgroupOf K) hφinjQ
    rw [thompsonSubgroup_subgroupOf_eq hQ.le, h2, hQ'coe]
  have hnormD : (Subgroup.normalizer (D.subgroupOf K : Set ↥K)).map φ =
      Subgroup.normalizer ((D.subgroupOf K).map φ : Set PSp43) :=
    map_normalizer_mk_comp_equiv_eq hN3 ψ (hQK.to_le (Subgroup.subgroupOf_mono K hDQ))
  have hnormJ : (Subgroup.normalizer
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map φ =
      Subgroup.normalizer (((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ :
        Set PSp43) :=
    map_normalizer_mk_comp_equiv_eq hN3 ψ
      (hQK.to_le (Subgroup.subgroupOf_mono K (CFSG.ambientMaxCardThompson_le Q)))
  have hDQ' : (D.subgroupOf K).map φ ≤ (Q' : Subgroup PSp43) := by
    rw [hQ'coe]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hDQ)
  have hbijD : Function.Bijective (φ.subgroupMap (D.subgroupOf K)) :=
    ⟨fun _ _ h => hφinjD (congrArg Subtype.val h),
      φ.subgroupMap_surjective (D.subgroupOf K)⟩
  have hDcard : Nat.card ((D.subgroupOf K).map φ) = 27 := by
    rw [← Nat.card_congr
        (MulEquiv.ofBijective (φ.subgroupMap (D.subgroupOf K)) hbijD).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hD]
  have hD3 : ∀ y ∈ (D.subgroupOf K).map φ, y ^ 3 = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    have hd3 : ((d : ↥K) : G) ^ 3 = 1 := h3 d hd
    have hd3' : d ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [← map_pow, hd3', map_one]
  have hDnc : ¬ IsMulCommutative ((D.subgroupOf K).map φ) := by
    intro h
    apply hnc
    exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hDK)
      ((isMulCommutative_map_iff_of_injective φ hφinjD).mp h)
  have hmap' : (Subgroup.normalizer (D.subgroupOf K : Set ↥K)).map φ ≤
      (Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map φ := by
    simpa only [φ, N, π, ψm] using hmap
  rw [hnormD, hnormJ, hJQeq] at hmap'
  exact not_normalizer_le_normalizer_thompsonSubgroup Q' hDQ' hDcard hD3 hDnc hmap'

theorem not_inf_normalizer_le_of_quotient_pCore_two {G : Type} [Group G] [Finite G]
    {K M Q D : Subgroup G}
    (hK : CFSG.Blueprint.LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 3 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q) (hD : Nat.card D = 27)
    (h3 : ∀ x ∈ D, x ^ 3 = 1) (hnc : ¬ IsMulCommutative D)
    (hKM : K ⊓ M ≤ (K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
      CFSG.Open.pCoreOf 2 K) :
    ¬ K ⊓ Subgroup.normalizer (D : Set G) ≤ M := by
  rintro hNM
  obtain ⟨ψ⟩ := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.psp43_equiv_of_lieModel hK
  exact false_of_map_normalizer_le ψ hQ hDQ hD h3 hnc
    (map_normalizer_le_of_le_of_quotient_pCore_two ψ hQ hDQ hNM hKM)

private theorem exists_thompson_transport {G : Type} [Group G] [Finite G]
    {K Q : Subgroup G} (hK : CFSG.Blueprint.LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 3 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) :
    ∃ (φ : ↥K →* PSp43) (Q' : Sylow 3 PSp43),
      (Q' : Subgroup PSp43) = (Q.subgroupOf K).map φ ∧
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ =
        CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) ∧
      (Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map φ =
        Subgroup.normalizer (CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) : Set PSp43) ∧
      φ.ker = CFSG.pCore 2 ↥K ∧
      Function.Injective (φ.comp (Q.subgroupOf K).subtype) := by
  let N : Subgroup ↥K := CFSG.pCore 2 ↥K
  haveI hNnormal : N.Normal := CFSG.pCore_normal
  have hN3 : ¬ 3 ∣ Nat.card N := not_three_dvd_card_pCore_two
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ⟩ := CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.psp43_equiv_of_lieModel hK
  obtain ⟨Qs, hQs⟩ := hQ.exists_sylow_eq_subgroupOf
  have hQK : IsPGroup 3 (Q.subgroupOf K) := hQ.isPGroup.comap_subtype
  let ψm : ↥K ⧸ N →* PSp43 := ψ.toMonoidHom
  have hψinj : Function.Injective ψm := ψ.injective
  have hψsurj : Function.Surjective ψm := ψ.surjective
  let π : ↥K →* ↥K ⧸ N := QuotientGroup.mk' N
  let φ : ↥K →* PSp43 := ψm.comp π
  have hπinj : Function.Injective (π.comp (Q.subgroupOf K).subtype) :=
    CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hN3 hQK
  have hφinjQ : Function.Injective (φ.comp (Q.subgroupOf K).subtype) := by
    intro a b hab
    exact hπinj (hψinj (by simpa only [φ, ψm, MonoidHom.comp_apply] using hab))
  have hnormJ : (Subgroup.normalizer
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map φ =
      Subgroup.normalizer (((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ :
        Set PSp43) :=
    map_normalizer_mk_comp_equiv_eq hN3 ψ
      (hQK.to_le (Subgroup.subgroupOf_mono K (CFSG.ambientMaxCardThompson_le Q)))
  have hker : φ.ker = N := by
    change ((ψ : ↥K ⧸ N →* PSp43).comp π).ker = N
    rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']
  let Q' : Sylow 3 PSp43 :=
    (Sylow.mapSurjective (QuotientGroup.mk'_surjective N) Qs).mapSurjective
      (f := ψm) hψsurj
  have hQ'coe : (Q' : Subgroup PSp43) = (Q.subgroupOf K).map φ := by
    dsimp only [Q']
    rw [Sylow.coe_mapSurjective, Sylow.coe_mapSurjective, ← hQs, Subgroup.map_map]
  have hJQeq : ((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ =
      CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) := by
    have h2 := CFSG.map_ambientMaxCardThompson_of_injective φ (Q.subgroupOf K) hφinjQ
    rw [thompsonSubgroup_subgroupOf_eq hQ.le, h2, hQ'coe]
  rw [hJQeq] at hnormJ
  exact ⟨φ, Q', hQ'coe, hJQeq, hnormJ, hker, hφinjQ⟩

private theorem mem_sup_of_normalizer_transport {G : Type} [Group G] [Finite G]
    {K Q : Subgroup G} {x : G}
    (φ : ↥K →* PSp43) (Q' : Sylow 3 PSp43)
    (hJQeq : ((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ =
      CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43))
    (hnormJ : (Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map
      φ = Subgroup.normalizer (CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) : Set PSp43))
    (hker : φ.ker = CFSG.pCore 2 ↥K) (hJQK : CFSG.Open.thompsonSubgroup Q ≤ K)
    (hxK : x ∈ K)
    (hx'norm : φ ⟨x, hxK⟩ ∈ Subgroup.normalizer
      (CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) : Set PSp43)) :
    x ∈ (K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
      CFSG.Open.pCoreOf 2 K := by
  let N : Subgroup ↥K := CFSG.pCore 2 ↥K
  have hnormJ'' : (Subgroup.normalizer
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map φ =
      Subgroup.normalizer (((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ :
        Set PSp43) := by
    simpa only [← hJQeq] using hnormJ
  rw [← hJQeq] at hx'norm
  have hxKsup : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.normalizer
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K) ⊔ N :=
    mem_sup_normalizer_of_map_normalizer_eq hker hnormJ'' hx'norm
  have hxmem : x ∈ (Subgroup.normalizer
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K) ⊔ N).map K.subtype :=
    Subgroup.mem_map_of_mem K.subtype hxKsup
  have hnormJQ_map : (Subgroup.normalizer
      ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Subgroup ↥K)).map K.subtype =
      K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hJQK, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [Subgroup.map_sup, hnormJQ_map] at hxmem
  exact hxmem

private theorem map_conj_le_thompsonSubgroup_transport {G : Type} [Group G]
    {K Q B : Subgroup G} {x : G} (φ : ↥K →* PSp43) (Q' : Sylow 3 PSp43)
    (hJQeq : ((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ =
      CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43))
    (hBK : B ≤ K) (hxK : x ∈ K)
    (hBxJ : B.map (MulAut.conj x).toMonoidHom ≤ CFSG.Open.thompsonSubgroup Q) :
    ((B.subgroupOf K).map φ).map (MulAut.conj (φ ⟨x, hxK⟩)).toMonoidHom ≤
      CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) := by
  have hcomp : K.subtype.comp (MulAut.conj (⟨x, hxK⟩ : ↥K)).toMonoidHom =
      (MulAut.conj x).toMonoidHom.comp K.subtype := by
    ext y
    simp [MulAut.conj_apply]
  have hBxKJ : (B.subgroupOf K).map (MulAut.conj (⟨x, hxK⟩ : ↥K)).toMonoidHom ≤
      (CFSG.Open.thompsonSubgroup Q).subgroupOf K := by
    change (B.subgroupOf K).map (MulAut.conj (⟨x, hxK⟩ : ↥K)).toMonoidHom ≤
      (CFSG.Open.thompsonSubgroup Q).comap K.subtype
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hBK]
    exact hBxJ
  have h := Subgroup.map_mono (f := φ) hBxKJ
  rw [hJQeq, CFSG.ClassicalInvolution.RouteD.map_map_conj φ ⟨x, hxK⟩
    (B.subgroupOf K)] at h
  exact h

private theorem mem_sup_of_transport {G : Type} [Group G] [Finite G]
    {K Q D B : Subgroup G} {x : G}
    (φ : ↥K →* PSp43) (Q' : Sylow 3 PSp43)
    (hQ'coe : (Q' : Subgroup PSp43) = (Q.subgroupOf K).map φ)
    (hJQeq : ((CFSG.Open.thompsonSubgroup Q).subgroupOf K).map φ =
      CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43))
    (hnormJ : (Subgroup.normalizer ((CFSG.Open.thompsonSubgroup Q).subgroupOf K : Set ↥K)).map
      φ = Subgroup.normalizer (CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) : Set PSp43))
    (hker : φ.ker = CFSG.pCore 2 ↥K)
    (hφinjQ : Function.Injective (φ.comp (Q.subgroupOf K).subtype))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q) (hD : Nat.card D = 27)
    (h3 : ∀ y ∈ D, y ^ 3 = 1) (hnc : ¬ IsMulCommutative D)
    (hB : B ≤ CFSG.Open.thompsonSubgroup Q ⊓ D) (hBZ : ¬ B ≤ CFSG.centerIn D)
    (hxK : x ∈ K) (hxD : x ∈ Subgroup.normalizer (D : Set G))
    (hBxJ : B.map (MulAut.conj x).toMonoidHom ≤ CFSG.Open.thompsonSubgroup Q) :
    x ∈ (K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
      CFSG.Open.pCoreOf 2 K := by
  let N : Subgroup ↥K := CFSG.pCore 2 ↥K
  have hDK : D ≤ K := hDQ.trans hQ.le
  have hJQK : CFSG.Open.thompsonSubgroup Q ≤ K :=
    (CFSG.ambientMaxCardThompson_le Q).trans hQ.le
  have hφinjD : Function.Injective (φ.comp (D.subgroupOf K).subtype) :=
    injective_comp_subtype_of_le (Subgroup.subgroupOf_mono K hDQ) hφinjQ
  have hBK : B ≤ K := (hB.trans inf_le_right).trans hDK
  have hBD : B ≤ D := hB.trans inf_le_right
  have hDQ' : (D.subgroupOf K).map φ ≤ (Q' : Subgroup PSp43) := by
    rw [hQ'coe]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hDQ)
  have hbijD : Function.Bijective (φ.subgroupMap (D.subgroupOf K)) :=
    ⟨fun _ _ h => hφinjD (congrArg Subtype.val h),
      φ.subgroupMap_surjective (D.subgroupOf K)⟩
  have hDcard : Nat.card ((D.subgroupOf K).map φ) = 27 := by
    rw [← Nat.card_congr
        (MulEquiv.ofBijective (φ.subgroupMap (D.subgroupOf K)) hbijD).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hD]
  have hD3 : ∀ y ∈ (D.subgroupOf K).map φ, y ^ 3 = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    have hd3 : ((d : ↥K) : G) ^ 3 = 1 := h3 d hd
    have hd3' : d ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [← map_pow, hd3', map_one]
  have hDnc : ¬ IsMulCommutative ((D.subgroupOf K).map φ) := by
    intro h
    apply hnc
    exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hDK)
      ((isMulCommutative_map_iff_of_injective φ hφinjD).mp h)
  have hB' : (B.subgroupOf K).map φ ≤
      CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) ⊓ (D.subgroupOf K).map φ := by
    refine le_inf ?_ ?_
    · rw [← hJQeq]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono K (hB.trans inf_le_left))
    · exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hBD)
  have hBZ' : ¬ (B.subgroupOf K).map φ ≤ CFSG.centerIn ((D.subgroupOf K).map φ) := by
    intro h
    exact hBZ (le_centerIn_of_subgroupOf_le hBK hBD hDK
      (le_centerIn_of_map_le_centerIn φ (Subgroup.subgroupOf_mono K hBD) hφinjD h))
  have hxK' : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.normalizer (D.subgroupOf K : Set ↥K) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hDK]
    exact hxD
  have hx' : φ ⟨x, hxK⟩ ∈ Subgroup.normalizer ((D.subgroupOf K).map φ : Set PSp43) :=
    Subgroup.le_normalizer_map (f := φ) (H := D.subgroupOf K)
      (Subgroup.mem_map_of_mem φ hxK')
  have hBxJ' := map_conj_le_thompsonSubgroup_transport φ Q' hJQeq hBK hxK hBxJ
  have hx'norm : φ ⟨x, hxK⟩ ∈ Subgroup.normalizer
      (CFSG.Open.thompsonSubgroup (Q' : Subgroup PSp43) : Set PSp43) :=
    mem_normalizer_thompsonSubgroup_of_map_conj_le Q' hDQ' hDcard hD3 hDnc hB' hBZ'
      hx' hBxJ'
  exact mem_sup_of_normalizer_transport φ Q' hJQeq hnormJ hker hJQK hxK hx'norm

private theorem mem_sup_of_map_conj_le_thompsonSubgroup {G : Type} [Group G] [Finite G]
    {K Q D B : Subgroup G} {x : G}
    (hK : CFSG.Blueprint.LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 3 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q) (hD : Nat.card D = 27)
    (h3 : ∀ y ∈ D, y ^ 3 = 1) (hnc : ¬ IsMulCommutative D)
    (hB : B ≤ CFSG.Open.thompsonSubgroup Q ⊓ D) (hBZ : ¬ B ≤ CFSG.centerIn D)
    (hxK : x ∈ K) (hxD : x ∈ Subgroup.normalizer (D : Set G))
    (hBxJ : B.map (MulAut.conj x).toMonoidHom ≤ CFSG.Open.thompsonSubgroup Q) :
    x ∈ (K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
      CFSG.Open.pCoreOf 2 K := by
  obtain ⟨φ, Q', hQ'coe, hJQeq, hnormJ, hker, hφinjQ⟩ := exists_thompson_transport hK hQ
  exact mem_sup_of_transport φ Q' hQ'coe hJQeq hnormJ hker hφinjQ hQ hDQ hD h3 hnc hB hBZ
    hxK hxD hBxJ

theorem thompsonSubgroup_sup_map_conj_eq_of_quotient_pCore_two {G : Type} [Group G] [Finite G]
    {K Q D B : Subgroup G} {x : G}
    (hK : CFSG.Blueprint.LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSp 2 3 1)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K) (hDQ : D ≤ Q) (hD : Nat.card D = 27)
    (h3 : ∀ y ∈ D, y ^ 3 = 1) (hnc : ¬ IsMulCommutative D)
    (hB : B ≤ CFSG.Open.thompsonSubgroup Q ⊓ D) (hBZ : ¬ B ≤ CFSG.centerIn D)
    (hx : x ∈ K ⊓ Subgroup.normalizer (D : Set G))
    (hxA : x ∉ (K ⊓ Subgroup.normalizer (CFSG.Open.thompsonSubgroup Q : Set G)) ⊔
      CFSG.Open.pCoreOf 2 K) :
    CFSG.Open.thompsonSubgroup Q ⊔ B.map (MulAut.conj x).toMonoidHom = Q := by
  have hxK : x ∈ K := hx.1
  have hxD : x ∈ Subgroup.normalizer (D : Set G) := hx.2
  have hBD : B ≤ D := hB.trans inf_le_right
  have hDconj : D.map (MulAut.conj x).toMonoidHom = D :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxD
  have hBxD : B.map (MulAut.conj x).toMonoidHom ≤ D := by
    rw [← hDconj]
    exact Subgroup.map_mono hBD
  have hBxQ : B.map (MulAut.conj x).toMonoidHom ≤ Q := hBxD.trans hDQ
  have hnotBxJ : ¬ B.map (MulAut.conj x).toMonoidHom ≤
      CFSG.Open.thompsonSubgroup Q := by
    intro hBxJ
    exact hxA (mem_sup_of_map_conj_le_thompsonSubgroup hK hQ hDQ hD h3 hnc hB hBZ
      hxK hxD hBxJ)
  have hJQleQ : CFSG.Open.thompsonSubgroup Q ≤ Q :=
    CFSG.ambientMaxCardThompson_le Q
  have hlt : CFSG.Open.thompsonSubgroup Q <
      CFSG.Open.thompsonSubgroup Q ⊔ B.map (MulAut.conj x).toMonoidHom := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    apply hnotBxJ
    rw [heq]
    exact le_sup_right
  obtain ⟨eQ⟩ := nonempty_mulEquiv_W3_of_quotient_pCore_two (Or.inl hK) hQ
  have hQcard : Nat.card Q = 81 := by
    rw [← card_W3]
    exact Nat.card_congr eQ.toEquiv
  have hJQcard : Nat.card (CFSG.Open.thompsonSubgroup Q) = 27 := by
    rw [thompsonSubgroup_eq_baseIn eQ, card_baseIn eQ]
  let S : Subgroup G := CFSG.Open.thompsonSubgroup Q ⊔ B.map (MulAut.conj x).toMonoidHom
  have hsup_le : S ≤ Q := sup_le hJQleQ hBxQ
  have hcard_gt : 27 < Nat.card S := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [hJQcard] at this
  have hcard_dvd : Nat.card S ∣ 81 := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le hsup_le
  have hcard_eq : Nat.card S = 81 := by
    obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow (p := 3) (m := 4) Nat.prime_three).mp (by
      simpa only [show (81 : ℕ) = 3 ^ 4 by norm_num] using hcard_dvd)
    have hk3 : 3 < k := by
      have h27 : 3 ^ 3 < 3 ^ k := by
        rw [← hk]
        simpa only [show (27 : ℕ) = 3 ^ 3 by norm_num] using hcard_gt
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h27
    have hk4' : k = 4 := by omega
    rw [hk, hk4']
    norm_num
  change S = Q
  exact Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hQcard, hcard_eq])

end CFSG.LieType.PSp43Local
