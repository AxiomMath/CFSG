module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowDatum
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardRowCentralizer
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
import CFSG.Timmesfeld.Bridge.SchurNarrowCore

public noncomputable section

open Matrix Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem exists_characteristic_odd_complement_of_standard_row
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hF : 16 ≤ Nat.card F)
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφsurj : Function.Surjective φ)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
    let ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
    let E : Subgroup G :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map ρ
    let J : Subgroup G := E ⊔ Subgroup.zpowers t
    let N : Subgroup G := Subgroup.normalizer (J : Set G)
    let C : Subgroup G := Subgroup.centralizer (J : Set G)
    CFSG.Open.IsElemAbelian 2 J ∧
      Nat.card J = 2 * (Nat.card F) ^ 2 ∧
      CFSG.ABGLocalTools.IsSylowOf 2 J C ∧
      J.subgroupOf C ≤ Subgroup.center C ∧
      ∃ O : Subgroup G,
        O ≤ C ∧
        Odd (Nat.card O) ∧
        (O.subgroupOf C).Characteristic ∧
        N ≤ Subgroup.normalizer (O : Set G) ∧
        O ≤ Subgroup.centralizer (A : Set G) ∧
        J ⊔ O = C ∧ J ⊓ O = ⊥ := by
  classical
  dsimp only
  set E : Subgroup G :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
      (A.subtype.comp φ) with hE
  set J : Subgroup G := E ⊔ Subgroup.zpowers t with hJ
  set N : Subgroup G := Subgroup.normalizer (J : Set G) with hN
  set C : Subgroup G := Subgroup.centralizer (J : Set G) with hC
  obtain ⟨htSyl, -⟩ :=
    exists_seitz_fusion_configuration_of_standard hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  obtain ⟨d, -, -, -, hrad⟩ :=
    exists_datum_with_standard_unipotent_radicals hnonab hF A hA hZ e φ hφsurj hφproj hcyc
      t ht htC
  have hAperfect : Group.IsPerfect A := Group.IsPerfect.mk hA.1.1
  have htsq : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hEea : CFSG.Open.IsElemAbelian 2 E := by
    rw [hE]
    exact hrad.elem₁
  have hEcard : Nat.card E = (Nat.card F) ^ 2 := by
    rw [hE]
    exact hrad.card₁
  have hEA : E ≤ A := by
    rw [hE]
    intro x hx
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (φ u).2
  have ht_comm_E : ∀ a ∈ E, a * t = t * a := by
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp htC) a (hEA ha)
  have ht_comm_E' : t ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ht_comm_E a ha
  have hEcenter : E ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxE : x ∈ E := hx.1
    have hxC : x ∈ Subgroup.centralizer (A : Set G) := hx.2
    have hxA : x ∈ A := hEA hxE
    have hxZ : (⟨x, hxA⟩ : A) ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxC) g g.2
    have hdvd : orderOf (⟨x, hxA⟩ : A) ∣ Nat.card (Subgroup.center A) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center A) hxZ
    have hxodd : Odd (orderOf (⟨x, hxA⟩ : A)) := hZ.of_dvd_nat hdvd
    have hx2A : (⟨x, hxA⟩ : A) ^ 2 = 1 := by
      apply Subtype.ext
      show x ^ 2 = 1
      rw [pow_two]
      exact hEea.mul_self_eq_one hxE
    have hdvd2 : orderOf (⟨x, hxA⟩ : A) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2A
    have hone : (⟨x, hxA⟩ : A) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hxodd
        obtain ⟨k, hk⟩ := hxodd
        omega
    simpa using congrArg Subtype.val hone
  have ht_notE : t ∉ E := by
    intro htE
    have hmem : t ∈ E ⊓ Subgroup.centralizer (A : Set G) := ⟨htE, htC⟩
    rw [hEcenter] at hmem
    have ht1 : t = 1 := Subgroup.mem_bot.mp hmem
    rw [ht1] at ht
    simp at ht
  have hEJ_comm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a t from ht_comm_E a ha) m).eq
  have hJea : CFSG.Open.IsElemAbelian 2 J := by
    rw [hJ]
    exact hEea.sup_of_commute (CFSG.Open.isElemAbelian_zpowers (p := 2) htsq) hEJ_comm
  have hEt_inf : E ⊓ Subgroup.zpowers t = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxE : x ∈ E := hx.1
    have hxt : x ∈ Subgroup.zpowers t := hx.2
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two ht).mp hxt with h1 | h1
    · exact h1
    · rw [h1] at hxE
      exact absurd hxE ht_notE
  have hnormal_zt : Subgroup.zpowers t ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.zpowers_le.mpr ht_comm_E').trans
      (Subgroup.centralizer_le_normalizer (E : Set G))
  have hcardJ : Nat.card J = 2 * (Nat.card F) ^ 2 := by
    rw [hJ,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E
        (Subgroup.zpowers t) hnormal_zt (disjoint_iff.mpr hEt_inf),
      hEcard, Nat.card_zpowers, ht]
    ring
  have hfactor : ∀ b : G, b ∈ C →
      ∃ e ∈ E, ∃ d ∈ Subgroup.centralizer (A : Set G), b = e * d := by
    intro b hb
    have hbE : b ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp hb) x (Subgroup.mem_sup_left hx)
    have hbt : b * t = t * b := by
      have h := (Subgroup.mem_centralizer_iff.mp hb) t
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      exact h.symm
    have hbA : b ∈ Subgroup.normalizer (A : Set G) :=
      hA.mem_normalizer_of_commute (htSyl.le (Subgroup.mem_zpowers t)) ht hbt
    have hbE' : b ∈ Subgroup.centralizer
        (((CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
          (A.subtype.comp φ) : Subgroup G) : Set G) := by
      rw [← hE]
      exact hbE
    obtain ⟨a, ha, k, hk, hbk⟩ :=
      exists_row_mul_centralizer_of_normalizes A hAperfect e φ hφproj b hbA hbE'
    exact ⟨a, by rwa [hE], k, hk, hbk⟩
  have hmax : ∀ R : Subgroup G, J ≤ R → R ≤ C → IsPGroup 2 R → R = J := by
    intro R hJR hRC hRpg
    refine le_antisymm ?_ hJR
    intro r hr
    have hrC : r ∈ C := hRC hr
    obtain ⟨a, ha, d, hdC, hde⟩ := hfactor r hrC
    have haR : a ∈ R := hJR (Subgroup.mem_sup_left ha)
    have hdR : d ∈ R := by
      have hd_eq : d = a⁻¹ * r := by rw [hde]; group
      rw [hd_eq]
      exact mul_mem (inv_mem haR) hr
    have hd_int : d ∈ R ⊓ Subgroup.centralizer (A : Set G) := ⟨hdR, hdC⟩
    have ht_int : t ∈ R ⊓ Subgroup.centralizer (A : Set G) :=
      ⟨hJR (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)), htC⟩
    have hInt_eq : R ⊓ Subgroup.centralizer (A : Set G) = Subgroup.zpowers t :=
      htSyl.eq_of_le (Subgroup.zpowers_le.mpr ht_int) inf_le_right hRpg.to_inf_left
    have hdT : d ∈ Subgroup.zpowers t := by
      rw [← hInt_eq]
      exact hd_int
    rw [hde, hJ]
    exact Subgroup.mul_mem_sup ha hdT
  have hJC : J ≤ C := by
    rw [hC]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hJea.comm hy hx
  have hJpg : IsPGroup 2 J := hJea.isPGroup
  obtain ⟨Q, hQle⟩ := (hJpg.comap_subtype (K := C)).exists_le_sylow
  let P : Subgroup G := (Q : Subgroup C).map C.subtype
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 P C := ⟨Q, rfl⟩
  have hJP : J ≤ P := by
    intro j hj
    exact Subgroup.mem_map.mpr
      ⟨⟨j, hJC hj⟩, hQle (Subgroup.mem_subgroupOf.mpr hj), rfl⟩
  have hPC : P ≤ C := Subgroup.map_subtype_le (Q : Subgroup C)
  have hPJ : P = J := hmax P hJP hPC hP.isPGroup
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 J C := by
    rw [← hPJ]
    exact hP
  have hJcenter : J.subgroupOf C ≤ Subgroup.center C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp y.2)
      (x : G) (Subgroup.mem_subgroupOf.mp hx)).symm
  obtain ⟨Q', hQ'⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hcop : (Nat.card (J.subgroupOf C)).Coprime (J.subgroupOf C).index := by
    rw [← hQ']
    exact Q'.card_coprime_index
  let OC : Subgroup C :=
    CFSG.Semidihedral.centralHallComplement (J.subgroupOf C) hJcenter hcop
  have hOCchar : OC.Characteristic :=
    CFSG.Semidihedral.centralHallComplement_characteristic (J.subgroupOf C) hJcenter hcop
  let O : Subgroup G := OC.map C.subtype
  have hOC : O ≤ C := Subgroup.map_subtype_le OC
  have hOcard : Nat.card O = (J.subgroupOf C).index := by
    change Nat.card (OC.map C.subtype) = (J.subgroupOf C).index
    rw [Subgroup.card_map_of_injective C.subtype_injective,
      CFSG.Semidihedral.centralHallComplement_card (J.subgroupOf C) hJcenter hcop]
  have hindexOdd : Odd ((J.subgroupOf C).index) := by
    have hnd := Q'.not_dvd_index
    rw [hQ'] at hnd
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hnd
  have hOodd : Odd (Nat.card O) := by
    rw [hOcard]
    exact hindexOdd
  have hOsub : O.subgroupOf C = OC := by
    change Subgroup.comap C.subtype (Subgroup.map C.subtype OC) = OC
    exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective OC
  have hOchar : (O.subgroupOf C).Characteristic := by
    rw [hOsub]
    exact hOCchar
  have hJmap : (J.subgroupOf C).map C.subtype = J := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJC]
  have hsup : J ⊔ O = C := by
    have h := congrArg (Subgroup.map C.subtype)
      (CFSG.Semidihedral.centralHallComplement_sup (J.subgroupOf C) hJcenter hcop)
    rw [Subgroup.map_sup, hJmap, Subgroup.map_top, Subgroup.range_subtype] at h
    simpa [O] using h
  have hinf : J ⊓ O = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxJ : x ∈ J := hx.1
    have hxO : x ∈ O := hx.2
    have hxC : x ∈ C := hJC hxJ
    have hxJsub : (⟨x, hxC⟩ : C) ∈ J.subgroupOf C :=
      Subgroup.mem_subgroupOf.mpr hxJ
    have hxOsub : (⟨x, hxC⟩ : C) ∈ OC := by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxO
      have hy_eq : y = ⟨x, hxC⟩ := Subtype.ext hyx
      rwa [hy_eq] at hy
    have hmem : (⟨x, hxC⟩ : C) ∈ (J.subgroupOf C) ⊓ OC := ⟨hxJsub, hxOsub⟩
    rw [CFSG.Semidihedral.centralHallComplement_inf (J.subgroupOf C) hJcenter hcop] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hNleNC : N ≤ Subgroup.normalizer (C : Set G) := by
    rw [hN, hC]
    exact CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup J
  have hNleO : N ≤ Subgroup.normalizer (O : Set G) :=
    hNleNC.trans
      (CFSG.QuasithinUnique.normalizer_le_normalizer_of_characteristic hOC hOchar)
  have hO_le_CA : O ≤ Subgroup.centralizer (A : Set G) := by
    intro o ho
    obtain ⟨a, ha, d, hdC, hode⟩ := hfactor o (hOC ho)
    have ho_pow : o ^ Nat.card O = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact Subgroup.orderOf_dvd_natCard O ho
    have ha2 : a ^ 2 = 1 := by
      rw [pow_two]
      exact hEea.mul_self_eq_one ha
    have ha_m : a ^ Nat.card O = a := by
      obtain ⟨m, hm⟩ := hOodd
      rw [hm, pow_succ, pow_mul, ha2, one_pow, one_mul]
    have hcomm_ad : Commute a d := by
      show a * d = d * a
      exact (Subgroup.mem_centralizer_iff.mp hdC) a (hEA ha)
    have hcalc : a * d ^ Nat.card O = 1 := by
      have h := hcomm_ad.mul_pow (Nat.card O)
      rw [← hode, ho_pow, ha_m] at h
      exact h.symm
    have ha_CA : a ∈ Subgroup.centralizer (A : Set G) := by
      have hdm : d ^ Nat.card O ∈ Subgroup.centralizer (A : Set G) :=
        Subgroup.pow_mem _ hdC _
      rw [eq_inv_of_mul_eq_one_left hcalc]
      exact Subgroup.inv_mem _ hdm
    have ha1 : a = 1 := by
      have hmem : a ∈ E ⊓ Subgroup.centralizer (A : Set G) := ⟨ha, ha_CA⟩
      rw [hEcenter] at hmem
      exact Subgroup.mem_bot.mp hmem
    rw [hode, ha1, one_mul]
    exact hdC
  exact ⟨hJea, hcardJ, hSyl, hJcenter, O, hOC, hOodd, hOchar, hNleO, hO_le_CA, hsup, hinf⟩

end CFSG.ComponentClassification.GS79bSec5

end
