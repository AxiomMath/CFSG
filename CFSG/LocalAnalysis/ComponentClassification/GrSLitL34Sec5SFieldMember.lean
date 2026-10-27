module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem mem_solomonKStar_of_field_mirror
    {G : Type} [Group G] [Finite G] {t : G} {P : Subgroup G}
    (hG : L34BaseSetting G) (ht : orderOf t = 2)
    (hP : FooteLit.IsTwoComponentIn P (centralizer ({t} : Set G)))
    {m : ℕ} (hm : 4 ≤ m)
    (htype : Blueprint.LieModel (P ⧸ Open.fusionZStar P) .PSL 3 2 m)
    (hmax : FooteLit.GSMirrorMaximal P) :
    P ∈ FooteLit.solomonKStar G ∧ 3 ≤ pRank 2 ↥P := by
  obtain ⟨hsF, hnF, -⟩ := GrS5.fstar_facts hG
  have hsol := Foote5.SolMax.isSolomonMaximal_of_gsMirrorMaximal hsF hnF ht hP hmax
  have hrank : ∀ {K : Subgroup G},
      Nonempty (P ⧸ Open.fusionZStar P ≃* K ⧸ Open.fusionZStar K) → 3 ≤ pRank 2 ↥K :=
    fun ⟨e⟩ => three_le_pRank_of_lieModel_fusionZStar (by omega)
      (LieType.CurtisTits.lieModel_of_mulEquiv e htype)
  refine ⟨⟨hsol, hsol.1, fun K hK => ?_⟩, hrank ⟨MulEquiv.refl _⟩⟩
  exact (by norm_num : 2 ≤ 3).trans (hrank (Sol76.nonempty_fusionZStar_equiv_of_reflTransGen hK.2))

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem inf_le_sup_of_sup_eq {K P C : Subgroup G} (hPC : P ≤ C)
    (hsup : P ⊔ FooteLit.oddCoreIn K = K) :
    K ⊓ C ≤ (FooteLit.oddCoreIn K ⊓ C) ⊔ P := by
  have hPK : P ≤ K := hsup ▸ le_sup_left
  have hPn : P ≤ normalizer (FooteLit.oddCoreIn K : Set G) := fun p hp =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 ↥K)
      (le_normalizer (hPK hp))
  intro x hx
  have hxK : x ∈ (P : Set G) * (FooteLit.oddCoreIn K : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right P _ hPn, hsup]
    exact (mem_inf.mp hx).1
  obtain ⟨p, hp, o, ho, rfl⟩ := hxK
  have hoC : o ∈ C := by
    have h := mul_mem (inv_mem (hPC hp)) (mem_inf.mp hx).2
    rwa [inv_mul_cancel_left] at h
  exact mul_mem (mem_sup_right hp) (mem_sup_left (mem_inf.mpr ⟨ho, hoC⟩))

private theorem oddResidualIn_eq_of_fixed {t : G} {P K M : Subgroup G} (ht : orderOf t = 2)
    (hPt : P ≤ centralizer ({t} : Set G))
    (hPp : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hPn : centralizer ({t} : Set G) ≤ normalizer (P : Set G))
    (hK : FooteLit.IsTwoComponentIn K M) (htK : t ∈ coreActionKernel K)
    (hfix : UnbalancedGS.gsFixedLayer K t = P) :
    FooteLit.oddResidualIn (FooteLit.oddCoreIn (centralizer ({t} : Set G)) ⊔
      (K ⊓ centralizer ({t} : Set G))) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  have hKq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K M hK.1).mp hK.2).2.2
  have hsup : P ⊔ FooteLit.oddCoreIn K = K :=
    hfix ▸ gsFixedLayer_sup_map_pPrimeCore ht hKq htK.1 htK.2
  have hPH : P ≤ FooteLit.oddCoreIn C ⊔ (K ⊓ C) :=
    le_sup_of_le_right (le_inf (hsup ▸ le_sup_left) hPt)
  refine le_antisymm ?_ ((FooteLit.oddResidualIn_eq_self_of_isPComponent hPt hPp).symm.le.trans
    (FooteLit.oddResidualIn_mono hPH))
  set A := (FooteLit.oddCoreIn K ⊓ C) ⊔ FooteLit.oddCoreIn C with hA
  have hoddK : Odd (Nat.card ↥(FooteLit.oddCoreIn K ⊓ C)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_dvd_of_le (inf_le_left :
      FooteLit.oddCoreIn K ⊓ C ≤ FooteLit.oddCoreIn K))
    rw [FooteLit.oddCoreIn, Subgroup.card_map_of_injective K.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two (dvd_refl 2) h (pPrimeCore_coprime_card))
  have hoddC : Odd (Nat.card ↥(FooteLit.oddCoreIn C)) := by
    rw [FooteLit.oddCoreIn, Subgroup.card_map_of_injective C.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two (dvd_refl 2) h (pPrimeCore_coprime_card))
  have hAodd : Odd (Nat.card A) := FooteLit.odd_card_sup_of_le_normalizer
    (fun x hx => UnbalancedGS.normalizer_le_normalizer_map_of_characteristic C (pPrimeCore 2 ↥C)
      (le_normalizer (mem_inf.mp hx).2)) hoddK hoddC
  have hAP : A ≤ normalizer (P : Set G) :=
    (sup_le inf_le_right (map_subtype_le _)).trans hPn
  have hHA : FooteLit.oddCoreIn C ⊔ (K ⊓ C) ≤ A ⊔ P := sup_le
    (le_sup_of_le_left le_sup_right)
    ((inf_le_sup_of_sup_eq hPt hsup).trans (sup_le_sup_right le_sup_left P))
  rw [FooteLit.oddResidualIn, closure_le]
  rintro g ⟨hg, hg2⟩
  exact FooteLit.mem_of_two_element_of_mem_sup hAP
    (by rw [FooteLit.oddResidualIn_eq_bot_of_odd hAodd]; exact bot_le) (hHA hg) hg2

private theorem isTwoComponentIn_self {P C : Subgroup G} (hPC : P ≤ C)
    (hP : IsPComponent 2 (P.subgroupOf C)) : FooteLit.IsTwoComponentIn P P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hres, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P C hPC).mp hP
  refine ⟨le_rfl, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P P le_rfl).mpr
    ⟨?_, hres, hq⟩⟩
  rw [subgroupOf_self]
  exact IsSubnormal.top

end Helpers

theorem solomon_member_of_same_field_host
    {G : Type} [Group G] [Finite G] {t : G} {P K M : Subgroup G}
    (hset : L34FieldNormalSetting G t P)
    (hmax : FooteLit.GSMirrorMaximal P)
    (hK : FooteLit.IsTwoComponentIn K M)
    (htK : t ∈ coreActionKernel K)
    (hfix : UnbalancedGS.gsFixedLayer K t = P)
    (htype : Nonempty (P ⧸ Open.fusionZStar P ≃*
      K ⧸ Open.fusionZStar K)) :
    FooteLit.SolomonLt K P ∧ FooteLit.SolomonEquiv P K ∧
      K ∈ FooteLit.solomonKStar G := by
  obtain ⟨hG, ht, hPt, hPp, hPn, m, hm, -, hPL⟩ := hset
  have hP : FooteLit.IsTwoComponentIn P (centralizer ({t} : Set G)) := ⟨hPt, hPp⟩
  have hPN : centralizer ({t} : Set G) ≤ normalizer (P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hPt).mp hPn
  have hPmem := Sol76.isSolomonMember_of_isTwoComponentIn_centralizer ht hP
  have hCT : centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hT2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hTK : zpowers t ≤ coreActionKernel K := zpowers_le.mpr htK
  have hKmem : FooteLit.IsSolomonMember K := by
    refine ⟨UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2, zpowers t, ?_, hT2, hTK, ?_⟩
    · intro h
      rw [zpowers_eq_bot] at h
      rw [h, orderOf_one] at ht
      norm_num at ht
    · rw [hCT, oddResidualIn_eq_of_fixed ht hPt hPp hPN hK htK hfix]
      exact hP
  have hlt : FooteLit.SolomonLt K P := by
    refine ⟨hKmem, hPmem, zpowers t, hT2, hTK, ?_⟩
    have h1 : FooteLit.twoLayerIn (K ⊓ centralizer ({t} : Set G)) = P := hfix
    have h2 : FooteLit.conjClosure P (FooteLit.twoLayerIn (centralizer ({t} : Set G))) = P :=
      le_antisymm (Sol78.conjClosure_le le_rfl ((map_subtype_le _).trans hPN))
        (FooteLit.le_conjClosure P _)
    rw [hCT, h1, h2]
    exact isTwoComponentIn_self hPt hPp
  have heq : FooteLit.SolomonEquiv P K :=
    ⟨hPmem, Relation.ReflTransGen.single ⟨htype, Or.inr hlt⟩⟩
  exact ⟨hlt, heq, Sol76.mem_solomonKStar_of_solomonEquiv
    (mem_solomonKStar_of_field_mirror hG ht hP hm hPL hmax).1 heq⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
