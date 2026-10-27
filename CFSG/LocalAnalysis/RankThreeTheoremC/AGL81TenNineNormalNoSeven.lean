module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgRankNormalOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideWreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneHolds
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

namespace TenNineNoSeven

private def c1 : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2
private def c2 : Equiv.Perm (Fin 7) := Equiv.swap 3 4 * Equiv.swap 4 5

private theorem c_facts :
    c1 ∈ alternatingGroup (Fin 7) ∧ c2 ∈ alternatingGroup (Fin 7) ∧ c1 ^ 3 = 1 ∧ c2 ^ 3 = 1 ∧
      c1 ≠ 1 ∧ c2 ≠ 1 ∧ c1 * c2 = c2 * c1 ∧
      ∀ i j : Fin 3, c1 ^ (i : ℕ) = c2 ^ (j : ℕ) → c1 ^ (i : ℕ) = 1 := by
  refine ⟨Equiv.Perm.mem_alternatingGroup.mpr (by decide),
    Equiv.Perm.mem_alternatingGroup.mpr (by decide), ?_⟩
  decide

theorem exists_elemAbelian_nine_alt :
    ∃ E : Subgroup ↥(alternatingGroup (Fin 7)), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  obtain ⟨h1, h2, h13, h23, h11, h21, hc, hij⟩ := c_facts
  set a : ↥(alternatingGroup (Fin 7)) := ⟨c1, h1⟩
  set b : ↥(alternatingGroup (Fin 7)) := ⟨c2, h2⟩
  have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using h13)
  have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using h23)
  have ha1 : a ≠ 1 := fun h => h11 (congrArg Subtype.val h)
  have hb1 : b ≠ 1 := fun h => h21 (congrArg Subtype.val h)
  have hEA : ∀ x : ↥(alternatingGroup (Fin 7)), x ^ 3 = 1 → IsElemAbelian 3 (zpowers x) := by
    intro x hx
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hlt : ∀ (x : ↥(alternatingGroup (Fin 7))), x ^ 3 = 1 → x ≠ 1 → ∀ y ∈ zpowers x,
      ∃ i : Fin 3, y = x ^ (i : ℕ) := by
    intro x hx hx1 y hy
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime hx hx1] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    exact ⟨⟨n, hn⟩, rfl⟩
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    have hab : Commute a b := Subtype.ext hc
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact (hab.zpow_zpow m n).eq
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    obtain ⟨i, rfl⟩ := hlt a ha3 ha1 x hxa
    obtain ⟨j, hj⟩ := hlt b hb3 hb1 _ hxb
    have := hij i j (congrArg Subtype.val hj)
    exact Subtype.ext (by simpa using this)
  obtain ⟨hE, hEcard⟩ := TenTenClaim.elemAbelian_sup_card (hEA a ha3) (hEA b hb3) hcomm hinf
  refine ⟨_, hE, ?_⟩
  rw [hEcard, Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1,
    orderOf_eq_prime hb3 hb1]

theorem exists_elemAbelian_nine_of_alt {Γ : Type} [Group Γ] {B : Subgroup Γ}
    (e : ↥B ≃* alternatingGroup (Fin 7)) :
    ∃ E : Subgroup Γ, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_nine_alt
  refine ⟨(E.map e.symm.toMonoidHom).map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE _) _
  · rw [Subgroup.card_map_of_injective B.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hcard]

end TenNineNoSeven

variable {G : Type} [Group G] [Finite G]

theorem agl81TenNineNormal_of_pRank_nx_noTenSeven (hNX3 : D1NoXBlock3 G)
    (h98 : AGL81NineEightFour G) (hE : Asc81bASevenPLRankNX) (hS : Setting G) {p : ℕ}
    {P : Sylow p G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hd : AGL81CfgData p P M H Q K) (hr : Open.pRank 3 (H ⊓ M) ≤ 3) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (he : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7))) : (L.subgroupOf M).Normal := by
  obtain ⟨e⟩ := he
  have hNX := noXBlockFor_of_setting hNX3 hS
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hLM : L ≤ M := hL.le
  rw [normal_subgroupOf_iff_le_normalizer hLM]
  intro m hm
  rw [mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set L' := L.map (MulAut.conj m).toMonoidHom with hL'def
  have hL'2 : IsTwoPrimeComponent M L' := hL.toIsTwoPrimeComponent.map_conj hm
  have hLX : ¬ InClassXBlock L := fun h =>
    hNX M L hT.toTwoLocalPair.maxTwoLocal_M hLM hL.subnormal h
  set mbar := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m, hm⟩
  have hbar' : barM M L' = (barM M L).map (MulAut.conj mbar).toMonoidHom := barM_map_conj hm L
  have e' : ↥(barM M L') ≃* alternatingGroup (Fin 7) :=
    ((MulEquiv.subgroupCongr hbar').trans
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj mbar).injective).symm).trans e
  obtain ⟨E, hEP, hEel, hEc⟩ := hE G M (pCoreOf 2 H) L hK hA hL hLX ⟨e⟩
  obtain ⟨E', hEP', hEel', hEc'⟩ : ∃ E' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E' ≤ barM M (normalizer (pCoreOf 2 H : Set G) ⊓ L') ∧ IsElemAbelian 3 E' ∧
        Nat.card E' = 9 := by
    by_cases hL'H : L' ≤ normalizer (pCoreOf 2 H : Set G)
    · rw [inf_eq_right.mpr hL'H]
      exact TenNineNoSeven.exists_elemAbelian_nine_of_alt e'
    · have hL' : IsWeakSBlock M (pCoreOf 2 H) L' := ⟨hL'2, hL'H⟩
      have hL'X : ¬ InClassXBlock L' := fun h =>
        hNX M L' hT.toTwoLocalPair.maxTwoLocal_M hL'2.le hL'2.subnormal h
      exact hE G M (pCoreOf 2 H) L' hK hA hL' hL'X ⟨e'⟩
  have hsub : ∀ X : Subgroup G, barM M (normalizer (pCoreOf 2 H : Set G) ⊓ X) ≤ barM M X ∧
      barM M (normalizer (pCoreOf 2 H : Set G) ⊓ X) ≤ barM M (H ⊓ M) := fun X =>
    ⟨map_mono fun y hy => by
      rw [mem_subgroupOf] at hy ⊢
      exact hy.2,
    map_mono fun y hy => by
      rw [mem_subgroupOf] at hy ⊢
      exact ⟨hNH ▸ hy.1, y.2⟩⟩
  have hLL' : L ≠ L' := fun h => hne h.symm
  have hcomm : ∀ x ∈ E, ∀ y ∈ E', Commute x y := fun x hx y hy =>
    hL.toIsTwoPrimeComponent.commute_of_mem_barM hL'2 hLL' ((hsub L).1 (hEP hx))
      ((hsub L').1 (hEP' hy))
  have hcen := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
    (by norm_num : 4 ≤ 7) e
  have hdisj : ∀ x ∈ E, x ∈ E' → x = 1 := by
    intro x hx hx'
    have hxL : x ∈ barM M L := (hsub L).1 (hEP hx)
    have hxL' : x ∈ barM M L' := (hsub L').1 (hEP' hx')
    have hz : (⟨x, hxL⟩ : barM M L) ∈ Subgroup.center (barM M L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hL.toIsTwoPrimeComponent.commute_of_mem_barM hL'2 hLL' g.2 hxL').eq
    rw [hcen] at hz
    exact congrArg Subtype.val ((Subgroup.mem_bot).mp hz)
  have h4 := four_le_pRank_of_commute ((hsub L).2.trans' hEP) ((hsub L').2.trans' hEP') hEel hEel'
    hEc hEc' hcomm hdisj
  have h4' := h4.trans (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)
  omega


theorem agl81TenNineNormalCfg_of_nx_noTenSeven (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G)
    (hRk : AGL81TenNineRankCfg G) (hE : Asc81bASevenPLRankNX) : AGL81TenNineNormalCfg G :=
  fun hS p P M H Q K hd hp3 _ hL he =>
    agl81TenNineNormal_of_pRank_nx_noTenSeven hNX3 h98 hE hS hd (hRk hS p P M H Q K hd hp3) hL he

theorem agl81TenNineOneThreeNormCfg_of_noTenSeven (hNX3 : D1NoXBlock3 G)
    (h98 : AGL81NineEightFour G) (hE : Asc81bASevenPLRankNX) : AGL81TenNineOneThreeNormCfg G := by
  intro hS P M H Q K hd L hL he
  have hN := agl81TenNineNormal_of_pRank_nx_noTenSeven hNX3 h98 hE hS hd
    (pRank_three_inf_le_of_cfg hS hd) hL he
  exact inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).1 hN)

theorem agl81TenNineOneCfg_of_kfacts_cert_nx_noTenSeven
    (hNX3 : D1NoXBlock3 G)
    (h98 : AGL81NineEightFour G) (hX : AGL81NineThreeXCfg G) (hRk : AGL81TenNineRankCfg G)
    (hE : Asc81bASevenPLRankNX) (h3 : AGL81TenNineOneThreeCfg G)
    (h93 : Asc81bNineThree) : AGL81TenNineOneCfg G := fun hS =>
  agl81TenNineOneCfg_of_nx aschbacherLocalCGTBlock_proved (noXBlockFor_of_setting hNX3 hS) h98 hX
    (agl81TenNineNormalCfg_of_nx_noTenSeven hNX3 h98 hRk hE) h3
    (asc81bASevenBlockAutNX_holds (asc81bEightSix_of_bhs bhsLocalCStar_proved) h93
      fun q hv _ => CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_G2_carrier q hv) hS

end CFSG.LocalAnalysis.RankThreeTheoremC
