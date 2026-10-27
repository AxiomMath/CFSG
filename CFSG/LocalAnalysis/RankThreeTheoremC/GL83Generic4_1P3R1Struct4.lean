module

import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.ABGLocalTools

open scoped IsMulCommutative

theorem r1s_eq_one_of_center_sylow {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (S : Sylow 3 L) (hS : IsMulCommutative (S : Subgroup L)) {z : L} (hz : z ∈ center L)
    (hzS : z ∈ (S : Subgroup L)) : z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := MonoidHom.transfer (MonoidHom.id (S : Subgroup L)) with hV
  have hker : ⊤ ≤ V.ker := by
    have h1 := Abelianization.commutator_subset_ker V
    rwa [Group.IsPerfect.commutator_eq_top] at h1
  have hVz : V z = 1 := MonoidHom.mem_ker.mp (hker (mem_top z))
  have key : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ (S : Subgroup L) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h := mem_center_iff.mp (pow_mem hz k) g₀
    calc g₀⁻¹ * z ^ k * g₀ = g₀⁻¹ * (z ^ k * g₀) := by rw [mul_assoc]
      _ = g₀⁻¹ * (g₀ * z ^ k) := by rw [h]
      _ = z ^ k := by rw [inv_mul_cancel_left]
  have h2 := MonoidHom.transfer_eq_pow (MonoidHom.id (S : Subgroup L)) z key
  rw [← hV, hVz] at h2
  have h3 : z ^ (S : Subgroup L).index = 1 := by
    have := congrArg Subtype.val h2.symm
    simpa using this
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨z, hzS⟩
  have hj' : orderOf z = 3 ^ j := by rwa [← Subgroup.orderOf_coe] at hj
  have hdvd : orderOf z ∣ (S : Subgroup L).index := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (3 ^ j) (S : Subgroup L).index :=
    Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr S.not_dvd_index)
  rw [hj'] at hdvd
  have : 3 ^ j = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  rw [this] at hj'
  exact orderOf_eq_one_iff.mp hj'

theorem r1s_center_eq_bot {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hL : ∀ T : Sylow 3 L, IsMulCommutative (T : Subgroup L) ∧ centralizer (T : Set L) ≤ T) :
    center L = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 L) := inferInstance
  refine eq_bot_iff.mpr fun z hz => ?_
  have hzT : z ∈ (T : Subgroup L) :=
    (hL T).2 (mem_centralizer_iff.mpr fun h _ => mem_center_iff.mp hz h)
  exact mem_bot.mpr (r1s_eq_one_of_center_sylow T (hL T).1 hz hzT)

theorem r1s_isElemAbelian_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    {E : Subgroup X} (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem r1s_inf_centralizer_eq_bot {Y : Type*} [Group Y] [Finite Y] {Lb D : Subgroup Y}
    [Group.IsPerfect Lb] (hD : D = centralizer (Lb : Set Y))
    (hL : ∀ T : Sylow 3 Lb, IsMulCommutative (T : Subgroup Lb) ∧ centralizer (T : Set Lb) ≤ T) :
    Lb ⊓ D = ⊥ := by
  have hZ : center Lb = ⊥ := r1s_center_eq_bot hL
  refine eq_bot_iff.mpr fun c hc => ?_
  have hcD : c ∈ centralizer (Lb : Set Y) := by rw [← hD]; exact hc.2
  have h1 : (⟨c, hc.1⟩ : Lb) ∈ center Lb :=
    mem_center_iff.mpr fun l => Subtype.ext (mem_centralizer_iff.mp hcD l l.2)
  rw [hZ, mem_bot] at h1
  exact mem_bot.mpr (congrArg Subtype.val h1)

theorem r1s_sylow_centralizer_cyclic {Y : Type} [Group Y] [Finite Y] {S : Sylow 3 Y}
    (hrk : CFSG.Open.pRank 3 (S : Subgroup Y) ≤ 3) {Lb D : Subgroup Y} [Lb.Normal]
    [Group.IsPerfect Lb] (hD : D = centralizer (Lb : Set Y))
    (hL : ∀ T : Sylow 3 Lb, IsElemAbelian 3 (T : Subgroup Lb) ∧ Nat.card T = 3 ^ 2 ∧
      centralizer (T : Set Lb) ≤ T)
    (T : Sylow 3 D) : IsCyclic ↥(T : Subgroup D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDn : D.Normal := by rw [hD]; infer_instance
  have hDc : ∀ c ∈ D, ∀ l ∈ Lb, l * c = c * l := fun c hc l hl =>
    mem_centralizer_iff.mp (by rwa [hD] at hc) l hl
  have hLD : Lb ⊓ D = ⊥ :=
    r1s_inf_centralizer_eq_bot hD fun T => ⟨(hL T).1.1, (hL T).2.2⟩
  have hSY : IsSylowOf 3 (S : Subgroup Y) ⊤ := (isSylowOf_iff).mpr
    ⟨le_top, S.isPGroup', by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  have hSL : IsSylowOf 3 ((S : Subgroup Y) ⊓ Lb) Lb :=
    hSY.inf_of_le_normalizer le_top (normalizer_eq_top Lb).ge
  have hSD : IsSylowOf 3 ((S : Subgroup Y) ⊓ D) D :=
    hSY.inf_of_le_normalizer le_top (normalizer_eq_top D).ge
  obtain ⟨Q, hQ⟩ := hSL
  obtain ⟨hQe, hQc, -⟩ := hL Q
  have hE₁ : IsElemAbelian 3 ((S : Subgroup Y) ⊓ Lb) :=
    hQ ▸ r1s_isElemAbelian_map Lb.subtype hQe
  have hE₁c : Nat.card ((S : Subgroup Y) ⊓ Lb : Subgroup Y) = 3 ^ 2 := by
    rw [← hQ, Subgroup.card_map_of_injective Lb.subtype_injective, hQc]
  obtain ⟨Q', hQ'⟩ := hSD
  have hSDc : IsCyclic ↥((S : Subgroup Y) ⊓ D) := by
    by_contra hnc
    have h2 := two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num)
      S.isPGroup'.to_inf_left hnc
    obtain ⟨E, hEle, hE, hEc⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three ((S : Subgroup Y) ⊓ D)
    have hsum := add_le_pRank_of_commute (P := (S : Subgroup Y)) hE₁ hE hE₁c hEc
      (fun a ha b hb => hDc b (hEle hb).2 a ha.2)
      (by
        rw [disjoint_iff, eq_bot_iff]
        intro c hc
        have : c ∈ Lb ⊓ D := ⟨hc.1.2, (hEle hc.2).2⟩
        rwa [hLD] at this)
      inf_le_left (hEle.trans inf_le_left)
    omega
  have hcQ' : IsCyclic ↥(Q' : Subgroup D) := by
    let e : ↥(Q' : Subgroup D) ≃* ↥((S : Subgroup Y) ⊓ D) :=
      (Q'.equivMapOfInjective D.subtype D.subtype_injective).trans (MulEquiv.subgroupCongr hQ')
    have := hSDc
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have := hcQ'
  exact isCyclic_of_surjective (Q'.equiv T) (Q'.equiv T).surjective

theorem r1s_isCyclic_quotient {Y : Type*} [Group Y] {Lb D : Subgroup Y} [Lb.Normal]
    [IsCyclic D] (hdec : ∀ y : Y, ∃ ℓ ∈ Lb, ∃ d ∈ D, y = ℓ * d) : IsCyclic (Y ⧸ Lb) := by
  refine isCyclic_of_surjective ((QuotientGroup.mk' Lb).comp D.subtype) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨ℓ, hℓ, d, hd, rfl⟩ := hdec y
  refine ⟨⟨d, hd⟩, ?_⟩
  have h1 : ((ℓ : Y) : Y ⧸ Lb) = 1 := (QuotientGroup.eq_one_iff ℓ).mpr hℓ
  change (QuotientGroup.mk' Lb) d = ((ℓ * d : Y) : Y ⧸ Lb)
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, h1, one_mul]

theorem r1s_not_isCyclic_of_pow_three {Y : Type*} [Group Y] {U : Subgroup Y}
    (hU3 : ∀ u ∈ U, u ^ 3 = 1) (hUc : Nat.card U = 3 ^ 2) : ¬ IsCyclic U := by
  intro h
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (hU3 g g.2))
  rw [hg, hUc] at h1
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
