module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62PGroupA
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Center
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62PGroupB
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Invariant
public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

variable {H : Type} [Group H] [Finite H]

private theorem isCyclic_subgroupOf_iff' {A C : Subgroup H} (hAC : A ≤ C) :
    IsCyclic ↥(A.subgroupOf C) ↔ IsCyclic ↥A :=
  ⟨fun h => isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAC).surjective,
   fun h => isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAC).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAC).symm.surjective⟩

theorem l62_false_of_two_fixed {S : Sylow 3 H} {x z : H} (hB : L62Bar H S x z)
    (hNC : T29.NoncyclicCentreRank) {C C' : Subgroup H} (hC : IsComponentOf C ⊤)
    (hC' : IsComponentOf C' ⊤) (hne : C ≠ C') (hfix : (S : Subgroup H) ≤ normalizer (C : Set H))
    (hfix' : (S : Subgroup H) ≤ normalizer (C' : Set H)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : IsPGroup 3 (S : Subgroup H) := S.isPGroup'
  have hzmem : ∀ D : Subgroup H, IsComponentOf D ⊤ → (S : Subgroup H) ≤ normalizer (D : Set H) →
      z ∈ D := by
    intro D hD hfixD
    obtain ⟨Q, hQ⟩ := sylow_inf_component S hfixD
    have hnb : (S : Subgroup H) ⊓ D ≠ ⊥ := by
      intro hbot
      have hQb : (Q : Subgroup ↥D) = ⊥ := by
        have h0 : (Q : Subgroup ↥D).map D.subtype = ⊥ := by rw [hQ, hbot]
        exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp h0
      have hidx : ¬ 3 ∣ (Q : Subgroup ↥D).index := Q.not_dvd_index
      rw [hQb, Subgroup.index_bot] at hidx
      exact hidx (three_dvd_card_component hB.core hD)
    have hN : ∀ g ∈ (S : Subgroup H), ∀ n ∈ (S : Subgroup H) ⊓ D,
        g * n * g⁻¹ ∈ (S : Subgroup H) ⊓ D := fun g hg n hn =>
      ⟨(S : Subgroup H).mul_mem ((S : Subgroup H).mul_mem hg hn.1) ((S : Subgroup H).inv_mem hg),
        (mem_normalizer_iff.mp (hfixD hg) n).mp hn.2⟩
    exact (l62_z_mem_of_normal hT hB.z_ne hB.z_pow hB.z_gen inf_le_left hN hnb).2
  have hzC := hzmem C hC hfix
  have hzC' := hzmem C' hC' hfix'
  have hplane : ∀ D D' : Subgroup H, IsComponentOf D ⊤ → IsComponentOf D' ⊤ → D ≠ D' →
      (S : Subgroup H) ≤ normalizer (D : Set H) → z ∈ D → z ∈ D' →
      ∃ V : Subgroup H, V ≤ (S : Subgroup H) ⊓ D ∧ (S : Subgroup H) ≤ normalizer (V : Set H) ∧
        Nat.card V = 3 ^ 2 ∧ (∀ v ∈ V, v ^ 3 = 1) ∧ ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro D D' hD hD' hDD' hfixD hzD hzD'
    have hcent : (⟨z, hzD⟩ : ↥D) ∈ center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact component_commute hD hD' hDD' c.2 hzD'
    have hdvd : 3 ∣ Nat.card ↥(center ↥D) := by
      have h1 : orderOf (⟨(⟨z, hzD⟩ : ↥D), hcent⟩ : ↥(center ↥D)) = 3 :=
        (Subgroup.orderOf_mk _ hcent).trans ((Subgroup.orderOf_mk z hzD).trans
          (orderOf_eq_prime hB.z_pow hB.z_ne))
      exact h1 ▸ orderOf_dvd_natCard _
    have hnc : ¬ IsCyclic ↥((S : Subgroup H) ⊓ D) := by
      intro hcyc
      obtain ⟨Q, hQ⟩ := sylow_inf_component S hfixD
      have hnonab := (GL83.I_6_10_1_proved ↥D hD.2.2 3 Nat.prime_three (by norm_num) hdvd Q).1
      apply hnonab
      have hQc : IsCyclic ↥(Q : Subgroup ↥D) := by
        have e : ↥(Q : Subgroup ↥D) ≃* ↥((Q : Subgroup ↥D).map D.subtype) :=
          (Q : Subgroup ↥D).equivMapOfInjective D.subtype D.subtype_injective
        rw [hQ] at e
        exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      exact ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
    have hTR : (S : Subgroup H) ≤ normalizer (((S : Subgroup H) ⊓ D : Subgroup H) : Set H) :=
      fun g hg => inf_normalizer_le_normalizer_inf ⟨le_normalizer hg, hfixD hg⟩
    exact CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le Nat.prime_three (by norm_num) hT
      inf_le_left hTR hnc
  obtain ⟨V, hVR, hVn, hVc, hVp, hVab⟩ := hplane C C' hC hC' hne hfix hzC hzC'
  obtain ⟨V', hVR', hVn', hVc', hVp', hVab'⟩ := hplane C' C hC' hC hne.symm hfix' hzC' hzC
  have hVT : V ≤ (S : Subgroup H) := hVR.trans inf_le_left
  have hVT' : V' ≤ (S : Subgroup H) := hVR'.trans inf_le_left
  have hVe : IsElemAbelian 3 V := ⟨⟨⟨fun a b => Subtype.ext (hVab a a.2 b b.2)⟩⟩, hVp⟩
  have hVe' : IsElemAbelian 3 V' := ⟨⟨⟨fun a b => Subtype.ext (hVab' a a.2 b b.2)⟩⟩, hVp'⟩
  have hVV' : ∀ a ∈ V, ∀ b ∈ V', a * b = b * a := fun a ha b hb =>
    component_commute hC hC' hne (hVR ha).2 (hVR' hb).2
  have hrank : ∀ E : Subgroup H, E ≤ (S : Subgroup H) → IsElemAbelian 3 E →
      (∀ e ∈ E, e * x = x * e) → Nat.card E ≤ 3 ^ 2 := by
    intro E hET hE hcomm
    obtain ⟨k, hk⟩ := (hT.to_le hET).exists_card_eq
    have hEc : E ≤ centralizer ({x} : Set H) := fun e he =>
      mem_centralizer_singleton_iff.mpr (hcomm e he)
    have hkle : k ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set H)) :=
      CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hEc hE hk
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hkle.trans hB.cent)
  have hcommV : ∀ e ∈ V, x * e * x⁻¹ * e⁻¹ ∈ zpowers z := fun e he =>
    l62_comm_mem_zpowers hT hB.z_mem hB.z_ne hB.z_pow hB.z_central hB.z_gen hVT
      (fun g hg u hu => (mem_normalizer_iff.mp (hVn hg) u).mp hu) hVc x hB.x_mem e he
  have hcommV' : ∀ e ∈ V', x * e * x⁻¹ * e⁻¹ ∈ zpowers z := fun e he =>
    l62_comm_mem_zpowers hT hB.z_mem hB.z_ne hB.z_pow hB.z_central hB.z_gen hVT'
      (fun g hg u hu => (mem_normalizer_iff.mp (hVn' hg) u).mp hu) hVc' x hB.x_mem e he
  have hEe : IsElemAbelian 3 (V ⊔ V') := by
    haveI : CFSG.IsElementaryAbelian 3 V :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 V).2 hVe
    haveI : CFSG.IsElementaryAbelian 3 V' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 V').2 hVe'
    have hle : V' ≤ centralizer (V : Set H) := fun b hb =>
      mem_centralizer_iff.mpr fun a ha => hVV' a ha b hb
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      (CFSG.IsElementaryAbelian.sup_of_le_centralizer hle)
  have hcommE := l62_comm_mem_sup hB.z_central hVT hVT' hcommV hcommV'
  have hEle : Nat.card ↥(V ⊔ V') ≤ 3 ^ 2 :=
    l62_card_le_nine_of_comm hB.x_mem hB.x_pow hB.z_mem hB.z_ne hB.z_pow hB.z_central hrank
      (sup_le hVT hVT') hEe hcommE
  have hVeq : V = V ⊔ V' :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hVc]; exact hEle)
  have hVeq' : V' = V ⊔ V' :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hVc']; exact hEle)
  have hVV : V = V' := hVeq.trans hVeq'.symm
  have hVC : V ≤ C := hVR.trans inf_le_right
  have hVz : V.subgroupOf C ≤ center ↥C := by
    intro a ha
    have haV : (a : H) ∈ V := ha
    have haC' : (a : H) ∈ C' := (hVR' (hVV ▸ haV)).2
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact component_commute hC hC' hne c.2 haC'
  have hZp : IsPGroup 3 ↥(center ↥C) := l62_center_isPGroup hB.core hC
  have hnotcyc : ¬ IsCyclic ↥(center ↥C) := by
    intro hcyc
    have h1 : IsCyclic ↥((V.subgroupOf C).subgroupOf (center ↥C)) := inferInstance
    have h2 : IsCyclic ↥(V.subgroupOf C) :=
      (isCyclic_subgroupOf_iff' hVz).1 h1
    exact CFSG.Goldschmidt.Sec82.not_isCyclic_of_card_sq Nat.prime_three hVc hVp
      ((isCyclic_subgroupOf_iff' hVC).1 h2)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) :=
    hNC ↥C hC.2.2 (hB.catalog.isCatalogGroup_center_quotient hC) hZp hnotcyc
  have hmono : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤
      CFSG.Open.pRank 3 ((⊤ : Subgroup ↥C).map C.subtype) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) C.subtype C.subtype_injective ⊤
  have hmono2 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥C).map C.subtype) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top
  have htop := hB.rank_top
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
