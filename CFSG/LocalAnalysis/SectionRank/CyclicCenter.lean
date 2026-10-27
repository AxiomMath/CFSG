module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.SectionRank

open CFSG.Open

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [hp : Fact p.Prime]

omit [Finite L] hp in
theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {E : Subgroup G} (hE : IsElemAbelian p E)
    (H : Subgroup G) : IsElemAbelian p (E.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem exists_elemAbelian_sq_of_dvd_card_center [Group.IsPerfect L] (hp2 : p ≠ 2)
    (hZ : p ∣ Nat.card (Subgroup.center L)) :
    ∃ E : Subgroup L, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) p hZ
  set A : Subgroup L := Subgroup.zpowers (a : L) with hAdef
  have hAZ : A ≤ Subgroup.center L := Subgroup.zpowers_le.2 a.2
  have hAo : orderOf (a : L) = p := by rw [Subgroup.orderOf_coe, ha]
  have hAp : IsPGroup p A := IsPGroup.of_card (by rw [Nat.card_zpowers, hAo, pow_one])
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p L))
  have hAP := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P A hAZ hAp
  have hncyc : ¬ IsCyclic (P : Subgroup L) := by
    intro hcyc
    have : IsMulCommutative (P : Subgroup L) := ⟨⟨fun x y => by
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      obtain ⟨i, rfl⟩ := hg x
      obtain ⟨j, rfl⟩ := hg y
      exact (Commute.zpow_zpow_self g i j).eq⟩⟩
    have hbot : commutator (P : Subgroup L) = ⊥ := commutator_eq_bot (P : Subgroup L)
    have ha' : (a : L) ∈ (commutator (P : Subgroup L)).map (P : Subgroup L).subtype :=
      hAP (Subgroup.mem_zpowers _)
    rw [hbot, Subgroup.map_bot, Subgroup.mem_bot] at ha'
    rw [ha', orderOf_one] at hAo
    exact hp.out.one_lt.ne hAo
  have : Fact (IsPGroup p (P : Subgroup L)) := ⟨P.isPGroup'⟩
  obtain ⟨S, -, hScard, hSe⟩ := CFSG.lemma_4_5_a (R := (P : Subgroup L)) hp2 hncyc
  refine ⟨S.map (P : Subgroup L).subtype, isElemAbelian_map ?_ _, ?_⟩
  · exact (isElementaryAbelian_iff_isElemAbelian p S).1 hSe
  · rw [Subgroup.card_map_of_injective (P : Subgroup L).subtype_injective, hScard]

theorem perfect_cyclic_center_odd_elements [Group.IsPerfect L] (hp2 : p ≠ 2)
    (hpL : p ∣ Nat.card L) :
    (CFSG.pRank p (Subgroup.center L) ≤ 1 →
        ∃ g : L, orderOf g = p ∧ g ∉ Subgroup.center L) ∧
      (p ∣ Nat.card (Subgroup.center L) → 2 ≤ CFSG.pRank p L) := by
  refine ⟨fun hZ => ?_, fun hZ => ?_⟩
  · by_cases hpZ : p ∣ Nat.card (Subgroup.center L)
    · obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_sq_of_dvd_card_center hp2 hpZ
      by_contra hall
      push Not at hall
      have hEZ : E ≤ Subgroup.center L := by
        intro g hg
        by_cases hg1 : g = 1
        · rw [hg1]; exact one_mem _
        · have hgo : orderOf g = p :=
            (hp.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hE.2 g hg))).resolve_left
              (fun h => hg1 (orderOf_eq_one_iff.1 h))
          exact hall g hgo
      have hE' : IsElemAbelian p (E.subgroupOf (Subgroup.center L)) :=
        isElemAbelian_subgroupOf hE _
      have hcard' : Nat.card (E.subgroupOf (Subgroup.center L)) = p ^ 2 := by
        rw [← hcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEZ).toEquiv
      have h3 : 2 ≤ CFSG.pRank p (Subgroup.center L) := by
        rw [pRank_eq_open_pRank_top]
        exact le_pRank hp.out.one_lt le_top hE' hcard'
      omega
    · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L) p hpL
      refine ⟨g, hg, fun hgZ => hpZ ?_⟩
      have := Subgroup.orderOf_dvd_natCard (Subgroup.center L) hgZ
      rwa [hg] at this
  · obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_sq_of_dvd_card_center hp2 hZ
    rw [pRank_eq_open_pRank_top]
    exact le_pRank hp.out.one_lt le_top hE hcard

end CFSG.SectionRank
