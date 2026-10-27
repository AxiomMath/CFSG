module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Model
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Suz
public import CFSG.Sporadic.Recognition.HeMultiplier
public import Certificates.Certificate15031
public import Certificates.Certificate15033
public import Certificates.Certificate15034
public import Certificates.Certificate15035

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG CFSG.LocalCores Subgroup CF24 CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.Recognition.SuzMultiplier
open scoped commutatorElement

theorem cf24CenterGe :
    CF24cCenterGe := by
  intro L _ _ hLq _ ⟨e⟩ α hα M hMF hMc hM
  have hK : Nat.card (M ⧸ center M) = 20160 := OddStandard.GlueL34.card_eq_of_lieModel_psl34 hM
  obtain ⟨q, -, hqk, hJ⟩ := exists_model e α hα M (CatFactsL4U4.OutInv.fixSub α)
    (fun y => Iff.rfl) hMF hMc hK
  set Q := suzM.subtype.comp q with hQ
  have hQk : Q.ker = center L := by
    rw [← hqk]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hQ, MonoidHom.comp_apply]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hMq : IsQuasisimple M := isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hMF) hMc.1
  have hcen := map_center_eq Q hQk.le hMq
  rintro _ ⟨z, hz, rfl⟩
  have h1 : toMap Q M z ∈ center (M.map Q) := by
    rw [hcen]
    exact mem_map_of_mem _ hz
  have hzJ : Q z ∈ J0 := hJ ▸ mem_map_of_mem Q z.2
  have h2 : Q z = 1 := by
    apply eq_one_of_mem_center_J0 hzJ
    intro h hh
    rw [← hJ] at hh
    exact (congrArg Subtype.val (mem_center_iff.mp h1 ⟨h, hh⟩)).symm
  rw [← hQk]
  exact h2

theorem cf24CenterLe :
    CF24cCenterLe := by
  intro L _ _ hLq hL2 ⟨e⟩ α hα M hMF hMc hM
  have hTab := Certificates.certificate15030
  have hRho0 := Certificates.certificate15031
  have hL0 := Certificates.certificate15033
  have hL1 := Certificates.certificate15034
  have hL2' := Certificates.certificate15035
  have hperf : Group.IsPerfect L := hLq.1
  have hK : Nat.card (M ⧸ center M) = 20160 := OddStandard.GlueL34.card_eq_of_lieModel_psl34 hM
  obtain ⟨q, hqs, hqk, hJ⟩ := exists_model e α hα M (CatFactsL4U4.OutInv.fixSub α)
    (fun y => Iff.rfl) hMF hMc hK
  have h6 : Nat.card (center L) ∣ 6 := by
    have h := Sporadic.Recognition.HeMultiplier.card_center_dvd_griess (S := suzM) hperf
      (e.trans suzEquivM)
    rcases card_griessHopfMultiplier_M hTab hRho0 hL0 hL1 hL2' with h36 | h36 <;> rw [h36] at h
    · exact h.trans (by norm_num)
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hL2.exists_card_eq
  have hZ2 : Nat.card (center L) ≤ 2 := by
    rw [hk] at h6 ⊢
    rcases k with _ | _ | k
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ∣ 6 := (pow_dvd_pow 2 (show 2 ≤ k + 2 by omega)).trans h6
      omega
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  have hzc : (⟨z, hz⟩ : center L) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hcard2 : Nat.card (center L) = 2 := by
    have h1 : 1 < Nat.card (center L) :=
      (Finite.one_lt_card_iff_nontrivial).2 ⟨⟨⟨z, hz⟩, 1, hzc⟩⟩
    omega
  have ht : orderOf z = 2 := by
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : center L)
    rw [hcard2, Subgroup.orderOf_mk] at h
    rcases (Nat.dvd_prime Nat.prime_two).1 h with h' | h'
    · exact absurd (orderOf_eq_one_iff.1 h') hz1
    · exact h'
  have hZt : center L = zpowers z := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 hz) ?_
    rw [Nat.card_zpowers, ht, hcard2]
  set Q := suzM.subtype.comp q with hQ
  obtain ⟨u, hu, hux⟩ : cf24XPerm ∈ M.map Q := hJ ▸ cf24XPerm_mem_J0
  obtain ⟨v, hv, hvy⟩ : cf24YPerm ∈ M.map Q := hJ ▸ cf24YPerm_mem_J0
  have hc := commutator_eq_of_doubleCover hTab hRho0 hL0 hL1 hL2' q hqs ht (hqk.trans hZt)
    hZt.symm.le hux hvy cf24_comm
  have hzM : z ∈ M := by
    rw [← hc, commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hu hv) (M.inv_mem hu)) (M.inv_mem hv)
  refine ⟨⟨z, hzM⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_center_iff]
  intro m
  exact Subtype.ext (mem_center_iff.mp hz m)

end CFSG.ComponentClassification.GSThmB
