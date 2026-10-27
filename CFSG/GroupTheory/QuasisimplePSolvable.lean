module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_18
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGrp
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQHallHigman
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalPComponentCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

variable {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem coprime_card_of_perfect [Group.IsPerfect X] (h : CFSG.HasNormalPComplement p X) :
    Nat.Coprime p (Nat.card X) := by
  obtain ⟨N, hN, hc, hq⟩ := h
  haveI := hN
  rw [CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect N hq,
    Subgroup.card_top] at hc
  exact hc

theorem not_isPSolvable_of_isQuasisimple (hq : CFSG.Open.IsQuasisimple X)
    (hd : p ∣ Nat.card X) : ¬ CFSG.HallHigman.IsPSolvable p X := by
  intro h
  have hp : p.Prime := Fact.out
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  haveI hs := hq.2
  by_cases hZ : p ∣ Nat.card (X ⧸ Subgroup.center X)
  · refine CFSG.LocalAnalysis.RankThreeUC.S15.K421GrpProof.not_isPSolvable_of_simple hs hp hZ
      (fun hcard => ?_) (InnerQ.HallHigman.IsPSolvable.quotient' h _)
    haveI : IsCyclic (X ⧸ Subgroup.center X) := isCyclic_of_prime_card hcard
    have hcomm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center X))
      (by rw [QuotientGroup.ker_mk'])
    obtain ⟨a, b, hab⟩ := exists_pair_ne (X ⧸ Subgroup.center X)
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have h1 : ∀ z : X, (z : X ⧸ Subgroup.center X) = 1 := fun z =>
      (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_center_iff.mpr fun g => hcomm g z)
    rw [h1, h1]
  · obtain ⟨S⟩ : Nonempty (Sylow p X) := inferInstance
    have hSZ : (S : Subgroup X) ≤ Subgroup.center X := by
      intro x hx
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
      have hxk : (x : X ⧸ Subgroup.center X) ^ (p ^ k) = 1 := by
        rw [← QuotientGroup.mk_pow, show x ^ (p ^ k) = 1 by simpa using congrArg Subtype.val hk,
          QuotientGroup.mk_one]
      have hcop : Nat.Coprime (p ^ k) (Nat.card (X ⧸ Subgroup.center X)) :=
        Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hZ)
      have h1 := Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hxk) hcop) (orderOf_dvd_natCard _)
      exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h1)
    have hN : CFSG.HasNormalPComplement p X :=
      CFSG.hasNormalPComplement_of_sylow_le_center_normalizer p S fun x hx =>
        ⟨Subgroup.le_normalizer hx, Subgroup.mem_centralizer_iff.mpr fun y _ =>
          Subgroup.mem_center_iff.mp (hSZ hx) y⟩
    exact hp.coprime_iff_not_dvd.mp (coprime_card_of_perfect hN) hd

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
