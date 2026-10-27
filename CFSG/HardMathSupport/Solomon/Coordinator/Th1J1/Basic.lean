module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple
public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_jOf {S E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian 2 E)
    (hcard : Nat.card E = 2 ^ pRank 2 S) : E ≤ jOf S := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hcard
  exact le_iSup₂_of_le E ⟨hES, hE, hcard⟩ le_rfl

theorem le_jOneOf {S E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian 2 E)
    (hcard : 2 ^ (pRank 2 S - 1) ≤ Nat.card E) : E ≤ jOneOf S := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hcard
  exact le_iSup₂_of_le E ⟨hES, hE, hcard⟩ le_rfl

theorem jOf_le_jOneOf (S : Subgroup G) : jOf S ≤ jOneOf S := by
  refine iSup₂_le fun E hE => ?_
  refine le_jOneOf hE.1 hE.2.1 ?_
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank, hE.2.2]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

omit [Finite G] in
theorem isElemAbelian_omegaOneZ (X : Subgroup G) : IsElemAbelian 2 (omegaOneZ X) := by
  unfold omegaOneZ
  refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ha.2)
  exact (Sec7.mem_centerOf_iff'.1 ha.1).2 b (Sec7.mem_centerOf_iff'.1 hb.1).1

omit [Finite G] in
theorem omegaOneZ_le_centralizer (X : Subgroup G) :
    omegaOneZ X ≤ Subgroup.centralizer (X : Set G) := by
  unfold omegaOneZ
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  refine SetLike.mem_coe.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
  exact ((Sec7.mem_centerOf_iff'.1 hx.1).2 h hh).symm

theorem omegaOneZ_jOneOf_le {S E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian 2 E)
    (hcard : Nat.card E = 2 ^ pRank 2 S) : omegaOneZ (jOneOf S) ≤ E := by
  have hEJ1 : E ≤ jOneOf S := (le_jOf hES hE hcard).trans (jOf_le_jOneOf S)
  have hcomm : ∀ a ∈ omegaOneZ (jOneOf S), ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (omegaOneZ_le_centralizer (jOneOf S) ha) b (hEJ1 hb)).symm
  have hEZ : IsElemAbelian 2 (omegaOneZ (jOneOf S) ⊔ E) :=
    IsElemAbelian.sup_of_commute (isElemAbelian_omegaOneZ (jOneOf S)) hE hcomm
  have hle : omegaOneZ (jOneOf S) ⊔ E ≤ S :=
    sup_le ((Sec7.omegaOneZ_le (jOneOf S)).trans (Sec7.jOneOf_le S)) hES
  obtain ⟨k, hk⟩ := hEZ.isPGroup.exists_card_eq
  have hkS : k ≤ CFSG.Open.pRank 2 S := CFSG.SectionRank.le_pRank Nat.one_lt_two hle hEZ hk
  have hcard_le : Nat.card (omegaOneZ (jOneOf S) ⊔ E : Subgroup G) ≤ Nat.card E := by
    rw [hk, hcard]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hkS
  have heq : E = omegaOneZ (jOneOf S) ⊔ E :=
    Subgroup.eq_of_le_of_card_ge le_sup_right hcard_le
  exact le_sup_left.trans heq.ge

theorem pRank_eq_of_jOf_le {S T : Subgroup G} (hTS : T ≤ S) (hJT : jOf S ≤ T) :
    pRank 2 T = pRank 2 S := by
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank, CFSG.SectionRank.pRank_coe_eq_openPRank]
  refine le_antisymm (CFSG.SectionRank.pRank_mono Nat.one_lt_two hTS) ?_
  obtain ⟨E, hES, hE, hcard⟩ := CFSG.SectionRank.exists_pRank Nat.one_lt_two S
  have hcard' : Nat.card E = 2 ^ pRank 2 S := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hcard
  exact CFSG.SectionRank.le_pRank Nat.one_lt_two ((le_jOf hES hE hcard').trans hJT) hE hcard

theorem jOf_eq_of_le {S T : Subgroup G} (hTS : T ≤ S) (hJT : jOf S ≤ T) : jOf T = jOf S := by
  have hp : pRank 2 T = pRank 2 S := pRank_eq_of_jOf_le hTS hJT
  refine le_antisymm (iSup₂_le fun E hE => ?_) (iSup₂_le fun E hE => ?_)
  ·
    have hcT : Nat.card E = 2 ^ pRank 2 T := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact hE.2.2
    exact le_jOf (hE.1.trans hTS) hE.2.1 (hcT.trans (by rw [hp]))
  ·
    have hcS : Nat.card E = 2 ^ pRank 2 S := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact hE.2.2
    have hET : E ≤ T := (le_jOf hE.1 hE.2.1 hcS).trans hJT
    exact le_jOf hET hE.2.1 (hcS.trans (by rw [hp]))

theorem jOneOf_eq_of_le {S T : Subgroup G} (hTS : T ≤ S) (hJT : jOneOf S ≤ T) :
    jOneOf T = jOneOf S := by
  have hp : pRank 2 T = pRank 2 S := pRank_eq_of_jOf_le hTS ((jOf_le_jOneOf S).trans hJT)
  refine le_antisymm (iSup₂_le fun E hE => ?_) (iSup₂_le fun E hE => ?_)
  ·
    have hcT : 2 ^ (pRank 2 T - 1) ≤ Nat.card E := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact hE.2.2
    exact le_jOneOf (hE.1.trans hTS) hE.2.1 (by rw [← hp]; exact hcT)
  ·
    have hcS : 2 ^ (pRank 2 S - 1) ≤ Nat.card E := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact hE.2.2
    have hET : E ≤ T := (le_jOneOf hE.1 hE.2.1 hcS).trans hJT
    exact le_jOneOf hET hE.2.1 (by rw [hp]; exact hcS)

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1
