module

public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82
import CFSG.LocalAnalysis.OddStandard.ChildHeHeld

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

theorem fusionZStar_eq_center_of_perfect {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (hO : CFSG.pPrimeCore 2 Q ≤ center Q) : Open.fusionZStar Q = center Q := by
  ext l
  rw [ComponentClassification.GSThmB.OddQuot.mem_fusionZStar_iff]
  constructor
  · intro h
    have hc : (QuotientGroup.mk l : Q ⧸ center Q) ∈ center (Q ⧸ center Q) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
      have h1 : (QuotientGroup.mk' (center Q)) ⁅l, m⁆ = 1 :=
        (QuotientGroup.eq_one_iff _).2 (hO (h m))
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    rw [Group.IsPerfect.center_quotient_center_eq_bot Q, mem_bot] at hc
    exact (QuotientGroup.eq_one_iff l).1 hc
  · intro hl m
    have h1 : ⁅l, m⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hl m).symm
    rw [h1]
    exact one_mem _

section Standard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fusionZStar_eq_center_of_standard (hL : standardComponentIsStandard L) :
    Open.fusionZStar ↥L = center ↥L := by
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hL.1
  have : Group.IsPerfect L := hq.1
  exact fusionZStar_eq_center_of_perfect (Residual.pPrimeCore_le_center_of_quasisimple hq
    (even_iff_two_dvd.1 (even_card_of_standard hL)))

theorem isMTypeSchur_of_multiplier (hL : standardComponentIsStandard L)
    (hev : Even (Nat.card (center L))) {p : ℕ}
    (hlie : ∃ (τ : Assembly.LowTwoRank.StatedLieTag) (n f : ℕ), LieModel (L ⧸ center L) τ n p f)
    (hc : ∀ n r : ℕ, 0 < n → 0 < r →
      (LieModel (L ⧸ center L) .PSL (2 * n) p r ∨ LieModel (L ⧸ center L) .PSU (2 * n) p r) →
      ordProj[2] (Nat.card (center L)) =
        ordProj[2] (Nat.card (Open.griessHopfMultiplier (L ⧸ center L)))) :
    ComponentClassification.HarrisLit.IsMTypeSchur p L := by
  obtain ⟨_, -, -, -, hL2⟩ := exists_intrinsic_twoComponent hL hev
  have key : ∀ (N : Subgroup ↥L) [N.Normal], N = center ↥L →
      ComponentClassification.HarrisLit.IsSimpleChevalleyOver p (↥L ⧸ N) ∧
        Even (Nat.card N) ∧ ∀ n r : ℕ, 0 < n → 0 < r →
          (LieModel (↥L ⧸ N) .PSL (2 * n) p r ∨ LieModel (↥L ⧸ N) .PSU (2 * n) p r) →
          ordProj[2] (Nat.card N) = ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥L ⧸ N))) := by
    intro N _ hN
    subst hN
    exact ⟨hlie, hev, hc⟩
  exact Or.inl ⟨hL2.2.2, key _ (fusionZStar_eq_center_of_standard hL)⟩

end Standard

@[expose] def OddLieThm187bResidualMult : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ((∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) →
      ComponentClassification.OutcomeLocal.UOutcome G) →
    OddLieType (L ⧸ center L) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    ¬ HarrisSolomonFritzScope L →
    (Odd (Nat.card (center L)) ∨
      ∃ p n r : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ 0 < r ∧
        (LieModel (L ⧸ center L) .PSL (2 * n) p r ∨ LieModel (L ⧸ center L) .PSU (2 * n) p r) ∧
        ordProj[2] (Nat.card (center L)) ≠
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (L ⧸ center L)))) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

theorem oddLieThm187bResidual_of_mult (h : OddLieThm187bResidualMult) : OddLieThm187bResidual := by
  intro G _ _ L hS hU hlie h5 h6 hhsf hcase S hcyc
  refine h G L hS hU hlie h5 h6 hhsf ?_ S hcyc
  by_cases hodd : Odd (Nat.card (center L))
  · exact Or.inl hodd
  · refine Or.inr ?_
    have hnot : ∀ p : ℕ, p.Prime → p ≠ 2 →
        ¬ ComponentClassification.HarrisLit.IsMTypeSchur p L :=
      hcase.resolve_left hodd
    obtain ⟨t, n, p, f, hp, hp2, -, hm⟩ := hlie
    by_contra hne
    refine hnot p hp hp2 (isMTypeSchur_of_multiplier hS.standard
      (Nat.not_odd_iff_even.1 hodd) ⟨t, n, f, hm⟩ fun n' r hn hr hmod => ?_)
    by_contra hneq
    exact hne ⟨p, n', r, hp, hp2, hn, hr, hmod, hneq⟩

end CFSG.OddStandard
