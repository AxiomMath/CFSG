module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22EvenCoverProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InFixes

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.EvenSporadicStandard.Solomon78

theorem fi22Quot_exists_ne_comm {Q : Type} [Group Q] (hs : IsSimpleGroup Q)
    (hc : Nat.card Q = 64561751654400) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup Q := { ‹Group Q› with mul_comm := h }
  have hp : (Nat.card Q).Prime := CommGroup.is_simple_iff_prime_card.1 hs
  rw [hc] at hp
  have h2 := hp.eq_one_or_self_of_dvd 2 (by norm_num)
  omega

theorem fi22Cov_center_char {K : Type} [Group K] (α : MulAut K) {x : K}
    (hx : x ∈ Subgroup.center K) : α x ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := Subgroup.mem_center_iff.1 hx (α.symm g)
  calc g * α x = α (α.symm g * x) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = α (x * α.symm g) := by rw [h1]
    _ = α x * g := by rw [map_mul, MulEquiv.apply_symm_apply]

theorem fi22Cov_oddCore_map_le {K : Type} [Group K] [Finite K] (α : MulAut K) :
    (CFSG.oddCore K).map α.toMonoidHom ≤ CFSG.oddCore K := by
  have hN : ((CFSG.oddCore K).map α.toMonoidHom).Normal :=
    (inferInstance : (CFSG.oddCore K).Normal).map α.toMonoidHom α.surjective
  have hodd' : Odd (Nat.card ((CFSG.oddCore K).map α.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]
    have hO : Odd (Nat.card (CFSG.oddCore K)) :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := K)
    exact hO
  exact le_sSup (show (CFSG.oddCore K).map α.toMonoidHom ∈
    {N : Subgroup K | N.Normal ∧ Odd (Nat.card N)} from ⟨hN, hodd'⟩)

theorem fi22Cov_lift_of_quot (K : Type) [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hcent : N ≤ Subgroup.center K) (hodd : Odd (Nat.card N)) (hperf : commutator K = ⊤)
    (hchar : ∀ α : MulAut K, ∀ x ∈ N, α x ∈ N) {n : ℕ} (h : InvolutionFixesElem (K ⧸ N) n) :
    InvolutionFixesElem K n := by
  have hmk : MonoidHom.ker (QuotientGroup.mk' N : K →* K ⧸ N) = N := QuotientGroup.ker_mk' N
  refine CFSG.EvenSporadicStandard.Induction.fi24in_involutionFixesElem_of_central_odd
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) ?_ ?_ hperf ?_ h
  · intro x hx
    rw [hmk] at hx
    exact hcent hx
  · rw [hmk]
    exact hodd
  · intro α x hx
    rw [hmk] at hx ⊢
    exact hchar α x hx

section Covers


theorem fi22Covers_oddCentre : ∀ (K : Type) [Group K] [Finite K], Group.IsPerfect K →
    CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .Fi22 →
    Odd (Nat.card (Subgroup.center K)) → InvolutionFixesElem K 16 := by
  intro K _ _ hq hS hodd
  obtain ⟨e⟩ := hS
  have hD' : InvolutionFixesElem (K ⧸ Subgroup.center K) 16 :=
    CFSG.EvenSporadicStandard.Induction.Fi.involutionFixesElem_of_mulEquiv e.symm
      involutionFixesElem_fi22
  exact fi22Cov_lift_of_quot K (Subgroup.center K) le_rfl hodd (Group.isPerfect_def.1 hq)
    (fun α x hx => fi22Cov_center_char α hx) hD'

theorem fi22Covers_of_fi23D
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hD : CFSG.EvenSporadicStandard.Solomon78.InvolutionFixesElem
      CFSG.EvenSporadicStandard.Induction.Fi.Fi23D 16) :
    CFSG.EvenSporadicStandard.Induction.Fi.Fi22CoversFixesElem := by
  intro K _ _ hq hS
  rcases Nat.even_or_odd (Nat.card (Subgroup.center K)) with heven | hodd
  ·
    obtain ⟨e⟩ := id hS
    have hsimp : IsSimpleGroup (K ⧸ Subgroup.center K) :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e
    have hcardQ : Nat.card (K ⧸ Subgroup.center K) = 64561751654400 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Fi22.card_Fi22
    have hqK : CFSG.IsQuasisimple K :=
      ⟨hq, hsimp, fi22Quot_exists_ne_comm hsimp hcardQ⟩
    have hevenQ : Even (Nat.card (K ⧸ Subgroup.center K)) := by
      rw [hcardQ]
      exact ⟨32280875827200, by norm_num⟩
    have hOZ : CFSG.oddCore K ≤ Subgroup.center K :=
      CFSG.EvenSporadicStandard.Induction.Fi.oddCore_le_center_of_even_quotient hqK hevenQ
    have hOodd : Odd (Nat.card (CFSG.oddCore K)) :=
      CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := K)
    obtain ⟨e'⟩ := CFSG.EvenSporadicStandard.Induction.Fi.fi22EvenCover_proved hSM K hqK hS heven
    have hD' : InvolutionFixesElem (K ⧸ CFSG.oddCore K) 16 :=
      CFSG.EvenSporadicStandard.Induction.Fi.involutionFixesElem_of_mulEquiv e'.symm hD
    exact fi22Cov_lift_of_quot K (CFSG.oddCore K) hOZ hOodd (Group.isPerfect_def.1 hq)
      (fun α x hx => fi22Cov_oddCore_map_le α (Subgroup.mem_map_of_mem α.toMonoidHom hx)) hD'
  ·
    exact fi22Covers_oddCentre K hq hS hodd

end Covers

end CFSG.EvenSporadicStandard.YS14
