module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi22EvenCoverProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InFixes
public import CFSG.GH74.Generic.GKFBridge

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.RankThree.PerfectCover

theorem u62Cov_oddCore_map_le {K : Type} [Group K] [Finite K] (α : MulAut K) :
    (CFSG.oddCore K).map α.toMonoidHom ≤ CFSG.oddCore K := by
  have hN : ((CFSG.oddCore K).map α.toMonoidHom).Normal :=
    (inferInstance : (CFSG.oddCore K).Normal).map α.toMonoidHom α.surjective
  have hodd' : Odd (Nat.card ((CFSG.oddCore K).map α.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := K)
  exact le_sSup (show (CFSG.oddCore K).map α.toMonoidHom ∈
    {N : Subgroup K | N.Normal ∧ Odd (Nat.card N)} from ⟨hN, hodd'⟩)

theorem u62Cov_lift_of_oddCore (K : Type) [Group K] [Finite K]
    (hcent : CFSG.oddCore K ≤ center K) (hperf : commutator K = ⊤) {n : ℕ}
    (h : InvolutionFixesElem (K ⧸ CFSG.oddCore K) n) : InvolutionFixesElem K n := by
  have hmk : MonoidHom.ker (QuotientGroup.mk' (CFSG.oddCore K) : K →* K ⧸ CFSG.oddCore K) =
      CFSG.oddCore K := QuotientGroup.ker_mk' _
  refine fi24in_involutionFixesElem_of_central_odd (QuotientGroup.mk' (CFSG.oddCore K))
    (QuotientGroup.mk'_surjective _) ?_ ?_ hperf ?_ h
  · intro x hx
    rw [hmk] at hx
    exact hcent hx
  · rw [hmk]
    exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd (G := K)
  · intro α x hx
    rw [hmk] at hx ⊢
    exact u62Cov_oddCore_map_le α (Subgroup.mem_map_of_mem α.toMonoidHom hx)

theorem u62Cov_ker_le_center {K Y : Type} [Group K] [Group Y] (N : Subgroup K) [N.Normal]
    (q : K →* Y) (hN : N ≤ q.ker) (hqk : q.ker ≤ center K) :
    (QuotientGroup.lift N q hN).ker ≤ center (K ⧸ N) := by
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x ∈ center K := hqk (by simpa using hy)
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro z
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx w]

theorem u62Cov_ker_isPGroup {K Y : Type} [Group K] [Finite K] [Group Y] (q : K →* Y)
    (hqk : q.ker ≤ center K) (hO : CFSG.oddCore K ≤ q.ker) :
    IsPGroup 2 (QuotientGroup.lift (CFSG.oddCore K) q hO).ker := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : K ⧸ CFSG.oddCore K)
  have hxZ : x ∈ center K := hqk (by
    rw [MonoidHom.mem_ker, ← QuotientGroup.lift_mk (N := CFSG.oddCore K) (φ := q) (HN := hO) x, hx]
    exact y.2)
  obtain ⟨a, r, hrodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  have hw : orderOf (x ^ 2 ^ a) = r := by
    rw [orderOf_pow' _ (pow_ne_zero a two_ne_zero), hord,
      Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]
  have hcen : zpowers (x ^ 2 ^ a) ≤ center K :=
    (zpowers_le).2 ((center K).pow_mem hxZ _)
  have hnorm : (zpowers (x ^ 2 ^ a)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := Subgroup.mem_center_iff.1 (hcen hn) g
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
    exact hn
  have hodd : Odd (Nat.card (zpowers (x ^ 2 ^ a))) := by
    rw [Nat.card_zpowers, hw]
    exact hrodd
  have hle : zpowers (x ^ 2 ^ a) ≤ CFSG.oddCore K :=
    le_sSup (show zpowers (x ^ 2 ^ a) ∈
      {N : Subgroup K | N.Normal ∧ Odd (Nat.card N)} from ⟨hnorm, hodd⟩)
  have hwO : x ^ 2 ^ a ∈ CFSG.oddCore K := hle (mem_zpowers _)
  have h1 : (QuotientGroup.mk (x ^ 2 ^ a) : K ⧸ CFSG.oddCore K) = 1 :=
    (QuotientGroup.eq_one_iff _).2 hwO
  apply Subtype.ext
  show (y : K ⧸ CFSG.oddCore K) ^ 2 ^ a = 1
  rw [← hx, ← QuotientGroup.mk_pow]
  exact h1

theorem u62Cov_exists_cover {K : Type} [Group K] [Finite K] (hqK : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* (Fi22D ⧸ center Fi22D)) (hevenQ : Even (Nat.card (K ⧸ center K))) :
    ∃ p : (K ⧸ CFSG.oddCore K) →* (Fi22D ⧸ center Fi22D), Function.Surjective p ∧
      p.ker ≤ center (K ⧸ CFSG.oddCore K) ∧ IsPGroup 2 p.ker := by
  have hOZ : CFSG.oddCore K ≤ center K :=
    oddCore_le_center_of_even_quotient hqK hevenQ
  have hqk : (CFSG.GH74.Generic.centralQuotientMap e).ker = center K :=
    CFSG.GH74.Generic.centralQuotientMap_ker e
  have hO : CFSG.oddCore K ≤ (CFSG.GH74.Generic.centralQuotientMap e).ker := hqk ▸ hOZ
  refine ⟨QuotientGroup.lift (CFSG.oddCore K) (CFSG.GH74.Generic.centralQuotientMap e) hO, ?_,
    u62Cov_ker_le_center _ _ hO hqk.le, u62Cov_ker_isPGroup _ hqk.le hO⟩
  intro y
  obtain ⟨x, rfl⟩ := CFSG.GH74.Generic.centralQuotientMap_surjective e y
  exact ⟨QuotientGroup.mk x, rfl⟩

section Final


theorem card_hopfMultiplier_u62 (hGA : CFSG.Open.GriessAllModelsStatement) :
    Nat.card (hopfMultiplier (Fi22D ⧸ center Fi22D)) = 12 := by
  rw [CFSG.GH74.Generic.card_hopfMultiplier_of_griess hGA
    (CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) fi22D_classical)]
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSU 6 2 1 = (3, 1) := by decide
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 6 2 1 = (2, 2) := by decide
  rw [hg, he]
  norm_num

theorem u62Covers_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) :
    U62CoversFixesElem := by
  intro K _ _ hperf hU
  obtain ⟨e⟩ := hU
  have hsimp : IsSimpleGroup (K ⧸ center K) :=
    @MulEquiv.isSimpleGroup _ _ _ _ fi22D_isQuasisimple.2.1 e
  have hnc : ∃ a b : K ⧸ center K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := fi22D_isQuasisimple.2.2
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hqK : CFSG.IsQuasisimple K := ⟨hperf, hsimp, hnc⟩
  have hevenQ : Even (Nat.card (K ⧸ center K)) := by
    rw [Nat.card_congr e.toEquiv, fi22D_card_quotient]
    exact ⟨4598415360, by norm_num⟩
  have hOZ : CFSG.oddCore K ≤ center K := oddCore_le_center_of_even_quotient hqK hevenQ
  obtain ⟨p, hps, hpc, hp2⟩ := u62Cov_exists_cover hqK e hevenQ
  obtain ⟨p₀, hp₀s, hp₀k, hp₀c, hBperf⟩ := exists_lvlTwo_cover
  haveI : Group.IsPerfect Fi22D := fi22D_isQuasisimple.1
  haveI : Group.IsPerfect K := hperf
  have hY : center (Fi22D ⧸ center Fi22D) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot Fi22D
  have hKbar : Group.IsPerfect (K ⧸ CFSG.oddCore K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.oddCore K))
  have h12 := card_hopfMultiplier_u62 hGA
  have hfix : InvolutionFixesElem (K ⧸ CFSG.oddCore K) 16 :=
    involutionFixesElem_of_cover hBperf hKbar hY p₀ hp₀s hp₀k p hps hpc hp2 3 (by decide)
      (by rw [h12, hp₀c]) hp₀c involutionFixesElem_lvl_two
  exact u62Cov_lift_of_oddCore K hOZ (Group.isPerfect_def.1 hperf) hfix

end Final

end CFSG.EvenSporadicStandard.Induction.Fi
