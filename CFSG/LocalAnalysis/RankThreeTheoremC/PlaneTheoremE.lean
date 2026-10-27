module

public import CFSG.LocalAnalysis.RankThreeTheoremC.StrongEmbeddingCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gamma_one_le_of_forall_centralizer_le (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {R : Subgroup G} (hRP : R ≤ P)
    (h : ∀ y ∈ R, y ≠ 1 → y ^ p = 1 → centralizer ({y} : Set G) ≤ M) :
    rankThreeGamma 1 p R ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  refine (gamma_le_iff 1 p R M).mpr fun Q hQR hQ1 => ?_
  have hQp : IsPGroup p Q := P.isPGroup'.to_le (hQR.trans hRP)
  by_cases hQc : IsCyclic Q
  · obtain ⟨y, hyQ, hy1, hyp, hNQy⟩ :=
      exists_pow_eq_one_normalizer_le_of_isCyclic hprime hQp hQc hQ1
    exact hNQy.trans (normalizer_zpowers_le_of_centralizer_le hS hU0 hp hM
      (two_le_pRank_inf_centralizer P.isPGroup' (by omega) (hRP (hQR hyQ)) hy1 hyp)
      (h y (hQR hyQ) hy1 hyp))
  · exact normalizer_le_of_le_of_two_le_pRank hS hU0 hp hM hQp ((hQR.trans hRP).trans hPM)
      (two_le_pRank_of_not_isCyclic hprime (sigmaA_odd p hp) hQp hQc)

theorem le_of_two_le_pRank_of_elemAbelian_obstructed (hS : Setting G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hD2three : 3 ∈ rankThreeSigmaA G → ∀ P₃ : Sylow 3 G, IsCoreMaxLocal 3 P₃ M →
      (∀ Q : Subgroup G, Q ≤ P₃ → Q ≠ ⊥ →
          3 ≤ CFSG.Open.pRank 3 (Q ⊔ ((P₃ : Subgroup G) ⊓ centralizer (Q : Set G))) →
          normalizer (Q : Set G) ≤ M) ∧
        (¬ Group.IsSolvable M → rankThreeGamma 1 3 (P₃ : Subgroup G) ≤ M))
    (hbad : ∀ R : Subgroup G, R ≤ P → IsElemAbelian p R → ∀ k : ℕ, 2 ≤ k →
      Nat.card R = p ^ k → ∀ y ∈ R, y ≠ 1 → y ^ p = 1 → ¬ centralizer ({y} : Set G) ≤ M →
        ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → H ≤ M)
    {H : Subgroup G} (hH : IsTwoLocal H) (h2 : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) : H ≤ M := by
  classical
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨R, hRHM, hRe, hRc⟩ := pRank_attained p (H ⊓ M) (by omega)
  have hRp : IsPGroup p R := elementary_isPGroup p R hRe
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM R hRp
    (hRHM.trans inf_le_right)
  set φ := (MulAut.conj (m : G)).toMonoidHom with hφ
  set R' := R.map φ with hR'
  have hR'e : IsElemAbelian p R' :=
    elementary_map_injective p R φ (MulAut.conj (m : G)).injective hRe
  have hR'c : Nat.card R' = p ^ CFSG.Open.pRank p (H ⊓ M) := by
    rw [hR', card_map_of_injective (MulAut.conj (m : G)).injective, hRc]
  have hR'H : R' ≤ H.map φ := map_mono (hRHM.trans inf_le_left)
  have hHM' : H.map φ ≤ M → H ≤ M :=
    (conjugate_subgroup_le_iff_of_conjugator_mem H M (m : G) m.2).1
  have hH' : IsTwoLocal (H.map φ) := by
    obtain ⟨T, hT1, hT2, hTH⟩ := hH
    refine ⟨T.map φ, ?_, hT2.map φ, ?_⟩
    · intro h
      exact hT1 ((map_eq_bot_iff_of_injective (f := φ) T (MulAut.conj (m : G)).injective).mp h)
    · rw [hTH, Subgroup.map_equiv_normalizer_eq]
  apply hHM'
  by_cases hall : ∀ y ∈ R', y ≠ 1 → y ^ p = 1 → centralizer ({y} : Set G) ≤ M
  ·
    have hRnc : ¬ IsCyclic R' := by
      intro hcyclic
      obtain ⟨g, hg⟩ := hcyclic.exists_generator
      have hdvd : p ^ CFSG.Open.pRank p (H ⊓ M) ∣ p := by
        rw [← hR'c, ← orderOf_eq_card_of_forall_mem_zpowers hg]
        exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hR'e.2 g g.2))
      have hle := (Nat.pow_le_pow_right hprime.pos h2).trans (Nat.le_of_dvd hprime.pos hdvd)
      nlinarith [hprime.two_le]
    exact hD2 M hM.1 (fun p' hp' P' hM' => hU0 p' hp' P' M hM') hD2three p hp P hM (H.map φ) R'
      hH' hR'H (hm.trans hPM) (elementary_isPGroup p R' hR'e) hRnc
      (gamma_one_le_of_forall_centralizer_le hS hU0 hp hM hm hall)
  ·
    push Not at hall
    obtain ⟨y, hyR, hy1, hyp, hyM⟩ := hall
    exact hbad R' hm hR'e _ h2 hR'c y hyR hy1 hyp hyM (H.map φ) hH' hR'H

end CFSG.LocalAnalysis.RankThreeTheoremC
