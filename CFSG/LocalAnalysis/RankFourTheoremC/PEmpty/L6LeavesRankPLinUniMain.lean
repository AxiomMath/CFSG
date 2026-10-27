module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLiftLinUni
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPLinUniUni
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankFourTheoremC (exists_cover_linear exists_cover_unitary
  l212in_projectiveSLEquivStated exists_char_pow_card)

theorem gl83I66TwoLinUni_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) :
    GL83I66TwoLinUni := by
  intro K _ _ f hf hf5 hq _ hZp hLU K' _ φ hsurj hker z hz hS
  haveI := Fact.mk hf
  have hf2 : f ≠ 2 := by omega
  obtain ⟨S, hzS, hcenS⟩ := hS
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    omega
  have hq' : CFSG.Open.IsQuasisimple K := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have key : ∀ (G : Type) [Group G] (π : G →* K) (A : G), A ^ f = 1 → φ (π A) = z →
      ∃ w : K, orderOf w = f ∧ φ w = z := by
    intro G _ π A hA hAz
    refine ⟨π A, orderOf_eq_prime (by rw [← map_pow, hA, map_one]) ?_, hAz⟩
    intro h
    rw [h, map_one] at hAz
    exact hz1 hAz.symm
  rcases hLU with ⟨n, F, _, _, hfn, hfF, ⟨e⟩⟩ | ⟨n, q, F, _, _, hFq, hfn, hfq, ⟨e⟩⟩
  ·
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · haveI := hq.2.1
        haveI : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 F)) := inferInstance
        exact absurd e.injective.subsingleton (not_subsingleton _)
      · exact h
    have hn5 : 5 ≤ n := hf5.trans (Nat.le_of_dvd hn0 hfn)
    let e' : K ⧸ center K ≃* LinearFlag.projectiveSL n F :=
      e.trans (l212in_projectiveSLEquivStated n F).symm
    obtain ⟨π, hπs, hπ⟩ := exists_cover_linear hf hf5 hGA hq' hZp (by omega) e'
    have hψker : ∀ s, (φ.comp π) s = 1 ↔ s ∈ LinearFlag.scalars n F := by
      intro s
      change φ (π s) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hker, ← QuotientGroup.eq_one_iff, ← e'.map_eq_one_iff, hπ,
        LinearFlag.proj_eq_one_iff]
    obtain ⟨A, hA, hAz⟩ := LU.exists_lift_linear hf2 hfn (by omega) hfF (φ.comp π)
      (hsurj.comp hπs) hψker hz S hzS hcenS
    exact key _ π A hA hAz
  ·
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · haveI := hq.2.1
        haveI : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSU 0 q F)) := inferInstance
        exact absurd e.injective.subsingleton (not_subsingleton _)
      · exact h
    have hn5 : 5 ≤ n := hf5.trans (Nat.le_of_dvd hn0 hfn)
    obtain ⟨r, m, hr, hchar, -, hFr⟩ := exists_char_pow_card F
    haveI : Fact r.Prime := ⟨hr⟩
    haveI := hchar
    obtain ⟨f', -, hqf⟩ : ∃ f' ≤ m, q = r ^ f' := by
      refine (Nat.dvd_prime_pow hr).1 ?_
      rw [← hFr, hFq]
      exact dvd_pow_self q two_ne_zero
    subst hqf
    obtain ⟨π, hπs, hπ⟩ := exists_cover_unitary hf hf5 hGA hq' hZp hn5 hFq e
    have hψker : ∀ s : CFSG.Open.StatedSU n (r ^ f') F, (φ.comp π) s = 1 ↔
        (s : GL (Fin n) F) ∈ CFSG.Open.StatedScalars (Fin n) F := by
      intro s
      change φ (π s) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hker, ← QuotientGroup.eq_one_iff, ← e.map_eq_one_iff, hπ,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    obtain ⟨A, hA, hAz⟩ := LU.exists_lift_unitary hf2 hfn (by omega) hFq hfq (φ.comp π)
      (hsurj.comp hπs) hψker hz S hzS hcenS
    exact key _ π A hA hAz

section CertificateInstances

theorem gl83I66TwoLinUni_holds
    : GL83I66TwoLinUni :=
  gl83I66TwoLinUni_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds

end CertificateInstances

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
