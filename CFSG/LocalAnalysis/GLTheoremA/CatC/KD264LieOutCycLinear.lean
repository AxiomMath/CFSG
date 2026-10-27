module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCyc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterLinear
public import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange

public section

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL
open CFSG.GorensteinWalter

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem outCycAt_psl2 {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : OutCycAt p (PSL2 K) := by
  classical
  let Ψ : PGammaL2 K ≃* MulAut (PSL2 K) := semilinearEquivAut K
  let φ : (⊤ : Subgroup (MulAut (PSL2 K))) →* (K ≃+* K) :=
    (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)).comp
      (Ψ.symm.toMonoidHom.comp (⊤ : Subgroup (MulAut (PSL2 K))).subtype)
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  refine outCycAt_of_cyclic hp ⊤ (fun α _ => Subgroup.mem_top α) φ ?_
  intro x hx hxp
  have hx' : SemidirectProduct.rightHom (Ψ.symm (x : MulAut (PSL2 K))) = 1 := hx
  have hmem : Ψ.symm (x : MulAut (PSL2 K)) ∈
      (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hx'
  obtain ⟨g, hg⟩ := hmem
  have hdg : (x : MulAut (PSL2 K)) = pglAction K g := by
    have h : (x : MulAut (PSL2 K)) = Ψ (SemidirectProduct.inl g) := by
      rw [hg]
      simp
    rw [h]
    change semilinearAction K (SemidirectProduct.inl g) = pglAction K g
    rw [semilinearAction_inl]
  have hgp : g ^ p = 1 := by
    have h1 : Ψ.symm ((x : MulAut (PSL2 K)) ^ p) = 1 := by
      rw [hxp, map_one]
    rw [map_pow, ← hg, ← map_pow] at h1
    exact SemidirectProduct.inl_injective (by rw [map_one]; exact h1)
  obtain ⟨y, hy⟩ := pgl2_mem_psl2Range_of_pow_odd (K := K) (hp.odd_of_ne_two hp2) hgp
  refine inner_le_innAutDerived (PSL2 K) ⟨y, ?_⟩
  rw [hdg, ← hy, pglAction_toPGL]

theorem isCyclic_semilinearAutGroup_quotient {K : Type} [Field K] [Finite K] {m : ℕ}
    [hN : ((linearAutGroup m K).subgroupOf (semilinearAutGroup m K)).Normal] :
    IsCyclic (↥(semilinearAutGroup m K) ⧸
      (linearAutGroup m K).subgroupOf (semilinearAutGroup m K)) := by
  obtain ⟨g, hgE, hg⟩ : ∃ g ∈ semilinearAutGroup m K,
      ∀ x ∈ semilinearAutGroup m K, ∃ k : ℤ, g ^ k * x ∈ linearAutGroup m K :=
    (standard_outer_quotients (K := K) (n := m)).2.2.2.2.2.1
  let gE : ↥(semilinearAutGroup m K) := ⟨g, hgE⟩
  refine ⟨⟨QuotientGroup.mk gE, fun q => ?_⟩⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := hg x hx
  refine ⟨-k, ?_⟩
  change ((QuotientGroup.mk gE : _ ⧸ _) ^ (-k)) = QuotientGroup.mk _
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa [_root_.zpow_neg] using hk

theorem outCycAt_projectiveSL {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 3 ≤ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : OutCycAt p (projectiveSL m K) := by
  classical
  let E : Subgroup (MulAut (projectiveSL m K)) := semilinearAutGroup m K
  let D : Subgroup (MulAut (projectiveSL m K)) := linearAutGroup m K
  have hDE : D ≤ E := linearAutGroup_le_semilinearAutGroup
  have hDR : D ≤ standardAutGroup m K :=
    hDE.trans semilinearAutGroup_le_standardAutGroup
  have hDnormR : (D.subgroupOf (standardAutGroup m K)).Normal :=
    (standard_outer_quotients (K := K) (n := m)).2.2.1
  have hEnorm : (D.subgroupOf E).Normal := by
    letI := hDnormR
    have hRle : standardAutGroup m K ≤ Subgroup.normalizer D :=
      Subgroup.le_normalizer_of_normal_subgroupOf hDR
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hDE).2
      (semilinearAutGroup_le_standardAutGroup.trans hRle)
  haveI := hEnorm
  haveI : IsCyclic (E ⧸ D.subgroupOf E) :=
    isCyclic_semilinearAutGroup_quotient (K := K) (m := m)
  let φ : E →* (E ⧸ D.subgroupOf E) := QuotientGroup.mk' _
  refine outCycAt_of_cyclic hp E ?_ φ ?_
  · intro α hα
    have hdvd : orderOf α ∣ p := orderOf_dvd_of_pow_eq_one hα
    refine mem_semilinearAutGroup_of_odd hm ?_
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  · intro x hx hxp
    have hxD : (x : MulAut (projectiveSL m K)) ∈ D := by
      have hx' : (QuotientGroup.mk x : E ⧸ D.subgroupOf E) = 1 := hx
      rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx'
    exact mem_innAutDerived_of_mem_linearAutGroup hp hp2 hxp hxD

theorem lieOutCyc_linear : LieOutCyc isLinearIdx := by
  intro d p hp hp2 hpchar hP
  obtain ⟨i, hi⟩ := d
  cases i with
  | A n q =>
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let F := GaloisField q.p q.exponent
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hi).1
    have hn1 : 1 ≤ n := hrange.1
    by_cases hn : n = 1
    · subst hn
      have eModel : (TauCeti.CFSGIndex.lie ⟨.A 1 q, hi⟩).Group ≃* PSL2 F :=
        CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hi
      exact outCycAt_of_mulEquiv eModel.symm (outCycAt_psl2 hp hp2)
    · have hn2 : 2 ≤ n := by omega
      have eModel : (TauCeti.CFSGIndex.lie ⟨.A n q, hi⟩).Group ≃* projectiveSL (n + 1) F :=
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hi).trans
          (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) F)
      exact outCycAt_of_mulEquiv eModel.symm (outCycAt_projectiveSL (by omega) hp hp2)
  | twistedA n q => exact absurd hP (by simp [isLinearIdx])
  | B n q => exact absurd hP (by simp [isLinearIdx])
  | C n q => exact absurd hP (by simp [isLinearIdx])
  | D n q => exact absurd hP (by simp [isLinearIdx])
  | twistedD n q => exact absurd hP (by simp [isLinearIdx])
  | E6 q => exact absurd hP (by simp [isLinearIdx])
  | E7 q => exact absurd hP (by simp [isLinearIdx])
  | E8 q => exact absurd hP (by simp [isLinearIdx])
  | F4 q => exact absurd hP (by simp [isLinearIdx])
  | G2 q => exact absurd hP (by simp [isLinearIdx])
  | twistedE6 q => exact absurd hP (by simp [isLinearIdx])
  | trialityD4 q => exact absurd hP (by simp [isLinearIdx])
  | suzuki k => exact absurd hP (by simp [isLinearIdx])
  | reeG2 k => exact absurd hP (by simp [isLinearIdx])
  | reeF4 k => exact absurd hP (by simp [isLinearIdx])
  | tits => exact absurd hP (by simp [isLinearIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
