module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamOrthBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamOrthFixed
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.ClassicalInvolution.RouteD.TWYType
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open Polynomial Module QuadraticMap CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus
  CFSG.GroupTheory.WeirSylow

section Setup

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {xe : V ≃ₗ[K] V}

private theorem primaryFactor_cases (hx : OddOrderIsometry Q 3 xe)
    (hΦ : Irreducible (X ^ 2 + X + 1 : K[X])) {k : K[X]}
    (hk : k ∈ primaryFactors xe.toLinearMap) : k = X - 1 ∨ k = X ^ 2 + X + 1 := by
  haveI : Fact (Irreducible k) := ⟨irreducible_of_mem_primaryFactors hk⟩
  have hkmon : k.Monic := monic_of_mem_primaryFactors hk
  have hdvd : k ∣ (X ^ 3 - 1 : K[X]) := hx.dvd_X_pow_sub_one hk
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
  rw [hfac] at hdvd
  have hkirr : Irreducible k := Fact.out
  rcases (hkirr.prime).dvd_or_dvd hdvd with h1 | h2
  · left
    have hX1 : Irreducible (X - 1 : K[X]) := by
      simpa using Polynomial.irreducible_X_sub_C (1 : K)
    exact (eq_of_monic_of_associated hkmon (monic_X_sub_C 1)
      (hkirr.associated_of_dvd hX1 h1)).trans (by simp)
  · right
    exact eq_of_monic_of_associated hkmon (by monicity!) (hkirr.associated_of_dvd hΦ h2)

end Setup


theorem orth_three_L2 {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {a : ProjOrthDerived Q} (ha : orderOf a = 3) {r : ℕ} (hr : Odd r) (hr1 : 1 < r)
    {J₁ J₂ J₃ : Subgroup (ProjOrthDerived Q)}
    (h1 : CFSG.Open.IsComponentOf J₁ (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))))
    (h2 : CFSG.Open.IsComponentOf J₂ (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))))
    (h3 : CFSG.Open.IsComponentOf J₃ (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))))
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃)
    (hL1 : catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r))
    (hL2 : catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r))
    (hL3 : catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r)) :
    finrank K V = 8 ∧ IsPlusType Q ∧ Nat.card K = 2 ^ r := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp3 : 3 ≠ ringChar K := by rw [ringChar.eq K 2]; norm_num
  obtain ⟨x, Rep, hxa, hxp, hx, hRep, hNeq, hcases⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_lift_isComponentOf_centralizer_cases
      hQ hT Nat.prime_three (by norm_num) hp3 ha
  have hcls : ∀ J : Subgroup (ProjOrthDerived Q),
      CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) →
      catalogIs (↥J ⧸ Subgroup.center ↥J) (S10.isL2n r) →
      (J = componentImage Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1) ∧
        (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧
        primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) = 2 ∧
        Nat.card K = 2 ^ r) ∨
      (FixedLayerListed Q (x : V ≃ₗ[K] V) ∧ J ≤ fixedComponentImage Q (x : V ≃ₗ[K] V)) := by
    intro J hJ hL
    rcases hcases J hJ with ⟨h, hhRep, hne1, hq, hJeq⟩ | ⟨hlist, n, C, hsup, -, -, i, hi⟩
    · left
      subst hJeq
      obtain ⟨hΦ, hm2, hcardK⟩ := orth_block_L2 hQ hT hx (hRep.1 hhRep) hne1 hq hr hr1 hL
      subst hΦ
      exact ⟨rfl, hRep.1 hhRep, hm2, hcardK⟩
    · right
      refine ⟨hlist, ?_⟩
      rw [hi, ← hsup]
      exact le_iSup C i
  have finish : ∀ {Jf Jg : Subgroup (ProjOrthDerived Q)},
      CFSG.Open.IsComponentOf Jf (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) →
      CFSG.Open.IsComponentOf Jg (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))) →
      Jf ≤ fixedComponentImage Q (x : V ≃ₗ[K] V) → Jg ≤ fixedComponentImage Q (x : V ≃ₗ[K] V) →
      Jf ≠ Jg → FixedLayerListed Q (x : V ≃ₗ[K] V) →
      ((X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧
        primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) = 2 ∧
        Nat.card K = 2 ^ r) →
      finrank K V = 8 ∧ IsPlusType Q ∧ Nat.card K = 2 ^ r := by
    intro Jf Jg hf hg hfY hgY hfg hlist ⟨hΦmem, hm2, hcardK⟩
    have hΦirr : Irreducible (X ^ 2 + X + 1 : K[X]) := irreducible_of_mem_primaryFactors hΦmem
    haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨hΦirr⟩
    have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
    obtain ⟨hW4, S, hS2, hSs⟩ := split_of_two_components_in_fixedLayer hx hlist.1
      (hNeq ▸ hf) (hNeq ▸ hg) hfY hgY hfg
    obtain ⟨hcompl, horth⟩ := hx.fixed_others
    have hWnd : PolarNondegOn Q (fixedSpace (x : V ≃ₗ[K] V)) :=
      polarNondegOn_fixedSpace hcompl horth hx.regular
    have hRnd : PolarNondegOn Q (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)) :=
      polarNondegOn_othersSpace hcompl horth hx.regular
    have hRΦ : othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1) =
        primaryComponent (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) := by
      have hne1 : (X ^ 2 + X + 1 : K[X]) ≠ X - 1 := by
        intro h
        have h2 := congrArg natDegree h
        rw [hΦdeg] at h2
        have h1 : (X - 1 : K[X]).natDegree = 1 := by
          simpa using Polynomial.natDegree_X_sub_C (1 : K)
        omega
      unfold othersSpace
      apply le_antisymm
      · refine iSup_le fun k => iSup_le fun hk => ?_
        rcases primaryFactor_cases hx hΦirr hk.1 with h | h
        · exact absurd h hk.2.1
        · rw [h]
      · exact le_iSup₂_of_le (X ^ 2 + X + 1) ⟨hΦmem, hne1, by
          rw [reciprocalPolynomial_X_sub_one]; exact hne1⟩ le_rfl
    have hRdim : finrank K (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)) = 2 * 2 := by
      rw [hRΦ, finrank_primaryComponent (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1), hΦdeg]
      have : Module.finrank (AdjoinRoot (X ^ 2 + X + 1 : K[X]))
          (primaryComponent (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1)) = 2 := hm2
      rw [this]
    have hWdim : finrank K (fixedSpace (x : V ≃ₗ[K] V)) = 2 * 2 := hW4
    have hfin : finrank K V = 8 := by
      have := Submodule.finrank_add_eq_of_isCompl hcompl
      omega
    refine ⟨hfin, ?_, hcardK⟩
    have h3q : 3 ∣ Nat.card K + 1 := by
      rw [hcardK]
      exact CFSG.RankThree.PartTwo.Sec8.Item82OneProof.three_dvd_two_pow_add_one_of_odd hr
    have hRinv : ∀ u ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1),
        (x : V ≃ₗ[K] V) u ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1) := by
      intro u hu
      rw [hRΦ] at hu ⊢
      exact apply_mem_primaryComponent (Commute.refl _) hu
    have hRfix : ∀ u ∈ othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1),
        (x : V ≃ₗ[K] V) u = u → u = 0 := fun u hu hyu =>
      (Submodule.disjoint_def.mp hcompl.disjoint) u (mem_fixedSpace.mpr hyu) hu
    have hRplus : IsPlusType (Q.comp (othersSpace (x : V ≃ₗ[K] V).toLinearMap (X - 1)).subtype) :=
      (CFSG.RankThree.PartOne.K159.isPlusType_iff_even_of_fixedFree hx Nat.prime_three
        (by norm_num) h3q 2 _ hRinv hRnd hRfix hRdim).mpr (by decide)
    have hWplus : IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[K] V)).subtype) :=
      ⟨S, by omega, hSs⟩
    have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hcompl horth hWnd
      hRnd (a := 2) (b := 2) (by norm_num) (by norm_num) hWdim hRdim
    exact hiff.mpr ⟨fun _ => hRplus, fun _ => hWplus⟩
  have three_fixed : ¬ (J₁ ≤ fixedComponentImage Q (x : V ≃ₗ[K] V) ∧
      J₂ ≤ fixedComponentImage Q (x : V ≃ₗ[K] V) ∧ J₃ ≤ fixedComponentImage Q (x : V ≃ₗ[K] V) ∧
      FixedLayerListed Q (x : V ≃ₗ[K] V)) := by
    rintro ⟨hy1, hy2, hy3, hlist⟩
    obtain ⟨n, C, -, hn2, hsup, hC, -, -⟩ := hx.fixedLayer_data hlist
    have hCc : ∀ i, CFSG.Open.IsComponentOf (C i) (centralizerImage Q (x : V ≃ₗ[K] V)) := by
      intro i
      obtain ⟨hq, hle, hsub⟩ := hC i
      exact CFSG.Assembly.isComponentOf_iff_open.1
        ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).2
          ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq,
            hsub⟩)
    obtain ⟨i₁, hi₁⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
      C hCc (hNeq ▸ h1) (hsup ▸ hy1)
    obtain ⟨i₂, hi₂⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
      C hCc (hNeq ▸ h2) (hsup ▸ hy2)
    obtain ⟨i₃, hi₃⟩ := CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.exists_eq_of_isComponentOf_le_iSup
      C hCc (hNeq ▸ h3) (hsup ▸ hy3)
    have a1 := i₁.2
    have a2 := i₂.2
    have a3 := i₃.2
    rcases (by omega : i₁.1 = i₂.1 ∨ i₁.1 = i₃.1 ∨ i₂.1 = i₃.1) with h | h | h
    · exact h12 (by rw [← hi₁, ← hi₂, Fin.ext h])
    · exact h13 (by rw [← hi₁, ← hi₃, Fin.ext h])
    · exact h23 (by rw [← hi₂, ← hi₃, Fin.ext h])
  rcases hcls J₁ h1 hL1 with ⟨hb1, hd1⟩ | ⟨hlist1, hy1⟩ <;>
  rcases hcls J₂ h2 hL2 with ⟨hb2, hd2⟩ | ⟨hlist2, hy2⟩ <;>
  rcases hcls J₃ h3 hL3 with ⟨hb3, hd3⟩ | ⟨hlist3, hy3⟩
  · exact absurd (hb1.trans hb2.symm) h12
  · exact absurd (hb1.trans hb2.symm) h12
  · exact absurd (hb1.trans hb3.symm) h13
  · exact finish h2 h3 hy2 hy3 h23 hlist2 hd1
  · exact absurd (hb2.trans hb3.symm) h23
  · exact finish h1 h3 hy1 hy3 h13 hlist1 hd2
  · exact finish h1 h2 hy1 hy2 h12 hlist1 hd3
  · exact absurd ⟨hy1, hy2, hy3, hlist1⟩ three_fixed

end CFSG.LocalAnalysis.GLTheoremA.T1428
