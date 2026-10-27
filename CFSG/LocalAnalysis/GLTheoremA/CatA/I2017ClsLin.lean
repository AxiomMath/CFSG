module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinear
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusLinearTransport
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017Cls

open Polynomial
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (glA)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.RankThree.PartOne.KCPrimary

private theorem eq_one_of_ne_zero_of_card_two {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {r : k} (hr : r ≠ 0) : r = 1 := by
  haveI := Fintype.ofFinite k
  have h := FiniteField.pow_card_sub_one_eq_one r hr
  rw [Fintype.card_eq_nat_card, hk] at h
  simpa using h

private theorem two_eq_zero_of_card_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    (2 : k) = 0 := by
  by_contra h
  have h1 : (1 : k) + 1 = 1 + 0 := by
    rw [one_add_one_eq_two, add_zero]
    exact eq_one_of_ne_zero_of_card_two hk h
  exact one_ne_zero (add_left_cancel h1)

private theorem X_pow_three_sub_one_eq (k : Type) [Field k] :
    (X ^ 3 - C 1 : k[X]) = (X - C 1) * (X ^ 2 + X + 1) := by
  rw [map_one]
  ring

private theorem natDegree_le_two_of_dvd {k : Type} [Field k] {a : k[X]} (ha : Irreducible a)
    (hdvd : a ∣ X ^ 3 - C 1) : a.natDegree ≤ 2 := by
  rw [X_pow_three_sub_one_eq] at hdvd
  have hq : (X ^ 2 + X + 1 : k[X]).natDegree ≤ 2 := by compute_degree
  have hq0 : (X ^ 2 + X + 1 : k[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg (eval 0) h0
    simp at h1
  rcases ha.prime.dvd_or_dvd hdvd with h1 | h2
  · have := natDegree_le_of_dvd h1 (X_sub_C_ne_zero 1)
    rw [natDegree_X_sub_C] at this
    omega
  · have := natDegree_le_of_dvd h2 hq0
    omega

private theorem eq_X_sub_one_of_dvd {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {a : k[X]} (hm : a.Monic) (hd : a.natDegree = 1) (hdvd : a ∣ X ^ 3 - C 1) :
    a = X - C 1 := by
  have ha : a = X - C (-a.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]
    exact hm.eq_X_add_C hd
  have hroot : (X ^ 3 - C 1 : k[X]).IsRoot (-a.coeff 0) := by
    rw [← dvd_iff_isRoot, ← ha]
    exact hdvd
  have hr3 : (-a.coeff 0) ^ 3 = 1 := by
    have h0 := hroot.eq_zero
    rw [eval_sub, eval_pow, eval_X, eval_C] at h0
    exact sub_eq_zero.mp h0
  have hr0 : -a.coeff 0 ≠ 0 := by
    intro h0
    rw [h0] at hr3
    simp at hr3
  calc a = X - C (-a.coeff 0) := ha
    _ = X - C 1 := by rw [eq_one_of_ne_zero_of_card_two hk hr0]

private theorem card_alt_eight' : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 8)
  rw [Nat.card_perm, Nat.card_fin] at h
  have h8 : (8 : ℕ).factorial = 40320 := by decide
  omega

private theorem le_six_of_pow_two_dvd {t : ℕ} (h : 2 ^ t ∣ 20160) : t ≤ 6 := by
  rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at h
  have h64 : 2 ^ t ∣ 2 ^ 6 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_left t (Nat.coprime_two_left.mpr (by norm_num : Odd 315))) h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h64

private theorem card_SL_three_two {E : Type} [Field E] [Fintype E] (hE : Fintype.card E = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) E) = 168 := by
  rw [Matrix.card_SL_field 3, hE, Fin.prod_univ_three]
  norm_num

private theorem card_SL_two_four {E : Type} [Field E] [Fintype E] (hE : Fintype.card E = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) = 60 := by
  rw [Matrix.card_SL_field 2, hE, Fin.prod_univ_two]
  norm_num

private theorem even_of_component_alt_eight {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {N : ℕ} {A : GL (Fin N) k} {c : kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {K : Subgroup (LinearFlag.projectiveSL N k)}
    (hK : CFSG.Open.IsComponentOf K (fixSubgroup (LinearFlag.conjAut N k A)))
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* ↥(alternatingGroup (Fin 8))) : Even N := by
  classical
  have hpk : (3 : k) ≠ 0 := by
    rw [show (3 : k) = 2 + 1 by norm_num, two_eq_zero_of_card_two hk, zero_add]
    exact one_ne_zero
  have hc1 : (c : k) = 1 := eq_one_of_ne_zero_of_card_two hk c.ne_zero
  have hsq := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.squarefree_minpoly_glA hpk hA
  obtain ⟨⟨⟨h, hh⟩, hgood⟩, rfl⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components (p := 3) hpk hA K hK
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite k
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite _
  have hcardE : Nat.card (AdjoinRoot h) = 2 ^ h.natDegree := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hk]
  have hdvd_h : h ∣ X ^ 3 - C 1 := by
    have h3 := CFSG.LocalAnalysis.GLTheoremA.dvd_X_pow_three_sub_C_of_mem_primaryFactors hA hh
    rwa [hc1] at h3
  have hdeg_pos : 0 < h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  have hdeg_le : h.natDegree ≤ 2 := natDegree_le_two_of_dvd (Fact.out : Irreducible h) hdvd_h
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq hh
  have hgood' : 3 ≤ primaryMultiplicity (glA A : Module.End k (Fin N → k)) h ∨
      (2 ≤ primaryMultiplicity (glA A : Module.End k (Fin N → k)) h ∧
        4 ≤ Nat.card (AdjoinRoot h)) := hgood
  generalize hmdef : primaryMultiplicity (glA A : Module.End k (Fin N → k)) h = m at e hgood'
  have hQS : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isQuasisimple_specialFactor hsq hh
        hgood)
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) := hQS.1
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) = ⊤ :=
    Group.isPerfect_def.mp hQS.1
  obtain ⟨f, hfs, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_surjective_ker_le_center_map_proj e
  have hcardQ := Nat.card_congr eK.toEquiv
  rw [card_alt_eight'] at hcardQ
  have hcardSL := Nat.card_congr
    (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hfs hker).toEquiv
  rw [hcardQ] at hcardSL
  have hle : 20160 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) := by
    rw [← hcardSL]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hm1 : 1 ≤ m := by rcases hgood' with h3 | ⟨h2, -⟩ <;> omega
  have hdvd2 :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.pow_dvd_card_centerQuotient_of_surjective_specialLinear
      hm1 (by omega) hcardE f hfs hker hperf
  rw [hcardQ] at hdvd2
  have hbound := le_six_of_pow_two_dvd hdvd2
  rcases (show h.natDegree = 1 ∨ h.natDegree = 2 by omega) with hd1 | hd2
  ·
    have hE2 : Fintype.card (AdjoinRoot h) = 2 := by
      rw [Fintype.card_eq_nat_card, hcardE, hd1, pow_one]
    have hm3 : 3 ≤ m := by
      rcases hgood' with h3 | ⟨-, h4⟩
      · exact h3
      · rw [hcardE, hd1] at h4
        norm_num at h4
    have hm4 : m ≤ 4 := by
      by_contra hc
      have h20 : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
      rw [hd1, one_mul] at hbound
      generalize m * (m - 1) = t at h20 hbound
      omega
    rcases (show m = 3 ∨ m = 4 by omega) with rfl | rfl
    · rw [card_SL_three_two hE2] at hle
      norm_num at hle
    · have hN : Module.finrank k (Fin N → k) = N := Module.finrank_fin_fun k
      rw [← hN, finrank_eq_sum_degree_mul_multiplicity hsq]
      refine Finset.even_sum _ fun a _ => ?_
      by_cases hah : (a : k[X]) = h
      · rw [hah, hmdef]
        exact Even.mul_left ⟨2, rfl⟩ _
      · have ha := a.2
        have hirr := irreducible_of_mem_primaryFactors ha
        have hdvd_a : (a : k[X]) ∣ X ^ 3 - C 1 := by
          have h3 := CFSG.LocalAnalysis.GLTheoremA.dvd_X_pow_three_sub_C_of_mem_primaryFactors hA ha
          rwa [hc1] at h3
        have hle_a := natDegree_le_two_of_dvd hirr hdvd_a
        have hpos_a := hirr.natDegree_pos
        have hne1 : (a : k[X]).natDegree ≠ 1 := by
          intro h1
          apply hah
          rw [eq_X_sub_one_of_dvd hk (monic_of_mem_primaryFactors ha) h1 hdvd_a,
            eq_X_sub_one_of_dvd hk (monic_of_mem_primaryFactors hh) hd1 hdvd_h]
        rw [show (a : k[X]).natDegree = 2 by omega]
        exact even_two.mul_right _
  ·
    exfalso
    have hE4 : Nat.card (AdjoinRoot h) = 4 := by
      rw [hcardE, hd2]
      norm_num
    have hm2 : 2 ≤ m := by rcases hgood' with h3 | ⟨h2, -⟩ <;> omega
    have hm3 : m ≤ 3 := by
      by_contra hc
      have h12 : 4 * 3 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
      rw [hd2] at hbound
      generalize m * (m - 1) = t at h12 hbound
      omega
    rcases (show m = 2 ∨ m = 3 by omega) with rfl | rfl
    · have hE4' : Fintype.card (AdjoinRoot h) = 4 := by
        rw [Fintype.card_eq_nat_card, hE4]
      rw [card_SL_two_four hE4'] at hle
      norm_num at hle
    · exact CFSG.HardMathSupport.Solomon.Coordinator.false_of_projectiveSL_alt_eight hE4
        (((QuotientGroup.quotientMulEquivOfEq
          (LinearFlag.scalars_eq_center 3 (AdjoinRoot h))).trans
          (CFSG.ComponentClassification.PerfectCentralQuotient.equivalence f hfs hker)).trans eK)

theorem linTwoA8_holds : LinTwoA8 := by
  intro n d hd _ _ β hmem hβ3 _ hA8
  classical
  obtain ⟨d₁, hv⟩ := d
  have hd₁ : d₁ = TauCeti.LieTypeIndex.A n gfTwoPP := hd
  subst hd₁
  have hn1 : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have hn2 : 2 ≤ n + 1 := Nat.succ_le_succ hn1
  haveI : Fact gfTwoPP.p.Prime := ⟨gfTwoPP.prime_p⟩
  let k := GaloisField gfTwoPP.p gfTwoPP.exponent
  have hcardk : Nat.card k = 2 := by
    dsimp only [k]
    rw [GaloisField.card _ _ gfTwoPP.exponent_pos.ne']
    rfl
  let eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n gfTwoPP, hv⟩).Group ≃*
      LinearFlag.projectiveSL (n + 1) k :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n gfTwoPP hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) k)
  let β' : MulAut (LinearFlag.projectiveSL (n + 1) k) := eModel.symm.trans (β.trans eModel)
  have hβ'mem : β' ∈ innAutDerived (LinearFlag.projectiveSL (n + 1) k) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr eModel).2 hmem
  have hβ'3 : β' ^ 3 = 1 := by
    have h := map_pow (MulAut.congr eModel) β 3
    rw [hβ3, map_one] at h
    exact h.symm
  obtain ⟨A, hAeq⟩ := LinearFlag.mem_linearAutGroup_iff.1
    (CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived_projectiveSL_le_linearAutGroup
      (m := n + 1) hn2 hβ'mem)
  have hconj3 : LinearFlag.conjAut (n + 1) k (A ^ 3) = 1 := by
    rw [map_pow, hAeq, hβ'3]
  obtain ⟨c, hc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one
      (n := n + 1) hn2 hconj3
  obtain ⟨J, -, hJc, ⟨eJ⟩⟩ := hA8
  have hfix := CFSG.LocalAnalysis.GLTheoremA.map_fixSubgroup eModel β
  have hK : CFSG.Open.IsComponentOf (J.map eModel.toMonoidHom)
      (fixSubgroup (LinearFlag.conjAut (n + 1) k A)) := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map eModel hJc
    rw [hAeq]
    exact hfix ▸ h
  have eJK : ↥J ≃* ↥(J.map eModel.toMonoidHom) :=
    J.equivMapOfInjective eModel.toMonoidHom eModel.injective
  have eK : ↥(J.map eModel.toMonoidHom) ⧸ Subgroup.center ↥(J.map eModel.toMonoidHom) ≃*
      ↥(alternatingGroup (Fin 8)) :=
    (QuotientGroup.congr _ _ eJK (Subgroup.map_center_eq eJK)).symm.trans eJ
  exact even_of_component_alt_eight hcardk hc hK eK

end CFSG.LocalAnalysis.GLTheoremA.I2017Cls

end
