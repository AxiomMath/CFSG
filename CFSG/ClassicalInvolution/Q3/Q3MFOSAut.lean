module

public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.ClassicalInvolution.Q3.Q3NMClass

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.Classical2
  CFSG.ClassicalInvolution.Q3.Q3NM
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

section Bridge

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem map_matrixDerived_linear :
    (matrixDerived Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom = orthDerived Q := by
  rw [matrixDerived, Subgroup.map_commutator]
  have h : (matrixIsometries Q).map (matrixLinearIso (d := d) (K := K)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [matrixIsometries]
    exact Subgroup.map_comap_eq_self_of_surjective (matrixLinearIso (d := d) (K := K)).surjective _
  rw [h]

@[expose] noncomputable def derivedEquivElem (hE : orthDerived Q = elementaryGroup Q) :
    matrixDerived Q ≃* ↥(elementaryGroup Q) :=
  ((matrixLinearIso (d := d) (K := K)).subgroupMap (matrixDerived Q)).trans
    (MulEquiv.subgroupCongr ((map_matrixDerived_linear Q).trans hE))

theorem coe_derivedEquivElem (hE : orthDerived Q = elementaryGroup Q) (A : matrixDerived Q) :
    ((derivedEquivElem Q hE A : ↥(elementaryGroup Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      matrixLinearEquiv A.1 := rfl

theorem mem_matrixDerivedScalars_iff_mem_scalars (A : matrixDerived Q) :
    A ∈ matrixDerivedScalars Q ↔ matrixLinearEquiv A.1 ∈ scalars K (Fin d → K) :=
  mem_statedScalars_iff A.1

variable [Finite K]

theorem map_scalars_derivedEquivElem (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ d) (hE : orthDerived Q = elementaryGroup Q) :
    (matrixDerivedScalars Q).map (derivedEquivElem Q hE).toMonoidHom =
      Subgroup.center ↥(elementaryGroup Q) := by
  have hdim' : 3 ≤ Module.finrank K (Fin d → K) := by simpa using hdim
  ext x
  rw [mem_center_iff_mem_scalars hK hQ hdim']
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (mem_matrixDerivedScalars_iff_mem_scalars Q A).mp hA
  · intro hx
    refine ⟨(derivedEquivElem Q hE).symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_matrixDerivedScalars_iff_mem_scalars]
    have h1 : ((derivedEquivElem Q hE ((derivedEquivElem Q hE).symm x) : ↥(elementaryGroup Q)) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) = x := by rw [MulEquiv.apply_symm_apply]
    rw [coe_derivedEquivElem] at h1
    rw [h1]
    exact hx

@[expose] noncomputable def centralEquiv (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ d) (hE : orthDerived Q = elementaryGroup Q) :
    matrixProjectiveDerived Q ≃*
      ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q) :=
  QuotientGroup.congr _ _ (derivedEquivElem Q hE) (map_scalars_derivedEquivElem Q hK hQ hdim hE)

theorem centralEquiv_mk (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ d)
    (hE : orthDerived Q = elementaryGroup Q) (A : matrixDerived Q) :
    centralEquiv Q hK hQ hdim hE (QuotientGroup.mk A) =
      QuotientGroup.mk (derivedEquivElem Q hE A) := rfl

theorem centralEquiv_conj (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ d) (hE : orthDerived Q = elementaryGroup Q) (g : similarityPairs Q)
    (hg1 : g.val.right = 1)
    (hĝ : matrixLinearEquiv g.val.left ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    MulAut.congr (centralEquiv Q hK hQ hdim hE) (matrixProjectiveConjugationHom Q g) =
      autToCentralQuotient ↥(elementaryGroup Q)
        (conjE Q (matrixLinearEquiv g.val.left) hĝ) := by
  ext y
  obtain ⟨z, rfl⟩ := (centralEquiv Q hK hQ hdim hE).surjective y
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective z
  change centralEquiv Q hK hQ hdim hE (matrixProjectiveConjugation Q g
    ((centralEquiv Q hK hQ hdim hE).symm (centralEquiv Q hK hQ hdim hE (QuotientGroup.mk A)))) = _
  rw [MulEquiv.symm_apply_apply]
  have h1 : matrixProjectiveConjugation Q g (QuotientGroup.mk A) =
      QuotientGroup.mk (matrixDerivedConjugation Q g A) := matrixProjectiveConjugation_mk Q g A
  rw [h1, centralEquiv_mk, centralEquiv_mk, autToCentralQuotient_mk]
  congr 1
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have hA : glFieldAut (Fin d) K g.val.right A.1 = A.1 := by
    rw [hg1, map_one]
    rfl
  rw [coe_derivedEquivElem, matrixDerivedConjugation_val, hA]
  change matrixLinearIso (g.val.left * A.1 * g.val.left⁻¹) v =
    (matrixLinearEquiv g.val.left * matrixLinearEquiv A.1 * (matrixLinearEquiv g.val.left)⁻¹) v
  rw [map_mul, map_mul, map_inv]
  rfl

end Bridge

section Arith

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_one_or_neg_one (hK : Nat.card K = 3) (x : K) : x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := (three_eq_zero_two_ne_zero_of_card_eq_three hK).2
  have h1 : (1 : K) ≠ -1 := fun h => h2 (by linear_combination h)
  have h0 : (0 : K) ≠ 1 := zero_ne_one
  have h0' : (0 : K) ≠ -1 := fun h => one_ne_zero (neg_eq_zero.mp h.symm)
  have hcard : ({0, 1, -1} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h0, h0']), Finset.card_pair h1]
  have huniv : ({0, 1, -1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, ← Nat.card_eq_fintype_card, hK])
  have hx : x ∈ ({0, 1, -1} : Finset K) := by rw [huniv]; exact Finset.mem_univ x
  simpa using hx

theorem ringEquiv_eq_one (hK : Nat.card K = 3) (σ : K ≃+* K) : σ = 1 := by
  refine RingEquiv.ext fun x => ?_
  rcases eq_zero_or_one_or_neg_one hK x with rfl | rfl | rfl
  · simp
  · simp
  · simp

theorem sq_eq_one_of_ne_zero (hK : Nat.card K = 3) {x : K} (hx : x ≠ 0) : x ^ 2 = 1 := by
  rcases eq_zero_or_one_or_neg_one hK x with h | h | h
  · exact absurd h hx
  · simp [h]
  · simp [h]

theorem sq_ne_neg_one (hK : Nat.card K = 3) (x : K) : x ^ 2 ≠ -1 := by
  intro h
  have h2 : (2 : K) ≠ 0 := (three_eq_zero_two_ne_zero_of_card_eq_three hK).2
  by_cases hx : x = 0
  · rw [hx] at h
    simp at h
  · rw [sq_eq_one_of_ne_zero hK hx] at h
    exact h2 (by linear_combination h)

end Arith

section Multiplier

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem det_sq_eq_pow (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate) (A : GL (Fin d) K)
    (mu : K) (hmu : ∀ v, Q (matrixLinearEquiv A v) = mu * Q v) :
    (A : Matrix (Fin d) (Fin d) K).det ^ 2 = mu ^ d := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  let b := Pi.basisFun K (Fin d)
  let f : (Fin d → K) →ₗ[K] (Fin d → K) := Matrix.toLin' (A : Matrix (Fin d) (Fin d) K)
  have hcomp : Q.comp f = mu • Q := by
    ext v
    simp [f]
    exact hmu v
  have h1 := QuadraticForm.discr_comp (b := b) b Q f
  rw [hcomp, QuadraticForm.discr_smul] at h1
  have hnd : (QuadraticMap.associated Q).Nondegenerate := by
    rw [QuadraticMap.nondegenerate_associated_iff]
    exact QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hdisc : Q.discr b ≠ 0 := by
    have := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
    exact this
  have hf : f.toMatrix b b = (A : Matrix (Fin d) (Fin d) K) := by
    simp [f, b, LinearMap.toMatrix_eq_toMatrix']
  rw [hf, Fintype.card_fin] at h1
  rw [_root_.sq]
  exact (mul_right_cancel₀ hdisc h1).symm

end Multiplier

section Main

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem exists_similarity_of_aut (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ d) (hE : orthDerived Q = elementaryGroup Q) (himg : matrixProjectiveImage Q = ⊤)
    (ρ : MulAut (↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q))) :
    ∃ g : similarityPairs Q,
      ρ = MulAut.congr (centralEquiv Q hK hQ hdim hE) (matrixProjectiveConjugationHom Q g) := by
  have hmem : (MulAut.congr (centralEquiv Q hK hQ hdim hE)).symm ρ ∈ matrixProjectiveImage Q := by
    rw [himg]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q _).mp hmem
  refine ⟨g, ?_⟩
  have h1 : matrixProjectiveConjugationHom Q g =
      (MulAut.congr (centralEquiv Q hK hQ hdim hE)).symm ρ := hg
  rw [h1, MulEquiv.apply_symm_apply]

theorem oddCoreIn_top_eq_bot_of_perfect_simple {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hperf : Group.IsPerfect S) : Balance.oddCoreIn (⊤ : Subgroup S) = ⊥ := by
  have hN : (Balance.oddCoreIn (⊤ : Subgroup S)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (Balance.normalizer_oddCoreIn ⊤))
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Balance.oddCoreIn (⊤ : Subgroup S)) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card S) := by
      have := Balance.odd_card_oddCoreIn (⊤ : Subgroup S)
      rw [h, Subgroup.card_top] at this
      exact this
    have hsolv : Group.IsSolvable S := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial S
    rw [hperf.commutator_eq_top] at this
    exact lt_irrefl _ this

theorem fixedOddFree_central_odd (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 3 ≤ d) (hd : Odd d) (hE : orthDerived Q = elementaryGroup Q)
    (himg : matrixProjectiveImage Q = ⊤) (hperf : Group.IsPerfect ↥(elementaryGroup Q))
    (hsimple : IsSimpleGroup (↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q))) :
    FixedOddFree (↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q)) := by
  classical
  intro ρ hρ2
  have hdim' : 3 ≤ Module.finrank K (Fin d → K) := by simpa using hdim
  have h2 : (2 : K) ≠ 0 := (three_eq_zero_two_ne_zero_of_card_eq_three hK).2
  obtain ⟨g, hg⟩ := exists_similarity_of_aut Q hK hQ hdim hE himg ρ
  have hg1 : g.val.right = 1 := ringEquiv_eq_one hK _
  have hR : ∀ x : K, g.val.right x = x := fun x => by rw [hg1]; rfl
  obtain ⟨mu, hmu⟩ := (mem_similarityPairs_iff Q g.val).mp g.property
  have hmu' : ∀ v, Q (matrixLinearEquiv g.val.left v) = (mu : K) * Q v := by
    intro v
    have h := hmu v
    rw [hR] at h
    have hsem : coordinateSemilinearMap g.val v = matrixLinearEquiv g.val.left v := by
      rw [coordinateSemilinearMap_apply]
      simp only [hR]
      rfl
    rw [hsem] at h
    exact h
  have hdet := det_sq_eq_pow Q h2 hQ g.val.left mu hmu'
  have hmu1 : (mu : K) = 1 := by
    rcases eq_zero_or_one_or_neg_one hK (mu : K) with h | h | h
    · exact absurd h mu.ne_zero
    · exact h
    · exfalso
      rw [h, hd.neg_one_pow] at hdet
      exact sq_ne_neg_one hK _ hdet
  set ĝ := matrixLinearEquiv g.val.left with hĝdef
  have hĝ : ĝ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [hmu', hmu1, one_mul]
  have hρ : ρ = autToCentralQuotient ↥(elementaryGroup Q) (conjE Q ĝ hĝ) := by
    rw [hg, centralEquiv_conj Q hK hQ hdim hE g hg1 hĝ]
  have hconj2 : conjE Q ĝ hĝ * conjE Q ĝ hĝ = 1 := by
    apply autToCentralQuotient_injective (X := ↥(elementaryGroup Q))
    rw [map_mul, ← hρ, map_one]
    exact hρ2
  have hcomm : ∀ x : ↥(elementaryGroup Q), (ĝ * ĝ) * (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) * (ĝ * ĝ) := by
    intro x
    have h := congrArg (fun φ : MulAut ↥(elementaryGroup Q) =>
      ((φ x : ↥(elementaryGroup Q)) : (Fin d → K) ≃ₗ[K] (Fin d → K))) hconj2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    change ĝ * (ĝ * (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) * ĝ⁻¹) * ĝ⁻¹ = x at h
    calc (ĝ * ĝ) * (x : (Fin d → K) ≃ₗ[K] (Fin d → K))
        = ĝ * (ĝ * (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) * ĝ⁻¹) * ĝ⁻¹ * (ĝ * ĝ) := by group
      _ = (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) * (ĝ * ĝ) := by rw [h]
  obtain ⟨P, a, -, ha⟩ := exists_hypPair_and_aniso hK hQ hdim'
  have hA := hasAnisoPerp_of_three_le_finrank hQ hdim'
  have hν : ĝ * ĝ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hĝ hĝ
  have hsq : ĝ * ĝ ∈ scalars K (Fin d → K) :=
    mem_scalars_of_commute_eichler h2 hQ hA P hν fun u w _ _ =>
      hcomm ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩
  obtain ⟨c, hc⟩ := mem_scalars.mp hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := hc (Pi.single ⟨0, by omega⟩ 1)
    rw [zero_smul, LinearEquiv.map_eq_zero_iff, Pi.single_eq_zero_iff] at h
    exact one_ne_zero h
  have hc1 : c = 1 := by
    rcases eq_zero_or_one_or_neg_one hK c with h | h | h
    · exact absurd h hc0
    · exact h
    · exfalso
      have hAA : (g.val.left : Matrix (Fin d) (Fin d) K) * (g.val.left : Matrix (Fin d) (Fin d) K) =
          (-1 : Matrix (Fin d) (Fin d) K) := by
        apply Matrix.ext_of_mulVec_single
        intro k
        have h1 := hc (Pi.single k 1)
        rw [h, neg_one_smul] at h1
        change Matrix.mulVec (g.val.left : Matrix (Fin d) (Fin d) K)
          (Matrix.mulVec (g.val.left : Matrix (Fin d) (Fin d) K) (Pi.single k 1)) = _ at h1
        rw [Matrix.mulVec_mulVec] at h1
        rw [h1, Matrix.neg_mulVec, Matrix.one_mulVec]
      have h3 := congrArg Matrix.det hAA
      rw [Matrix.det_mul, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin,
        hd.neg_one_pow] at h3
      rw [← _root_.sq] at h3
      exact sq_ne_neg_one hK _ h3
  have hĝ2 : ĝ * ĝ = 1 := LinearEquiv.ext fun v => by rw [hc v, hc1, one_smul]; rfl
  by_cases hs : ĝ ∈ scalars K (Fin d → K)
  · have hconj1 : conjE Q ĝ hĝ = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      change ĝ * (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) * ĝ⁻¹ = x
      rw [commute_of_mem_scalars hs]
      group
    have hfix : fixedSubgroup (1 : MulAut (↥(elementaryGroup Q) ⧸
        Subgroup.center ↥(elementaryGroup Q))) = ⊤ := by
      ext x
      simp [mem_fixedSubgroup_iff]
    have hperfS : Group.IsPerfect (↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q)) :=
      isPerfect_of_surjective (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q)))
        (QuotientGroup.mk'_surjective _)
    rw [hρ, hconj1, map_one, hfix]
    exact oddCoreIn_top_eq_bot_of_perfect_simple hperfS
  · rw [hρ]
    exact oddCoreIn_fixed_eq_bot_of_involution hK hQ hdim' hĝ hĝ2 hs

end Main

end CFSG.ClassicalInvolution.Q3.Q3MFO
