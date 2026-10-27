module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthBlock
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open Polynomial Module CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped Matrix

@[expose] noncomputable def toMatGL {E U : Type*} [Field E] [AddCommGroup U] [Module E U] {m : ℕ}
    (b : Basis (Fin m) E U) :
    LinearMap.GeneralLinearGroup E U ≃* Matrix.GeneralLinearGroup (Fin m) E :=
  Units.mapEquiv (MulEquivClass.toMulEquiv (LinearMap.toMatrixAlgEquiv b))

theorem coe_toMatGL {E U : Type*} [Field E] [AddCommGroup U] [Module E U] {m : ℕ}
    (b : Basis (Fin m) E U) (γ : LinearMap.GeneralLinearGroup E U) :
    ((toMatGL b γ : Matrix.GeneralLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      LinearMap.toMatrix b b (γ : Module.End E U) := rfl

theorem det_toMatGL {E U : Type*} [Field E] [AddCommGroup U] [Module E U] {m : ℕ}
    (b : Basis (Fin m) E U) (γ : LinearMap.GeneralLinearGroup E U) :
    ((toMatGL b γ : Matrix.GeneralLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E).det =
      LinearMap.det (γ : Module.End E U) := by
  rw [coe_toMatGL, LinearMap.det_toMatrix]

theorem toMatGL_scalar {E U : Type*} [Field E] [AddCommGroup U] [Module E U] {m : ℕ}
    (b : Basis (Fin m) E U) (ω : Eˣ) (γ : LinearMap.GeneralLinearGroup E U)
    (hγ : ∀ u, (γ : Module.End E U) u = (ω : E) • u) :
    toMatGL b γ = Matrix.GeneralLinearGroup.scalar (Fin m) ω := by
  apply Units.ext
  rw [coe_toMatGL]
  have h1 : (γ : Module.End E U) = algebraMap E (Module.End E U) ω :=
    LinearMap.ext fun u => by rw [hγ]; rfl
  rw [h1]
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply,
    Finsupp.single_apply, eq_comm]

section Special

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

@[expose] noncomputable def specialMat (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X])
    [Fact (Irreducible h)] {m : ℕ}
    (b : Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
    ↥(specialBlock Q x h) →* Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h) :=
  (toMatGL b).toMonoidHom.comp (specialBlockGL Q x h)

theorem specialMat_injective (hx : OddOrderIsometry Q 3 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) {m : ℕ}
    (b : Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
    Function.Injective (specialMat Q x h b) :=
  (toMatGL b).injective.comp (hx.specialBlockGL_injective hh)

theorem det_specialMat (h : K[X]) [Fact (Irreducible h)] {m : ℕ}
    (b : Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (g : ↥(specialBlock Q x h)) :
    ((specialMat Q x h b g : Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) :
      Matrix (Fin m) (Fin m) (AdjoinRoot h)).det = 1 := by
  rw [specialMat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, det_toMatGL]
  exact det_specialBlockGL h g

theorem specialMat_surjective_paired (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ reciprocalPolynomial h) {m : ℕ}
    (b : Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (A : Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h))
    (hA : (A : Matrix (Fin m) (Fin m) (AdjoinRoot h)).det = 1) :
    ∃ g : ↥(specialBlock Q x h), specialMat Q x h b g = A := by
  obtain ⟨ĝ, hĝ⟩ := hx.blockGL_surjective_paired hh hne ((toMatGL b).symm A)
  have hdet : blockDet Q x h ĝ = 1 := by
    rw [blockDet_apply, hĝ, ← det_toMatGL b, MulEquiv.apply_symm_apply]
    exact hA
  refine ⟨⟨ĝ.1, mem_specialBlock.mpr ⟨ĝ.2, hdet⟩⟩, ?_⟩
  rw [specialMat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have : specialBlockGL Q x h ⟨ĝ.1, mem_specialBlock.mpr ⟨ĝ.2, hdet⟩⟩ = (toMatGL b).symm A := hĝ
  rw [this, MulEquiv.apply_symm_apply]

end Special

theorem mem_sesqUnitaryGroup_iff_matrix {E U : Type*} [Field E] [AddCommGroup U] [Module E U]
    {σ : E →+* E} {B : U →ₛₗ[σ] U →ₗ[E] E} {m : ℕ} (e : Basis (Fin m) E U)
    (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) (γ : LinearMap.GeneralLinearGroup E U) :
    γ ∈ sesqUnitaryGroup B ↔
      (((toMatGL e γ : Matrix.GeneralLinearGroup (Fin m) E) :
        Matrix (Fin m) (Fin m) E).map σ)ᵀ *
          ((toMatGL e γ : Matrix.GeneralLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) = 1 := by
  classical
  rw [coe_toMatGL]
  set A : Matrix (Fin m) (Fin m) E := LinearMap.toMatrix e e (γ : Module.End E U) with hA
  have h1 : ∀ i, (γ : Module.End E U) (e i) = ∑ k, A k i • e k := fun i => by
    conv_lhs => rw [← e.sum_repr ((γ : Module.End E U) (e i))]
    simp [hA, LinearMap.toMatrix_apply]
  have key : ∀ i j, B ((γ : Module.End E U) (e i)) ((γ : Module.End E U) (e j)) =
      ((A.map σ)ᵀ * A) i j := by
    intro i j
    rw [h1 i, h1 j]
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, he,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_ite_eq, mul_comm]
  constructor
  · intro hγ
    ext i j
    rw [← key, hγ, he]
    simp [Matrix.one_apply]
  · intro hmat
    intro u w
    have hext : (B.comp (γ : Module.End E U)).compl₂ (γ : Module.End E U) = B := by
      refine LinearMap.ext_basis e e fun i j => ?_
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
      rw [key, hmat, he]
      simp [Matrix.one_apply]
    exact LinearMap.congr_fun₂ hext u w

theorem reciprocalPolynomial_quadratic {K : Type} [Field K] :
    reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1 := by
  have hc : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by simp
  have hnd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hrev : (X ^ 2 + X + 1 : K[X]).reverse = X ^ 2 + X + 1 := by
    ext n
    rw [coeff_reverse, hnd]
    rcases n with _ | _ | _ | n
    · rw [revAt_le (by norm_num)]; try simp [coeff_X, coeff_one]
    · rw [revAt_le (by norm_num)]; try simp [coeff_X, coeff_one]
    · rw [revAt_le (by norm_num)]; try simp [coeff_X, coeff_one]
    · rw [revAt_eq_self_of_lt (by omega)]
  rw [reciprocalPolynomial, hc, hrev]
  simp

section Paired

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem dvd_quadratic_of_mem_primaryFactors (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    h ∣ (X ^ 2 + X + 1 : K[X]) := by
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hω3 : (AdjoinRoot.root h) ^ 3 = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hω1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  rw [← AdjoinRoot.mk_eq_zero]
  have : (AdjoinRoot.root h - 1) * (AdjoinRoot.root h ^ 2 + AdjoinRoot.root h + 1) = 0 := by
    linear_combination hω3
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hω1
  · simpa using h0

theorem natDegree_le_two_of_order_three (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) :
    h.natDegree ≤ 2 := by
  have hnd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  rw [← hnd]
  refine natDegree_le_of_dvd (dvd_quadratic_of_mem_primaryFactors hx hh hne1) ?_
  intro h0
  have := congrArg (Polynomial.eval 0) h0
  simp at this

theorem natDegree_eq_one_of_primary_paired (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) : h.natDegree = 1 := by
  have hirr : Irreducible h := Fact.out
  have hdvd := dvd_quadratic_of_mem_primaryFactors hx hh hne1
  have hnd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hle : h.natDegree ≤ 2 := by
    rw [← hnd]
    refine natDegree_le_of_dvd hdvd ?_
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp at this
  have hpos : 0 < h.natDegree := hirr.natDegree_pos
  by_contra hne2
  have h2 : h.natDegree = 2 := by omega
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hmon2 : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
  have heq : (X ^ 2 + X + 1 : K[X]) = h :=
    eq_of_monic_of_dvd_of_natDegree_le hmon hmon2 hdvd (by rw [hnd, h2])
  apply hne
  rw [← heq, reciprocalPolynomial_quadratic]

theorem two_mul_finrank_le_of_paired (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) :
    2 * finrank K (primaryComponent x.toLinearMap h) ≤ finrank K V := by
  classical
  have hsq := hx.squarefree_minpoly
  have hh' := hx.reciprocalPolynomial_mem hh
  have hdual : finrank K (primaryComponent x.toLinearMap (reciprocalPolynomial h)) =
      finrank K (primaryComponent x.toLinearMap h) := by
    have e := LinearEquiv.ofBijective (pairingHom Q x h).flip (hx.pairing_flip_bijective hh)
    rw [e.finrank_eq, Subspace.dual_finrank_eq]
  have hne' : (⟨h, hh⟩ : primaryFactors x.toLinearMap) ≠ ⟨reciprocalPolynomial h, hh'⟩ :=
    fun e => hne (congrArg Subtype.val e)
  rw [finrank_eq_sum_primaryComponent hsq]
  calc 2 * finrank K (primaryComponent x.toLinearMap h)
      = finrank K (primaryComponent x.toLinearMap h) +
          finrank K (primaryComponent x.toLinearMap (reciprocalPolynomial h)) := by
        rw [hdual]; ring
    _ = ∑ a ∈ ({⟨h, hh⟩, ⟨reciprocalPolynomial h, hh'⟩} : Finset (primaryFactors x.toLinearMap)),
          finrank K (primaryComponent x.toLinearMap (a : K[X])) := by
        rw [Finset.sum_pair hne']
    _ ≤ ∑ a : primaryFactors x.toLinearMap, finrank K (primaryComponent x.toLinearMap (a : K[X])) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem exists_selfDual_matrix_data (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) {m : ℕ}
    (hm : primaryMultiplicity x.toLinearMap h = m) :
    h.natDegree = 2 ∧
      ∃ b : Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h),
        ∀ γ : BlockGL x h, γ ∈ (blockGL Q x h).range ↔
          (((toMatGL b γ : Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) :
            Matrix (Fin m) (Fin m) (AdjoinRoot h)).map (· ^ Nat.card K))ᵀ *
            ((toMatGL b γ : Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) :
              Matrix (Fin m) (Fin m) (AdjoinRoot h)) = 1 := by
  classical
  subst hm
  have hirr : Irreducible h := Fact.out
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian (by decide : Odd 3) hh hne1 hself
  have hdeg2 := natDegree_le_two_of_order_three hx hh hne1
  have hpos : 0 < h.natDegree := hirr.natDegree_pos
  have hd1 : d = 1 := by omega
  subst hd1
  refine ⟨by omega, ?_⟩
  have hd : finrank K (AdjoinRoot h) = 2 * 1 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq0, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) 1 z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  obtain ⟨eb, heb⟩ := hU.exists_orthonormal_basis hBsymm hBl
  refine ⟨eb, fun γ => ?_⟩
  have hrange : γ ∈ (blockGL Q x h).range ↔ γ ∈ sesqUnitaryGroup B :=
    (hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH γ).trans
      (by rw [mem_sesqUnitaryGroup]; exact Iff.rfl)
  rw [hrange, mem_sesqUnitaryGroup_iff_matrix eb heb γ]
  have hfun : (fun z : AdjoinRoot h => z ^ Nat.card K) = ⇑hU.bar :=
    funext fun z => by rw [hbar z, pow_one]
  rw [hfun]

theorem exists_specialBlock_equiv_SL (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ reciprocalPolynomial h) {m : ℕ}
    (b : Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
    ∃ ε : ↥(specialBlock Q x h) ≃* ↥(StatedSL m (AdjoinRoot h)),
      ∀ g, ((ε g : ↥(StatedSL m (AdjoinRoot h))) :
        Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) = specialMat Q x h b g := by
  have hmem : ∀ g : ↥(specialBlock Q x h), specialMat Q x h b g ∈ StatedSL m (AdjoinRoot h) :=
    fun g => CFSG.Open.StatedAPI.mem_statedSL_of_det (det_specialMat h b g)
  let θ := (specialMat Q x h b).codRestrict _ hmem
  have hinj : Function.Injective θ := fun g g' e =>
    specialMat_injective hx hh b (congrArg Subtype.val e)
  have hsurj : Function.Surjective θ := fun A => by
    obtain ⟨g, hg⟩ := specialMat_surjective_paired hx hh hne b A.1
      (CFSG.Open.StatedAPI.mem_statedSL_iff.mp A.2)
    exact ⟨g, Subtype.ext hg⟩
  exact ⟨MulEquiv.ofBijective θ ⟨hinj, hsurj⟩, fun g => rfl⟩

theorem exists_specialBlock_equiv_SU (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) {m : ℕ}
    (b : Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (hb : ∀ γ : BlockGL x h, γ ∈ (blockGL Q x h).range ↔
      (((toMatGL b γ : Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) :
        Matrix (Fin m) (Fin m) (AdjoinRoot h)).map (· ^ Nat.card K))ᵀ *
        ((toMatGL b γ : Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) :
          Matrix (Fin m) (Fin m) (AdjoinRoot h)) = 1) :
    ∃ ε : ↥(specialBlock Q x h) ≃* ↥(StatedSU m (Nat.card K) (AdjoinRoot h)),
      ∀ g, ((ε g : ↥(StatedSU m (Nat.card K) (AdjoinRoot h))) :
        Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) = specialMat Q x h b g := by
  have hmem : ∀ g : ↥(specialBlock Q x h),
      specialMat Q x h b g ∈ StatedSU m (Nat.card K) (AdjoinRoot h) := fun g =>
    Subgroup.subset_closure ⟨det_specialMat h b g,
      (hb (specialBlockGL Q x h g)).mp ⟨⟨g.1, specialBlock_le_supportedBlock h g.2⟩, rfl⟩⟩
  let θ := (specialMat Q x h b).codRestrict _ hmem
  have hinj : Function.Injective θ := fun g g' e =>
    specialMat_injective hx hh b (congrArg Subtype.val e)
  have hle : StatedSU m (Nat.card K) (AdjoinRoot h) ≤ (specialMat Q x h b).range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro A ⟨hdet, hun⟩
    have hγ : (toMatGL b).symm A ∈ (blockGL Q x h).range := by
      rw [hb]
      rw [MulEquiv.apply_symm_apply]
      exact hun
    obtain ⟨ĝ, hĝ⟩ := hγ
    have hdet' : blockDet Q x h ĝ = 1 := by
      rw [blockDet_apply, hĝ, ← det_toMatGL b, MulEquiv.apply_symm_apply]
      exact hdet
    refine ⟨⟨ĝ.1, mem_specialBlock.mpr ⟨ĝ.2, hdet'⟩⟩, ?_⟩
    rw [specialMat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : specialBlockGL Q x h ⟨ĝ.1, mem_specialBlock.mpr ⟨ĝ.2, hdet'⟩⟩ = (toMatGL b).symm A :=
      hĝ
    rw [this, MulEquiv.apply_symm_apply]
  have hsurj : Function.Surjective θ := fun A => by
    obtain ⟨g, hg⟩ := hle A.2
    exact ⟨g, Subtype.ext hg⟩
  exact ⟨MulEquiv.ofBijective θ ⟨hinj, hsurj⟩, fun g => rfl⟩

end Paired

theorem three_dvd_of_scalar {E : Type} [Field E] {m : ℕ} (ω : Eˣ) (hω : orderOf ω = 3)
    (g : Matrix.GeneralLinearGroup (Fin m) E)
    (hg : g = Matrix.GeneralLinearGroup.scalar (Fin m) ω)
    (hdet : (g : Matrix (Fin m) (Fin m) E).det = 1) : 3 ∣ m := by
  rw [hg] at hdet
  have h1 : (ω : E) ^ m = 1 := by
    have : ((Matrix.GeneralLinearGroup.scalar (Fin m) ω : Matrix.GeneralLinearGroup (Fin m) E) :
        Matrix (Fin m) (Fin m) E) = Matrix.diagonal (fun _ => (ω : E)) := by
      ext i j
      simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.diagonal_apply]
    rw [this, Matrix.det_diagonal] at hdet
    simpa using hdet
  have h2 : ω ^ m = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
  rw [← hω]
  exact orderOf_dvd_of_pow_eq_one h2

theorem exists_phi_of_mulEquiv {W G J : Type*} [Group W] [Group G] [Group J] (H : Subgroup G)
    (ε : W ≃* H) (lam : W →* J) (hlam : Function.Surjective lam)
    (hker : lam.ker ≤ Subgroup.center W) :
    ∃ φ : ↥H →* J, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥H ∧
      ∀ w, φ (ε w) = lam w := by
  refine ⟨lam.comp ε.symm.toMonoidHom, fun j => ?_, fun z hz => ?_, fun w => ?_⟩
  · obtain ⟨w, hw⟩ := hlam j
    exact ⟨ε w, by simp [hw]⟩
  · have h1 : ε.symm z ∈ lam.ker := hz
    have h2 := Subgroup.mem_center_iff.mp (hker h1)
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w', rfl⟩ := ε.surjective y
    have := congrArg ε (h2 w')
    simpa using this
  · simp

theorem exists_projOrth_model_dim {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G]
    {n ℓ f : ℕ} (hG : StatedClassicalModel G t n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧ ringChar K = ℓ ∧
      Nat.card K = ℓ ^ f ∧ finrank K V = (if t = .POmegaOdd then 2 * n + 1 else 2 * n) ∧
      Nonempty (G ≃* ProjOrthDerived Q) := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h3 : 3 ≤ n ∧ ℓ ≠ 2 := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two
        (by rw [hring]; exact hadm.1), hring]
      exact h3.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := K) (n := n) h2 h3.1
    refine ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hring, hcard,
      ?_, ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadOdd n K))⟩⟩
    simp [Module.finrank_fintype_fun_eq_card]
    ring
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n)
      (by omega)
    refine ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hring, hcard,
      ?_, ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus (n := n) (K := K)))⟩⟩
    simp [Module.finrank_fintype_fun_eq_card]
    ring
  · obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ n := hadm.2.2
    have hring : ringChar K = ℓ :=
      CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hcard
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := n) h4 hirr
    refine ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hring, hcard,
      ?_, ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c))⟩⟩
    simp [Module.finrank_fintype_fun_eq_card]
    omega

section Odd

open CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem eq_one_of_scalar_of_odd (hx : OddOrderIsometry Q 3 x) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hodd : Odd (primaryMultiplicity x.toLinearMap h))
    {g : ↥(specialBlock Q x h)} (hsc : (g : V ≃ₗ[K] V) ∈ scalars K V)
    (hsq : (g : V ≃ₗ[K] V) ^ 2 = 1) : g = 1 := by
  obtain ⟨c, hc⟩ := mem_scalars.mp hsc
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot hx.squarefree_minpoly hh)
  have hc2 : c * c = 1 := by
    have h1 : (g : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) u) = u := by
      have := congrArg (fun f : V ≃ₗ[K] V => f u) hsq
      simpa [pow_two] using this
    rw [hc, hc, smul_smul] at h1
    by_contra hne
    refine hu0 ?_
    have h2 : (c * c - 1) • u = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hne
    · exact h3
  have hdet := det_specialBlockGL h g
  have hend : ((specialBlockGL Q x h g : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) =
        (algebraMap K (AdjoinRoot h) c) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    show (g : V ≃ₗ[K] V) (v : V) = ((algebraMap K (AdjoinRoot h) c • v :
      primaryComponent x.toLinearMap h) : V)
    rw [coe_algebraMap_smul_primaryComponent, hc]
  rw [hend, LinearMap.det_smul, LinearMap.det_id, mul_one] at hdet
  have hcm : c ^ primaryMultiplicity x.toLinearMap h = 1 := by
    apply (algebraMap K (AdjoinRoot h)).injective
    rw [map_pow, map_one]
    exact hdet
  obtain ⟨k, hk⟩ := hodd
  have hc1 : c = 1 := by
    rw [hk, pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul] at hcm
    exact hcm
  exact Subtype.ext (LinearEquiv.ext fun v => by rw [hc, hc1, one_smul]; rfl)

end Odd

section ModelSection

open CFSG.ClassicalGroups.Orthogonal CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped commutatorElement

section Lam

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_specialBlock_hom_onto {S : Type} [Group S] (e : S ≃* ProjOrthDerived Q)
    {J : Subgroup S}
    (x' : V ≃ₗ[K] V) (h : K[X]) (hSB : specialBlock Q x' h ≤ orthDerived Q)
    (hJh : J.map (e : S →* ProjOrthDerived Q) = componentImage Q x' h)
    (hkerc : (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))).ker ≤
      Subgroup.center ↥(orthDerived Q)) :
    ∃ lam : ↥(specialBlock Q x' h) →* ↥J, Function.Surjective lam ∧
      lam.ker ≤ Subgroup.center _ ∧
      ∀ g, ((lam g : ↥J) : S) = e.symm (QuotientGroup.mk' ((scalars K V).subgroupOf
        (orthDerived Q)) (Subgroup.inclusion hSB g)) := by
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  let lam₀ : ↥(specialBlock Q x' h) →* S :=
    (e.symm : ProjOrthDerived Q →* S).comp (ρ.comp (Subgroup.inclusion hSB))
  have hcomp : ∀ g : ↥(specialBlock Q x' h), ρ (Subgroup.inclusion hSB g) ∈
      J.map (e : S →* ProjOrthDerived Q) := fun g => by
    rw [hJh]
    exact ⟨Subgroup.inclusion hSB g, Subgroup.mem_subgroupOf.mpr g.2, rfl⟩
  have hmem : ∀ g, lam₀ g ∈ J := by
    intro g
    obtain ⟨j, hj, hjg⟩ := hcomp g
    show e.symm (ρ (Subgroup.inclusion hSB g)) ∈ J
    rw [← hjg]
    simpa using hj
  refine ⟨lam₀.codRestrict J hmem, fun j => ?_, fun g hg => ?_, fun g => rfl⟩
  · have : e j ∈ J.map (e : S →* ProjOrthDerived Q) := ⟨j, j.2, rfl⟩
    rw [hJh] at this
    obtain ⟨p, hp, hpe⟩ := this
    refine ⟨⟨(p : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hp⟩, Subtype.ext ?_⟩
    show e.symm (ρ (Subgroup.inclusion hSB ⟨(p : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hp⟩)) = j
    have : Subgroup.inclusion hSB ⟨(p : V ≃ₗ[K] V), Subgroup.mem_subgroupOf.mp hp⟩ = p :=
      Subtype.ext rfl
    rw [this, hpe]
    simp
  · have h1 : lam₀ g = 1 := congrArg Subtype.val hg
    have h2 : ρ (Subgroup.inclusion hSB g) = 1 := by
      have : e.symm (ρ (Subgroup.inclusion hSB g)) = 1 := h1
      simpa using this
    have h3 := Subgroup.mem_center_iff.mp (hkerc (by rw [MonoidHom.mem_ker]; exact h2))
    rw [Subgroup.mem_center_iff]
    intro g'
    apply Subgroup.inclusion_injective hSB
    rw [map_mul, map_mul]
    exact h3 _

end Lam

section Model

open CFSG.RankThree.Classical

theorem orth_blockIdentification_model {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpℓ : 3 ≠ ringChar K)
    {S : Type} [Group S] [Finite S] (e : S ≃* ProjOrthDerived Q)
    (hlayer : ∀ y : S, y ^ 3 = 1 → PerfectInLayer (MulAut.conj y))
    {x : S} (hx3 : orderOf x = 3) {J : Subgroup S}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) J) (hxJ : x ∈ J) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), 3 ∣ m ∧ 2 * m ≤ finrank K V ∧
      ((Nat.card E = Nat.card K ∧ ∃ (φ : ↥(StatedSL m E) →* ↥J) (ω : Eˣ)
          (g : ↥(StatedSL m E)), Function.Surjective φ ∧ φ.ker ≤ Subgroup.center _ ∧
          (Odd m → Function.Injective φ) ∧
          ω ≠ 1 ∧ ω ^ 3 = 1 ∧ (g : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin m) ω ∧
          (φ g : S) = x) ∨
        (Nat.card E = Nat.card K ^ 2 ∧ ∃ (φ : ↥(StatedSU m (Nat.card K) E) →* ↥J) (ω : Eˣ)
          (g : ↥(StatedSU m (Nat.card K) E)), Function.Surjective φ ∧
          φ.ker ≤ Subgroup.center _ ∧ (Odd m → Function.Injective φ) ∧
          ω ≠ 1 ∧ ω ^ 3 = 1 ∧
          (g : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin m) ω ∧ (φ g : S) = x)) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, hcenter, hcard, -, -, -, -, -, hlift⟩ :=
    orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hkerρ : ρ.ker = (scalars K V).subgroupOf (orthDerived Q) := QuotientGroup.ker_mk' _
  have hkerc : ρ.ker ≤ Subgroup.center ↥(orthDerived Q) := by rw [hkerρ, hcenter]
  have hkerq : ∀ z ∈ ρ.ker, z ^ 2 = 1 := by
    intro z hz
    rw [hkerρ] at hz
    have h1 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣
        Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨z, hz⟩ : ↥((scalars K V).subgroupOf (orthDerived Q))) ∣ 2 := by
      have hpos : 0 < Nat.card ↥((scalars K V).subgroupOf (orthDerived Q)) := Nat.card_pos
      interval_cases hc : Nat.card ↥((scalars K V).subgroupOf (orthDerived Q))
      · exact h1.trans (one_dvd _)
      · exact h1
    have h3 := orderOf_dvd_iff_pow_eq_one.mp h2
    exact congrArg Subtype.val h3
  have hord : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx3
  obtain ⟨y, ⟨hya, hyp⟩, -, hcent⟩ := hlift 3 Nat.prime_three (by norm_num) (e x) hord
  have hy3 : y ^ 3 = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := fun h => by
    have : orderOf y = 1 := by rw [h]; exact orderOf_one
    omega
  have hρy : ρ y = e x := hya
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hfix := fixSubgroup_conj_eq_centralizer_so x
  have hcomp3 : GLAPComponent 3
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) J := by
    rw [hfix]; exact hJ
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJle : J ≤
      GLALayer (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) :=
    hlayer x hx3' J (by rw [hfix]; exact hJ.1) hJperf
  have hJcomp : IsComponentOf J (Subgroup.centralizer ({x} : Set S)) := by
    rw [← hfix]; exact (glaPComponent_isComponent_of_le_layer hcomp3 hJle).1
  have hJT : CFSG.Open.IsComponentOf (J.map (e : S →* ProjOrthDerived Q))
      (Subgroup.centralizer ({(QuotientGroup.mk y : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q))) := by
    have h1 := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hJcomp
    rw [map_centralizer_equiv] at h1
    have : (QuotientGroup.mk y : ProjOrthDerived Q) = e x := hya
    rw [this]; exact h1
  have hcent' : Subgroup.centralizer ({(QuotientGroup.mk y : ProjOrthDerived Q)} :
      Set (ProjOrthDerived Q)) = (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
    have : (QuotientGroup.mk y : ProjOrthDerived Q) = e x := hya
    rw [this]; exact hcent
  rcases orth_component_cases Nat.prime_three (by norm_num) hQ hpℓ y hy3 hcent' _ hJT with
    ⟨h, hh, hne1, hq, hJh⟩ | ⟨F, hF, hJF⟩
  swap
  · exfalso
    have hρyJ : ρ y ∈ (F.subgroupOf (orthDerived Q)).map ρ := by
      rw [← hJF]; exact ⟨x, hxJ, hρy.symm⟩
    have hyF : y ∈ F.subgroupOf (orthDerived Q) := mem_of_map_mem_of_cube ρ hkerc hkerq hy3 hρyJ
    have hyF' : (y : V ≃ₗ[K] V) ∈
        supportedBlock Q (y : V ≃ₗ[K] V) (Polynomial.X - 1 : K[X]) :=
      supportedFixedDerived_le_supportedBlock (hF (Subgroup.mem_subgroupOf.mp hyF))
    have hx : OddOrderIsometry Q 3 (y : V ≃ₗ[K] V) :=
      oddOrderIsometry_of_pow_eq_one Nat.prime_three hpℓ hQ y hy3
    exact hy1 (Subtype.ext (eq_one_of_mem_supportedBlock_fixed hx hyF'))
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := finite_adjoinRoot_of_fact h
  have hirr : Irreducible h := Fact.out
  have hx : OddOrderIsometry Q 3 (y : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_pow_eq_one Nat.prime_three hpℓ hQ y hy3
  have hSB : specialBlock Q (y : V ≃ₗ[K] V) h ≤ orthDerived Q :=
    specialBlock_le_orthDerived_of_perfect hq.1
      ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  have hρyJ : ρ y ∈ componentImage Q (y : V ≃ₗ[K] V) h := by
    rw [← hJh]; exact ⟨x, hxJ, hρy.symm⟩
  have hymem : (y : V ≃ₗ[K] V) ∈ specialBlock Q (y : V ≃ₗ[K] V) h :=
    Subgroup.mem_subgroupOf.mp (mem_of_map_mem_of_cube ρ hkerc hkerq hy3 hρyJ)
  obtain ⟨lam, hlam, hlamker, hlamval⟩ :=
    exists_specialBlock_hom_onto e (y : V ≃ₗ[K] V) h hSB hJh hkerc
  obtain ⟨hω0, hordu⟩ := hx.orderOf_root Nat.prime_three hh hne1
  obtain ⟨ω, hωval, hωord⟩ : ∃ ω : (AdjoinRoot h)ˣ, (ω : AdjoinRoot h) = AdjoinRoot.root h ∧
      orderOf ω = 3 := ⟨Units.mk0 _ hω0, rfl, hordu⟩
  have hω3 : ω ^ 3 = 1 := by
    have := pow_orderOf_eq_one ω
    rwa [hωord] at this
  have hω1 : ω ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hωord
    omega
  set y₀ : ↥(specialBlock Q (y : V ≃ₗ[K] V) h) := ⟨y, hymem⟩ with hy₀def
  have hy₀ : ∀ u, ((specialBlockGL Q (y : V ≃ₗ[K] V) h y₀ : BlockGL (y : V ≃ₗ[K] V) h) :
      Module.End (AdjoinRoot h) (primaryComponent (y : V ≃ₗ[K] V).toLinearMap h)) u =
        (ω : AdjoinRoot h) • u := by
    intro u
    apply Subtype.ext
    rw [hωval, coe_root_smul_primaryComponent]
    rfl
  have hlamy : ((lam y₀ : ↥J) : S) = x := by
    rw [hlamval]
    have : Subgroup.inclusion hSB y₀ = y := rfl
    rw [this, hρy]
    simp
  have hinj_gen : ∀ {H : Type} [Group H] (ε : ↥(specialBlock Q (y : V ≃ₗ[K] V) h) ≃* H)
      (φ : H →* ↥J), (∀ w, φ (ε w) = lam w) →
        Odd (primaryMultiplicity (y : V ≃ₗ[K] V).toLinearMap h) → Function.Injective φ := by
    intro H _ ε φ hφε hodd
    rw [injective_iff_map_eq_one]
    intro z hz
    obtain ⟨g₁, rfl⟩ := ε.surjective z
    rw [hφε] at hz
    have h1 : ρ (Subgroup.inclusion hSB g₁) = 1 := by
      have h2 := hlamval g₁
      rw [hz] at h2
      have h3 : e.symm (ρ (Subgroup.inclusion hSB g₁)) = 1 := h2.symm
      simpa using h3
    have hmemker : Subgroup.inclusion hSB g₁ ∈ ρ.ker := h1
    have hsc : (g₁ : V ≃ₗ[K] V) ∈ scalars K V := by
      have h4 := hmemker
      rw [hkerρ] at h4
      exact Subgroup.mem_subgroupOf.mp h4
    have hsq : (g₁ : V ≃ₗ[K] V) ^ 2 = 1 := by
      have h5 := congrArg Subtype.val (hkerq _ hmemker)
      simpa using h5
    rw [eq_one_of_scalar_of_odd hx hh hodd hsc hsq, map_one]
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hcardE : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h), hfin]
  have hU : finrank K (primaryComponent (y : V ≃ₗ[K] V).toLinearMap h) =
      h.natDegree * primaryMultiplicity (y : V ≃ₗ[K] V).toLinearMap h :=
    finrank_primaryComponent _ h
  have hUle : finrank K (primaryComponent (y : V ≃ₗ[K] V).toLinearMap h) ≤ finrank K V :=
    Submodule.finrank_le _
  set m := primaryMultiplicity (y : V ≃ₗ[K] V).toLinearMap h with hm
  by_cases hself : h = reciprocalPolynomial h
  ·
    obtain ⟨hdeg, b, hb⟩ := exists_selfDual_matrix_data hx hh hne1 hself rfl
    obtain ⟨ε, hε⟩ := exists_specialBlock_equiv_SU hx hh b hb
    obtain ⟨φ, hφs, hφk, hφε⟩ := exists_phi_of_mulEquiv _ ε lam hlam hlamker
    have hg : ((ε y₀ : ↥(StatedSU m (Nat.card K) (AdjoinRoot h))) :
        Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) =
          Matrix.GeneralLinearGroup.scalar (Fin m) ω := by
      rw [hε]
      exact toMatGL_scalar b ω _ hy₀
    have h3 : 3 ∣ m :=
      three_dvd_of_scalar ω hωord _ hg (CFSG.Open.StatedAPI.det_of_mem_statedSU (ε y₀).2)
    refine ⟨AdjoinRoot h, inferInstance, inferInstance, m, h3, ?_,
      Or.inr ⟨?_, φ, ω, ε y₀, hφs, hφk, hinj_gen ε φ hφε, hω1, hω3, hg, ?_⟩⟩
    · rw [hU, hdeg] at hUle
      exact hUle
    · rw [hcardE, hdeg]
    · rw [hφε]; exact hlamy
  ·
    have hdeg1 := natDegree_eq_one_of_primary_paired hx hh hne1 hself
    let b := Module.finBasis (AdjoinRoot h) (primaryComponent (y : V ≃ₗ[K] V).toLinearMap h)
    obtain ⟨ε, hε⟩ := exists_specialBlock_equiv_SL hx hh hself b
    obtain ⟨φ, hφs, hφk, hφε⟩ := exists_phi_of_mulEquiv _ ε lam hlam hlamker
    have hg : ((ε y₀ : ↥(StatedSL m (AdjoinRoot h))) :
        Matrix.GeneralLinearGroup (Fin m) (AdjoinRoot h)) =
          Matrix.GeneralLinearGroup.scalar (Fin m) ω := by
      rw [hε]
      exact toMatGL_scalar b ω _ hy₀
    have h3 : 3 ∣ m :=
      three_dvd_of_scalar ω hωord _ hg (CFSG.Open.StatedAPI.mem_statedSL_iff.mp (ε y₀).2)
    refine ⟨AdjoinRoot h, inferInstance, inferInstance, m, h3, ?_,
      Or.inl ⟨?_, φ, ω, ε y₀, hφs, hφk, hinj_gen ε φ hφε, hω1, hω3, hg, ?_⟩⟩
    · have h2 := two_mul_finrank_le_of_paired hx hh hself
      rw [hU, hdeg1, one_mul] at h2
      exact h2
    · rw [hcardE, hdeg1, pow_one]
    · rw [hφε]; exact hlamy

end Model

theorem orth_blockIdentification :
    ∀ (t : StatedLieTag), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
      ∀ (S : Type) [Group S] [Finite S] (n ℓ f : ℕ), StatedClassicalModel S t n ℓ f → ℓ ≠ 3 →
      ∀ x : S, orderOf x = 3 → ∀ J : Subgroup S,
        GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) J → x ∈ J →
        ∃ (K E : Type) (_ : Field K) (_ : Field E) (_ : Finite K) (_ : Finite E) (m : ℕ),
          Nat.card K = ℓ ^ f ∧ 3 ∣ m ∧ 2 * m ≤ (if t = .POmegaOdd then 2 * n + 1 else 2 * n) ∧
          ((Nat.card E = Nat.card K ∧ ∃ (φ : ↥(StatedSL m E) →* ↥J) (ω : Eˣ)
              (g : ↥(StatedSL m E)), Function.Surjective φ ∧ φ.ker ≤ Subgroup.center _ ∧
              (Odd m → Function.Injective φ) ∧ ω ≠ 1 ∧ ω ^ 3 = 1 ∧
              (g : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin m) ω ∧
              (φ g : S) = x) ∨
           (Nat.card E = Nat.card K ^ 2 ∧ ∃ (φ : ↥(StatedSU m (Nat.card K) E) →* ↥J) (ω : Eˣ)
              (g : ↥(StatedSU m (Nat.card K) E)), Function.Surjective φ ∧ φ.ker ≤ Subgroup.center _ ∧
              (Odd m → Function.Injective φ) ∧ ω ≠ 1 ∧ ω ^ 3 = 1 ∧
              (g : GL (Fin m) E) = Matrix.GeneralLinearGroup.scalar (Fin m) ω ∧
              (φ g : S) = x)) := by
  intro t ht S _ _ n ℓ f hG hℓ3 x hx3 J hJ hxJ
  obtain ⟨K, hKf, hKfin, V, _, _, _, Q, hQ, hT, hring, hcard, hdim, ⟨e⟩⟩ :=
    exists_projOrth_model_dim ht hG
  have hpℓ : 3 ≠ ringChar K := by rw [hring]; exact fun h => hℓ3 h.symm
  have hlayer : ∀ y : S, y ^ 3 = 1 → PerfectInLayer (MulAut.conj y) := fun y hy =>
    LieSemisimple.perfectInLayer_conj_omega ht hG Nat.prime_three (by norm_num) (Ne.symm hℓ3) y hy
  obtain ⟨E, hEf, hEfin, m, h3, h2, hcases⟩ :=
    orth_blockIdentification_model hQ hT hpℓ e hlayer hx3 hJ hxJ
  exact ⟨K, E, hKf, hEf, hKfin, hEfin, m, hcard, h3, hdim ▸ h2, hcases⟩

end ModelSection

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
