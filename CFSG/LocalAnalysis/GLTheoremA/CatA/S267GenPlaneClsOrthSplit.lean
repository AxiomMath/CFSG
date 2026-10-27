module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open Module Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix MatrixGroups

section Glue

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem det_glue {U R : Submodule K V} (hc : IsCompl U R) (a : U ≃ₗ[K] U) (b : R ≃ₗ[K] R) :
    LinearEquiv.det (glue hc a b) = LinearEquiv.det a * LinearEquiv.det b := by
  have h : glue hc a b = ((Submodule.prodEquivOfIsCompl U R hc).symm.trans
      (LinearEquiv.prodCongr a b)).trans (Submodule.prodEquivOfIsCompl U R hc) :=
    LinearEquiv.ext fun _ => rfl
  rw [h, LinearEquiv.det_conj]
  ext
  simp [LinearEquiv.coe_det, LinearMap.det_prodMap]

end Glue

section Others

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private noncomputable def othersForm (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    LinearMap.BilinForm K (othersSpace x.toLinearMap (X - 1)) :=
  (QuadraticMap.polarBilin Q).compl₁₂ (othersSpace x.toLinearMap (X - 1)).subtype
    ((x.toLinearMap - x.symm.toLinearMap) ∘ₗ (othersSpace x.toLinearMap (X - 1)).subtype)

private theorem othersForm_apply (u v : othersSpace x.toLinearMap (X - 1)) :
    othersForm Q x u v = QuadraticMap.polar Q u (x v - x.symm v) := rfl

private theorem othersForm_isAlt (hx : OddOrderIsometry Q p x) : (othersForm Q x).IsAlt := by
  intro v
  rw [othersForm_apply, QuadraticMap.polar_sub_right, ← hx.polar_apply,
    QuadraticMap.polar_comm (⇑Q) (x (v : V)) (v : V), sub_self]

private theorem eq_zero_of_apply_eq_symm (hx : OddOrderIsometry Q p x) (hp : Odd p) {v : V}
    (hv : v ∈ othersSpace x.toLinearMap (X - 1)) (h : x v = x.symm v) : v = 0 := by
  have h2 : x (x v) = v := by rw [h, x.apply_symm_apply]
  have h2k : ∀ k : ℕ, (x ^ (2 * k)) v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add, LinearEquiv.mul_apply, ih, pow_two,
        LinearEquiv.mul_apply, h2]
  obtain ⟨k, rfl⟩ := hp
  have h1 : x v = v := by
    have hp1 : (x ^ (2 * k + 1)) v = v := by rw [hx.pow_eq_one]; rfl
    rw [pow_succ', LinearEquiv.mul_apply, h2k] at hp1
    exact hp1
  exact Submodule.disjoint_def.mp hx.fixed_others.1.disjoint v (mem_fixedSpace.mpr h1) hv

private theorem mem_others_of_mem_centralizer {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) {r : V}
    (hr : r ∈ othersSpace x.toLinearMap (X - 1)) : g r ∈ othersSpace x.toLinearMap (X - 1) :=
  mem_othersSpace_of_apply hg hr

private theorem exists_sub_eq (hx : OddOrderIsometry Q p x) (hp : Odd p) {r : V}
    (hr : r ∈ othersSpace x.toLinearMap (X - 1)) :
    ∃ v ∈ othersSpace x.toLinearMap (X - 1), x v - x.symm v = r := by
  have hxc : x ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxs : x.symm ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := symm_mem_centralizer x hxc
  let D : othersSpace x.toLinearMap (X - 1) →ₗ[K] othersSpace x.toLinearMap (X - 1) :=
    (x.toLinearMap - x.symm.toLinearMap).restrict fun v hv =>
      Submodule.sub_mem _ (mem_others_of_mem_centralizer hxc hv)
        (mem_others_of_mem_centralizer hxs hv)
  have hinj : Function.Injective D := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : x v - x.symm v = 0 := congrArg Subtype.val hv
    exact Subtype.ext (eq_zero_of_apply_eq_symm hx hp v.2 (sub_eq_zero.mp h0))
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨r, hr⟩
  exact ⟨v, v.2, congrArg Subtype.val hv⟩

private theorem othersForm_nondegenerate (hx : OddOrderIsometry Q p x) (hp : Odd p) :
    (othersForm Q x).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl (othersForm_isAlt hx)).nondegenerate_iff_separatingLeft.mpr
    fun u hu => ?_
  obtain ⟨hc, horth⟩ := hx.fixed_others
  have hR : ∀ r ∈ othersSpace x.toLinearMap (X - 1), QuadraticMap.polar Q u r = 0 := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := exists_sub_eq hx hp hr
    simpa [othersForm_apply] using hu ⟨v, hv⟩
  have hall : ∀ y, QuadraticMap.polar Q u y = 0 := by
    intro y
    obtain ⟨w, r, rfl⟩ := exists_coe_add_of_isCompl hc y
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm, horth w w.2 u u.2, hR r r.2,
      add_zero]
  exact Subtype.ext (hx.regular u hall)

theorem det_restrict_others (hx : OddOrderIsometry Q p x) (hp : Odd p)
    {c : V ≃ₗ[K] V} (hc : c ∈ isometryCentralizer Q x)
    (h1 : ∀ r ∈ othersSpace x.toLinearMap (X - 1), c r ∈ othersSpace x.toLinearMap (X - 1))
    (h2 : ∀ r ∈ othersSpace x.toLinearMap (X - 1), c.symm r ∈ othersSpace x.toLinearMap (X - 1)) :
    LinearEquiv.det (restrictEquiv _ c h1 h2) = 1 := by
  have hcx := (mem_isometryCentralizer.mp hc).2
  have hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.mem_inf.mp hc).1
  have hcsymm : ∀ v, c (x.symm v) = x.symm (c v) := by
    intro v
    have h := hcx (x.symm v)
    rw [x.apply_symm_apply] at h
    rw [h, x.symm_apply_apply]
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_one]
  refine det_eq_one_of_isAlt (othersForm_isAlt hx) (othersForm_nondegenerate hx hp) _
    fun u v => ?_
  rw [othersForm_apply, othersForm_apply]
  simp only [LinearEquiv.coe_coe, coe_restrictEquiv]
  rw [← hcx, ← hcsymm, ← map_sub, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hcO]

theorem det_restrict_fixed (hx : OddOrderIsometry Q p x) (hp : Odd p)
    {c : V ≃ₗ[K] V} (hc : c ∈ isometryCentralizer Q x) (hdet : LinearEquiv.det c = 1)
    (h1 : ∀ w ∈ fixedSpace x, c w ∈ fixedSpace x)
    (h2 : ∀ w ∈ fixedSpace x, c.symm w ∈ fixedSpace x) :
    LinearEquiv.det (restrictEquiv _ c h1 h2) = 1 := by
  have hcpl := hx.fixed_others.1
  have hcc : c ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hc).2
  have k1 : ∀ r ∈ othersSpace x.toLinearMap (X - 1), c r ∈ othersSpace x.toLinearMap (X - 1) :=
    fun r hr => mem_others_of_mem_centralizer hcc hr
  have k2 : ∀ r ∈ othersSpace x.toLinearMap (X - 1),
      c.symm r ∈ othersSpace x.toLinearMap (X - 1) :=
    fun r hr => mem_others_of_mem_centralizer (symm_mem_centralizer x hcc) hr
  have hglue : c = glue hcpl (restrictEquiv _ c h1 h2) (restrictEquiv _ c k1 k2) := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, r, rfl⟩ := exists_coe_add_of_isCompl hcpl v
    rw [glue_apply, map_add, coe_restrictEquiv, coe_restrictEquiv]
  have h := congrArg LinearEquiv.det hglue
  rw [det_glue, det_restrict_others hx hp hc k1 k2, mul_one, hdet] at h
  exact h.symm

end Others

section Model

variable {K : Type*} [Field K]

private theorem det_mulRight_matrix (M : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.det (LinearMap.mulRight K M) = M.det ^ 2 := by
  let φ : (Fin 2 → Fin 2 → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K := Matrix.ofLinearEquiv K
  have h : (φ.symm : Matrix (Fin 2) (Fin 2) K →ₗ[K] (Fin 2 → Fin 2 → K)) ∘ₗ
      LinearMap.mulRight K M ∘ₗ (φ.symm.symm : (Fin 2 → Fin 2 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) K) =
      LinearMap.pi (fun i : Fin 2 => (Matrix.vecMulLinear M).comp (LinearMap.proj i)) := by
    refine LinearMap.ext fun v => funext fun i => funext fun j => ?_
    simp [φ, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have h2 := LinearMap.det_conj (LinearMap.mulRight K M) φ.symm
  rw [h, LinearMap.det_pi] at h2
  rw [← h2, ← Matrix.mulVecLin_transpose, ← Matrix.toLin'_apply', LinearMap.det_toLin',
    Matrix.det_transpose, Fin.prod_const]

private theorem det_mulLeft_matrix (M : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.det (LinearMap.mulLeft K M) = M.det ^ 2 := by
  let τ := Matrix.transposeLinearEquiv (Fin 2) (Fin 2) K K
  have h : (τ : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) ∘ₗ
      LinearMap.mulLeft K M ∘ₗ (τ.symm : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) =
      LinearMap.mulRight K Mᵀ := by
    refine LinearMap.ext fun X => ?_
    simp [τ, Matrix.transpose_mul]
  have h2 := LinearMap.det_conj (LinearMap.mulLeft K M) τ
  rw [h, det_mulRight_matrix, Matrix.det_transpose] at h2
  exact h2.symm

theorem det_rho (z : equalDeterminants K) : LinearEquiv.det (rho z).val = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_one]
  have h : ((rho z).val : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K) =
      LinearMap.mulRight K (z.val.2⁻¹).val ∘ₗ LinearMap.mulLeft K z.val.1.val := by
    refine LinearMap.ext fun X => ?_
    simp [rho_apply, Matrix.mul_assoc]
  have hz := (mem_equalDeterminants z.val.1 z.val.2).mp z.property
  rw [h, LinearMap.det_comp, det_mulRight_matrix, det_mulLeft_matrix, hz, ← mul_pow,
    ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_pow]

theorem det_tau : LinearEquiv.det (tau (K := K)).val = -1 := by
  set J : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0] with hJ
  have hdet : determinantForm K J = 1 := by
    rw [determinantForm_apply, hJ, Matrix.det_fin_two_of]
    ring
  letI : Invertible (determinantForm K J) := ⟨1, by rw [hdet, one_mul], by rw [hdet, one_mul]⟩
  have heq : (tau (K := K)).val = TauCeti.QuadraticMap.reflection (determinantForm K) J := by
    refine LinearEquiv.ext fun X => ?_
    rw [tau_apply, TauCeti.QuadraticMap.reflection_apply]
    have hinv : ⅟(determinantForm K J) = 1 := rfl
    rw [hinv, one_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticMap.polar, determinantForm_apply, Matrix.det_fin_two, hJ] <;> ring
  rw [heq, TauCeti.QuadraticMap.det_reflection]

theorem exists_rho_of_det_eq_one (h2 : (2 : K) ≠ 0) (g : DeterminantIsometries K)
    (hg : LinearEquiv.det g.val = 1) : ∃ z, g = rho z := by
  obtain ⟨z, hz | hz⟩ := determinant_isometry_exhaustion g
  · exact ⟨z, hz⟩
  · exfalso
    have h : LinearEquiv.det g.val = -1 := by
      rw [hz, Subgroup.coe_mul, map_mul, det_rho, det_tau, one_mul]
    rw [hg] at h
    have h' := congrArg Units.val h
    rw [Units.val_one, Units.val_neg, Units.val_one] at h'
    exact h2 (by linear_combination h')

private noncomputable def conjSLPair (A : GL (Fin 2) K) (S : SL(2, K)) : SL(2, K) :=
  ⟨A.val * S.val * (A⁻¹).val, by
    rw [Matrix.det_mul, Matrix.det_mul, S.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem rho_conj_mem_left (z : equalDeterminants K) {g : DeterminantIsometries K}
    (hg : g ∈ determinantLeftFactor K) : rho z * g * (rho z)⁻¹ ∈ determinantLeftFactor K := by
  obtain ⟨S, rfl⟩ := hg
  refine ⟨conjSLPair z.val.1 S, Subtype.ext (LinearEquiv.ext fun X => ?_)⟩
  change (specialRho (conjSLPair z.val.1 S, 1)).val X =
    (rho z).val ((specialRho (S, 1)).val ((rho z)⁻¹.val X))
  rw [← map_inv, specialRho_apply, specialRho_apply, rho_apply, rho_apply]
  simp only [conjSLPair, Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv, inv_inv, inv_one,
    Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem rho_conj_mem_right (z : equalDeterminants K) {g : DeterminantIsometries K}
    (hg : g ∈ determinantRightFactor K) : rho z * g * (rho z)⁻¹ ∈ determinantRightFactor K := by
  obtain ⟨S, rfl⟩ := hg
  refine ⟨conjSLPair z.val.2 S, Subtype.ext (LinearEquiv.ext fun X => ?_)⟩
  have hT : Matrix.SpecialLinearGroup.toGL (conjSLPair z.val.2 S) =
      z.val.2 * Matrix.SpecialLinearGroup.toGL S * z.val.2⁻¹ := Units.ext rfl
  change (specialRho (1, conjSLPair z.val.2 S)).val X =
    (rho z).val ((specialRho (1, S)).val ((rho z)⁻¹.val X))
  rw [← map_inv]
  change (Matrix.SpecialLinearGroup.toGL (1 : SL(2, K))).val * X *
      ((Matrix.SpecialLinearGroup.toGL (conjSLPair z.val.2 S))⁻¹).val =
    z.val.1.val * ((Matrix.SpecialLinearGroup.toGL (1 : SL(2, K))).val *
      ((z⁻¹).val.1.val * X * ((z⁻¹).val.2⁻¹).val) *
        ((Matrix.SpecialLinearGroup.toGL S)⁻¹).val) * (z.val.2⁻¹).val
  rw [hT, map_one]
  simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv, inv_inv, mul_inv_rev, Units.val_mul,
    Units.val_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end Model

section Transport

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private noncomputable def restrictFixedIso (c : V ≃ₗ[K] V) (hc : c ∈ isometryCentralizer Q x) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
  ⟨restrictEquiv (fixedSpace x) c
      (fun _ hw => mem_fixedSpace_of_apply (Subgroup.mem_inf.mp hc).2 hw)
      (fun _ hw => mem_fixedSpace_of_apply (symm_mem_centralizer x (Subgroup.mem_inf.mp hc).2) hw),
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => by
      show Q (c (w : V)) = Q (w : V)
      exact (mem_isometryCentralizer.mp hc).1 w⟩

private theorem fixedBlockEquiv_conj (hx : OddOrderIsometry Q p x) {c : V ≃ₗ[K] V}
    (hc : c ∈ isometryCentralizer Q x) (f : ↥(supportedBlock Q x (X - 1))) :
    fixedBlockEquiv hx ⟨c * f.1 * c⁻¹, conj_mem_supportedBlock hc f.2⟩ =
      restrictFixedIso c hc * fixedBlockEquiv hx f * (restrictFixedIso c hc)⁻¹ :=
  Subtype.ext (LinearEquiv.ext fun _ => Subtype.ext rfl)

private theorem conj_mem_splitFourFactors {W : Type*} [AddCommGroup W] [Module K W]
    {QW : QuadraticForm K W}
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup QW) ≃* DeterminantIsometries K)
    {γ : ↥(TauCeti.QuadraticMap.orthogonalGroup QW)} {z : equalDeterminants K}
    (hz : e γ = rho z) (i : Fin 2) {ℓ : ↥(TauCeti.QuadraticMap.orthogonalGroup QW)}
    (hℓ : ℓ ∈ splitFourFactors e i) : γ * ℓ * γ⁻¹ ∈ splitFourFactors e i := by
  have key : ∀ L : Subgroup (DeterminantIsometries K),
      (∀ g ∈ L, rho z * g * (rho z)⁻¹ ∈ L) →
      ∀ ℓ ∈ L.map e.symm.toMonoidHom, γ * ℓ * γ⁻¹ ∈ L.map e.symm.toMonoidHom := by
    rintro L hL _ ⟨g, hg, rfl⟩
    refine ⟨rho z * g * (rho z)⁻¹, hL g hg, ?_⟩
    apply e.injective
    simp [hz]
  fin_cases i
  · exact key _ (fun g hg => rho_conj_mem_left z hg) ℓ hℓ
  · exact key _ (fun g hg => rho_conj_mem_right z hg) ℓ hℓ

theorem conj_mem_supportedFactor_splitFour (hx : OddOrderIsometry Q p x) (hp : Odd p)
    (h2 : (2 : K) ≠ 0) {ψ : fixedSpace x ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    {e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K}
    (he : ∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
      (X : Matrix (Fin 2) (Fin 2) K), (e g).val X = ψ (g.val (ψ.symm X)))
    {c : V ≃ₗ[K] V} (hc : c ∈ isometryCentralizer Q x) (hdet : LinearEquiv.det c = 1)
    (i : Fin 2) {f : V ≃ₗ[K] V} (hf : f ∈ supportedFactor hx (splitFourFactors e i)) :
    c * f * c⁻¹ ∈ supportedFactor hx (splitFourFactors e i) := by
  obtain ⟨_, ⟨ℓ, hℓ, rfl⟩, rfl⟩ := hf
  have hdetW : LinearEquiv.det (e (restrictFixedIso c hc)).val = 1 := by
    have hconj : (e (restrictFixedIso c hc)).val =
        (ψ.symm.trans (restrictFixedIso c hc).val).trans ψ :=
      LinearEquiv.ext fun X => he _ X
    rw [hconj, LinearEquiv.det_conj]
    exact det_restrict_fixed hx hp hc hdet _ _
  obtain ⟨z, hz⟩ := exists_rho_of_det_eq_one h2 _ hdetW
  set f' := (fixedBlockEquiv hx).symm ℓ with hf'
  have hmem : c * f'.1 * c⁻¹ ∈ supportedBlock Q x (X - 1) := conj_mem_supportedBlock hc f'.2
  refine ⟨⟨_, hmem⟩, ⟨fixedBlockEquiv hx ⟨_, hmem⟩, ?_,
    (fixedBlockEquiv hx).symm_apply_apply _⟩, rfl⟩
  rw [fixedBlockEquiv_conj hx hc f', hf', MulEquiv.apply_symm_apply]
  exact conj_mem_splitFourFactors e hz i hℓ

theorem supportedFactor_family (hx : OddOrderIsometry Q p x) {n : ℕ}
    (L : Fin n →
      Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    (hsup : (⨆ i, L i) =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    (hL : ∀ i, CFSG.IsQuasisimple ↥(L i) ∧
      L i ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ∧
      ((L i).subgroupOf (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype)))).Normal) :
    (⨆ i, supportedFactor hx (L i)) = supportedFixedDerived Q x ∧
      ∀ i, CFSG.IsQuasisimple ↥(supportedFactor hx (L i)) ∧
        supportedFactor hx (L i) ≤ supportedFixedDerived Q x ∧
        ((supportedFactor hx (L i)).subgroupOf (supportedFixedDerived Q x)).Normal := by
  set φ := (fixedBlockEquiv hx).symm.toMonoidHom with hφ
  set ι := (supportedBlock Q x (X - 1)).subtype with hι
  have hmap : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))).map φ = commutator ↥(supportedBlock Q x (X - 1)) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (fixedBlockEquiv hx).symm.surjective]
    rfl
  have hSFD : ((commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace x).subtype))).map φ).map ι = supportedFixedDerived Q x := by
    rw [hmap, hι, Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  have hle : ∀ i, supportedFactor hx (L i) ≤ supportedFixedDerived Q x := fun i => by
    rw [← hSFD]
    exact Subgroup.map_mono (Subgroup.map_mono (hL i).2.1)
  refine ⟨?_, fun i => ⟨?_, hle i, ?_⟩⟩
  · simp only [supportedFactor]
    rw [← hφ, ← hι, ← Subgroup.map_iSup, ← Subgroup.map_iSup, hsup, hSFD]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (((L i).equivMapOfInjective φ (fixedBlockEquiv hx).symm.injective).trans
        (((L i).map φ).equivMapOfInjective ι (supportedBlock Q x (X - 1)).subtype_injective))
      (hL i).1
  · rw [Subgroup.normal_subgroupOf_iff (hle i)]
    rintro _ k ⟨_, ⟨l, hl, rfl⟩, rfl⟩ hk
    rw [← hSFD] at hk
    obtain ⟨_, ⟨m, hm, rfl⟩, rfl⟩ := hk
    have h1 := (Subgroup.normal_subgroupOf_iff (hL i).2.1).mp (hL i).2.2 l m hl hm
    refine ⟨φ (m * l * m⁻¹), ⟨m * l * m⁻¹, h1, rfl⟩, ?_⟩
    show ι (φ (m * l * m⁻¹)) = ι (φ m) * ι (φ l) * (ι (φ m))⁻¹
    simp only [map_mul, map_inv]

end Transport

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
