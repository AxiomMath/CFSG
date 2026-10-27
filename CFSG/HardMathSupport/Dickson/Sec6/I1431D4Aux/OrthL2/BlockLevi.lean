module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Levi
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 QuadraticMap
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem eichler_pow_nsmul {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) (n : ℕ) :
    eichler Q u w ^ n = eichler Q u (n • w) := by
  induction n with
  | zero => simp [eichler_zero_right]
  | succ n ih =>
    have hnw : polar Q u (n • w) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, polar_smul_right_eq, huw, mul_zero]
    rw [pow_succ, ih, succ_nsmul, eichler_mul hnw huw]

theorem eichler_pow_ringChar (u w : V) : eichler Q u w ^ ringChar K = 1 := by
  by_cases hc : Q u = 0 ∧ polar Q u w = 0
  · rw [eichler_pow_nsmul hc.1 hc.2]
    have : ringChar K • w = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K (ringChar K), zero_smul]
    rw [this, eichler_zero_right]
  · rw [eichler_of_not hc, one_pow]

theorem eichler_mem_supportedBlock {p : ℕ} (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {u w : V}
    (hu : u ∈ orbitSpace x.toLinearMap h) (hw : w ∈ orbitSpace x.toLinearMap h)
    (hcomm : eichler Q (x u) (x w) = eichler Q u w) :
    eichler Q u w ∈ supportedBlock Q x h := by
  rw [mem_supportedBlock]
  refine ⟨mem_isometryCentralizer.mpr ⟨?_, ?_⟩, ?_⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (eichler_mem_orthogonalGroup Q u w)
  · intro v
    have h1 := eichler_conj hx.mem u w
    rw [hcomm] at h1
    have h2 : x * eichler Q u w = eichler Q u w * x := by
      calc x * eichler Q u w = x * eichler Q u w * x⁻¹ * x := by group
        _ = eichler Q u w * x := by rw [h1]
    exact (congrArg (fun f : V ≃ₗ[K] V => f v) h2).symm
  · intro r hr
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm]; exact hx.polar_orbit_others hh hu hr
    · rw [polar_comm]; exact hx.polar_orbit_others hh hw hr

theorem Q_eq_zero_of_eigen {p : ℕ} (hx : OddOrderIsometry Q p x) {v : V} {ω : K}
    (hv : x v = ω • v) (hω : ω ^ 2 ≠ 1) : Q v = 0 := by
  have h1 : Q (x v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem v
  rw [hv, map_smul_eq_sq] at h1
  have h2 : (ω ^ 2 - 1) * Q v = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hω)

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem eichler_mem_specialBlock {p : ℕ} (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {u w : V}
    (hu : u ∈ orbitSpace x.toLinearMap h) (hw : w ∈ orbitSpace x.toLinearMap h)
    (hcomm : eichler Q (x u) (x w) = eichler Q u w) :
    eichler Q u w ∈ specialBlock Q x h := by
  have hS := eichler_mem_supportedBlock hx hh hu hw hcomm
  rw [mem_specialBlock]
  refine ⟨hS, ?_⟩
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Fact (ringChar K).Prime := by
    haveI := Fintype.ofFinite K
    obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
    exact ⟨hp⟩
  haveI : CharP (AdjoinRoot h) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective (ringChar K)
  set g : ↥(supportedBlock Q x h) := ⟨eichler Q u w, hS⟩ with hgdef
  have hg : g ^ ringChar K = 1 := Subtype.ext (eichler_pow_ringChar u w)
  have h1 : (blockDet Q x h g) ^ ringChar K = 1 := by rw [← map_pow, hg, map_one]
  have h2 : (blockDet Q x h g - 1) ^ ringChar K = 0 := by
    rw [sub_pow_char, h1, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : (ringChar K).Prime).ne_zero |>.mp h2)

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

noncomputable def thetaSL (x : V ≃ₗ[K] V) (h : K[X])
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
    SL(2, K) →* SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
  (Matrix.SpecialLinearGroup.toLin_equiv bE).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (algebraMap K (AdjoinRoot h)))

variable {h : K[X]}

theorem thetaSL_apply (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (m : SL(2, K)) (j : Fin 2) :
    (thetaSL x h bE m).1 (bE j) = ∑ i, algebraMap K (AdjoinRoot h) (m i j) • bE i := by
  have h1 := Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq bE
    (Matrix.SpecialLinearGroup.map (algebraMap K (AdjoinRoot h)) m)
  have h2 := LinearMap.congr_fun h1 (bE j)
  change _ = _ at h2
  rw [Matrix.toLin_self] at h2
  exact h2

theorem sl_ext_basis
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    {u v : SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h)}
    (huv : ∀ j, u.1 (bE j) = v.1 (bE j)) : u = v := by
  refine Subtype.ext (LinearEquiv.ext fun y => ?_)
  have : u.1.toLinearMap = v.1.toLinearMap :=
    bE.ext (f₁ := u.1.toLinearMap) (f₂ := v.1.toLinearMap) fun j => huv j
  exact LinearMap.congr_fun this y

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}

theorem eichler_upper_apply_fst (A B : HypPair Q) (c : K) :
    eichler Q A.e (c • B.f) A.e = A.e := eichler_apply_self _ _

theorem eichler_upper_apply_snd (A B : HypPair Q) (hAB : A.Orth B) (c : K) :
    eichler Q A.e (c • B.f) B.e = B.e - c • A.e := by
  have hpol : polar Q A.e (c • B.f) = 0 := by rw [polar_smul_right_eq, hAB.ef, mul_zero]
  have h1 : polar Q B.e A.e = 0 := by rw [polar_comm]; exact hAB.ee
  rw [eichler_apply A.Q_e hpol, h1, polar_smul_right_eq, B.polar_ef, zero_smul, add_zero, mul_zero,
    add_zero, mul_one]

theorem eichler_lower_apply_snd (A B : HypPair Q) (c : K) :
    eichler Q B.e (c • A.f) B.e = B.e := eichler_apply_self _ _

theorem eichler_lower_apply_fst (A B : HypPair Q) (hAB : A.Orth B) (c : K) :
    eichler Q B.e (c • A.f) A.e = A.e - c • B.e := by
  have hpol : polar Q B.e (c • A.f) = 0 := by
    rw [polar_smul_right_eq, polar_comm, hAB.fe, mul_zero]
  have h1 : polar Q A.e B.e = 0 := hAB.ee
  rw [eichler_apply B.Q_e hpol, h1, polar_smul_right_eq, A.polar_ef, zero_smul, add_zero, mul_zero,
    add_zero, mul_one]

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}

theorem coe_of_smul_primaryComponent (c : K) (v : primaryComponent x.toLinearMap h) :
    ((AdjoinRoot.of h c • v : primaryComponent x.toLinearMap h) : V) = c • (v : V) :=
  coe_algebraMap_smul_primaryComponent x.toLinearMap h c v

theorem specialToSL_eichler_upper (A B : HypPair Q) (hAB : A.Orth B)
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (hb0 : (bE 0 : V) = A.e) (hb1 : (bE 1 : V) = B.e) (c : K)
    (hmem : eichler Q A.e (c • B.f) ∈ specialBlock Q x h) :
    specialToSL Q x h ⟨eichler Q A.e (c • B.f), hmem⟩ = thetaSL x h bE (sl2Upper K (-c)) := by
  refine sl_ext_basis bE fun j => Subtype.ext ?_
  rw [thetaSL_apply, specialToSL_apply]
  fin_cases j
  · simp [Fin.sum_univ_two, hb0, eichler_upper_apply_fst]
  · simp [Fin.sum_univ_two, hb0, hb1, eichler_upper_apply_snd A B hAB, sub_eq_add_neg,
      coe_algebraMap_smul_primaryComponent,
      coe_of_smul_primaryComponent] <;> abel

theorem specialToSL_eichler_lower (A B : HypPair Q) (hAB : A.Orth B)
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (hb0 : (bE 0 : V) = A.e) (hb1 : (bE 1 : V) = B.e) (c : K)
    (hmem : eichler Q B.e (c • A.f) ∈ specialBlock Q x h) :
    specialToSL Q x h ⟨eichler Q B.e (c • A.f), hmem⟩ = thetaSL x h bE (sl2Lower K (-c)) := by
  refine sl_ext_basis bE fun j => Subtype.ext ?_
  rw [thetaSL_apply, specialToSL_apply]
  fin_cases j
  · simp [Fin.sum_univ_two, hb0, hb1, eichler_lower_apply_fst A B hAB, sub_eq_add_neg,
      coe_algebraMap_smul_primaryComponent,
      coe_of_smul_primaryComponent] <;> abel
  · simp [Fin.sum_univ_two, hb1, eichler_lower_apply_snd]

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}

theorem specialBlock_eq_levi_of {p : ℕ} (hx : OddOrderIsometry Q p x)
    (hh : h ∈ primaryFactors x.toLinearMap) (A B : HypPair Q) (hAB : A.Orth B)
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (hb0 : (bE 0 : V) = A.e) (hb1 : (bE 1 : V) = B.e)
    (hS₁ : ∀ c : K, eichler Q A.e (c • B.f) ∈ specialBlock Q x h)
    (hS₂ : ∀ c : K, eichler Q B.e (c • A.f) ∈ specialBlock Q x h)
    (hsur : ∀ g : ↥(specialBlock Q x h),
      ∃ m : SL(2, K), thetaSL x h bE m = specialToSL Q x h g) :
    specialBlock Q x h = leviV Q A.e B.e A.f B.f := by
  apply le_antisymm
  · intro g hg
    obtain ⟨m, hm⟩ := hsur ⟨g, hg⟩
    have key : ∀ m ∈ Subgroup.closure (Set.range (sl2Upper K) ∪ Set.range (sl2Lower K)),
        ∃ l : ↥(specialBlock Q x h), (l : V ≃ₗ[K] V) ∈ leviV Q A.e B.e A.f B.f ∧
          specialToSL Q x h l = thetaSL x h bE m := by
      intro m hm
      induction hm using Subgroup.closure_induction with
      | mem m hm =>
        rcases hm with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · refine ⟨⟨eichler Q A.e ((-c) • B.f), hS₁ (-c)⟩, ?_, ?_⟩
          · exact Subgroup.subset_closure (Or.inl ⟨-c, rfl⟩)
          · have := specialToSL_eichler_upper A B hAB bE hb0 hb1 (-c) (hS₁ (-c))
            rwa [neg_neg] at this
        · refine ⟨⟨eichler Q B.e ((-c) • A.f), hS₂ (-c)⟩, ?_, ?_⟩
          · exact Subgroup.subset_closure (Or.inr ⟨-c, rfl⟩)
          · have := specialToSL_eichler_lower A B hAB bE hb0 hb1 (-c) (hS₂ (-c))
            rwa [neg_neg] at this
      | one => exact ⟨1, Subgroup.one_mem _, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨la, hla, hsa⟩ := ha
        obtain ⟨lb, hlb, hsb⟩ := hb
        exact ⟨la * lb, Subgroup.mul_mem _ hla hlb, by rw [map_mul, map_mul, hsa, hsb]⟩
      | inv a _ ha =>
        obtain ⟨l, hl, hs⟩ := ha
        exact ⟨l⁻¹, Subgroup.inv_mem _ hl, by rw [map_inv, map_inv, hs]⟩
    obtain ⟨l, hl, hs⟩ := key m (by rw [sl2_closure_upper_lower]; exact Subgroup.mem_top _)
    have hlg : l = ⟨g, hg⟩ := hx.specialToSL_injective hh (by rw [hs, hm])
    rw [hlg] at hl
    exact hl
  · rw [leviV, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [hS₁ c, hS₂ c]

end

section

variable {K : Type} [Field K]

theorem reciprocalPolynomial_cyclotomic_three :
    reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1 := by
  have hdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hc : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by simp
  unfold reciprocalPolynomial Polynomial.reverse
  rw [hdeg, hc]
  have h1 : (reflect 2 X : K[X]) = X := by
    have := reflect_monomial (R := K) 2 1
    simpa [revAt_le] using this
  simp [reflect_add, h1]
  ring

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}

theorem natDegree_eq_one_of_paired (hx : OddOrderIsometry Q 3 x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) : h.natDegree = 1 := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd := hx.dvd_X_pow_sub_one hh
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
  rw [hfac] at hdvd
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
  · exact absurd (eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one h1)) hne1
  · have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
    have hΦmon : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
    have hle : h.natDegree ≤ 2 := by
      have := natDegree_le_of_dvd h2 hΦmon.ne_zero
      omega
    have hpos : 0 < h.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
    by_contra hne1'
    have h2' : h.natDegree = 2 := by omega
    have heq : h = X ^ 2 + X + 1 :=
      (eq_of_monic_of_dvd_of_natDegree_le hmon hΦmon h2 (by omega)).symm
    exact hne (by rw [heq, reciprocalPolynomial_cyclotomic_three])

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}

theorem exists_eigen_of_natDegree_one (hx : OddOrderIsometry Q 3 x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (hdeg : h.natDegree = 1) :
    ∃ ω : K, ω ≠ 0 ∧ ω ^ 2 ≠ 1 ∧ (∀ v ∈ primaryComponent x.toLinearMap h, x v = ω • v) ∧
      (∀ w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h), x w = ω⁻¹ • w) := by
  have hmon := monic_of_mem_primaryFactors hh
  have h0 : h.coeff 0 ≠ 0 := hx.coeff_zero_ne hh
  set ω : K := -(h.coeff 0) with hω
  have hform : h = X - C ω := by
    calc h = X + C (h.coeff 0) := hmon.eq_X_add_C hdeg
      _ = X - C ω := by rw [hω, C_neg, sub_neg_eq_add]
  have hω0 : ω ≠ 0 := neg_ne_zero.mpr h0
  have hω3 : ω ^ 3 = 1 := by
    have hdvd := hx.dvd_X_pow_sub_one hh
    rw [hform, dvd_iff_isRoot] at hdvd
    have := hdvd
    simpa [IsRoot, sub_eq_zero] using this
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    have : ω = 1 := by
      calc ω = ω * ω ^ 2 := by rw [h2, mul_one]
        _ = ω ^ 3 := by ring
        _ = 1 := hω3
    exact hne1 (by rw [hform, this, C_1])
  refine ⟨ω, hω0, hω2, fun v hv => ?_, fun w hw => ?_⟩
  · have := mem_primaryComponent.mp hv
    rw [hform] at this
    simpa [sub_eq_zero] using this
  · have h1 := (mem_primaryComponent_reciprocalPolynomial (x := x) h0).mp hw
    rw [hform] at h1
    have h2 : x.symm w = ω • w := by simpa [sub_eq_zero] using h1
    have h3 : w = ω • x w := by
      have := congrArg x h2
      rw [LinearEquiv.apply_symm_apply, map_smul] at this
      exact this
    calc x w = ω⁻¹ • (ω • x w) := by rw [smul_smul, inv_mul_cancel₀ hω0, one_smul]
      _ = ω⁻¹ • w := by rw [← h3]

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}

theorem thetaSL_surjective (hsurj : Function.Surjective (algebraMap K (AdjoinRoot h)))
    (hinj : Function.Injective (algebraMap K (AdjoinRoot h)))
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h)) :
    Function.Surjective (thetaSL x h bE) := by
  intro γ
  set X : SL(2, AdjoinRoot h) := (Matrix.SpecialLinearGroup.toLin_equiv bE).symm γ with hX
  choose f hf using hsurj
  let M' : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => f (X i j)
  have hmap : (algebraMap K (AdjoinRoot h)).mapMatrix M' = (X : Matrix (Fin 2) (Fin 2) _) := by
    ext i j
    exact hf (X i j)
  have hdet : M'.det = 1 := by
    apply hinj
    rw [RingHom.map_det, hmap, map_one]
    exact X.2
  refine ⟨⟨M', hdet⟩, ?_⟩
  have h1 : Matrix.SpecialLinearGroup.map (algebraMap K (AdjoinRoot h)) ⟨M', hdet⟩ = X :=
    Subtype.ext hmap
  show Matrix.SpecialLinearGroup.toLin_equiv bE
    (Matrix.SpecialLinearGroup.map (algebraMap K (AdjoinRoot h)) ⟨M', hdet⟩) = γ
  rw [h1, hX, MulEquiv.apply_symm_apply]

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {h : K[X]}

theorem specialBlock_eq_levi_paired (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q 3 x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : primaryMultiplicity x.toLinearMap h = 2) :
    ∃ A B : HypPair Q, A.Orth B ∧
      Submodule.span K {A.e, A.f, B.e, B.f} = orbitSpace x.toLinearMap h ∧
      specialBlock Q x h = leviV Q A.e B.e A.f B.f := by
  classical
  have _hQ := hQ
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hdeg := natDegree_eq_one_of_paired hx hh hne1 hne
  obtain ⟨ω, hω0, hω2, heig, heig'⟩ := exists_eigen_of_natDegree_one hx hh hne1 hdeg
  have hfin : finrank K (primaryComponent x.toLinearMap h) = 2 := by
    rw [finrank_primaryComponent, hdeg, one_mul]; exact hm
  have hrank1 : finrank K (AdjoinRoot h) = 1 := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hsurj : Function.Surjective (algebraMap K (AdjoinRoot h)) := by
    intro e
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot h) one_ne_zero).mp
      hrank1 e
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  have hinj : Function.Injective (algebraMap K (AdjoinRoot h)) :=
    (algebraMap K (AdjoinRoot h)).injective
  let eKE : K ≃+* AdjoinRoot h := RingEquiv.ofBijective (algebraMap K (AdjoinRoot h)) ⟨hinj, hsurj⟩
  let bK : Module.Basis (Fin 2) K (primaryComponent x.toLinearMap h) :=
    Module.finBasisOfFinrankEq K _ hfin
  let bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    bK.mapCoeffs eKE (fun c y => by
      show algebraMap K (AdjoinRoot h) c • y = c • y
      exact algebraMap_smul _ c y)
  have hbE : ∀ j, bE j = bK j := fun j => by simp [bE]
  let Φ : primaryComponent x.toLinearMap (reciprocalPolynomial h) ≃ₗ[K]
      Module.Dual K (primaryComponent x.toLinearMap h) :=
    LinearEquiv.ofBijective (pairingHom Q x h).flip (hx.pairing_flip_bijective hh)
  let w : Fin 2 → primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
    fun j => Φ.symm (bK.coord j)
  have hpol : ∀ i j, polar Q (bK i : V) (w j : V) = if i = j then 1 else 0 := by
    intro i j
    have h1 : (pairingHom Q x h).flip (w j) = bK.coord j := Φ.apply_symm_apply (bK.coord j)
    have h2 := LinearMap.congr_fun h1 (bK i)
    rw [LinearMap.flip_apply, pairingHom_apply] at h2
    rw [h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hQeig : ∀ v ∈ primaryComponent x.toLinearMap h, Q v = 0 := fun v hv =>
    Q_eq_zero_of_eigen hx (heig v hv) hω2
  have hω2' : (ω⁻¹) ^ 2 ≠ 1 := by
    intro h1
    apply hω2
    have : (ω ^ 2)⁻¹ = 1 := by rwa [← inv_pow]
    simpa using this
  have hQeig' : ∀ v ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h), Q v = 0 :=
    fun v hv => Q_eq_zero_of_eigen hx (heig' v hv) hω2'
  let A : HypPair Q := ⟨(bK 0 : V), (w 0 : V), hQeig _ (bK 0).2, hQeig' _ (w 0).2,
    by simpa using hpol 0 0⟩
  let B : HypPair Q := ⟨(bK 1 : V), (w 1 : V), hQeig _ (bK 1).2, hQeig' _ (w 1).2,
    by simpa using hpol 1 1⟩
  have hAB : A.Orth B :=
    ⟨hx.polar_eq_zero_of_ne hh hne (bK 0).2 (bK 1).2, by simpa using hpol 0 1,
      by rw [polar_comm]; simpa using hpol 1 0,
      hx.polar_reciprocal_eq_zero_of_ne hh hne (w 0).2 (w 1).2⟩
  have hb0 : (bE 0 : V) = A.e := by rw [hbE]
  have hb1 : (bE 1 : V) = B.e := by rw [hbE]
  have hS₁ : ∀ c : K, eichler Q A.e (c • B.f) ∈ specialBlock Q x h := fun c => by
    refine eichler_mem_specialBlock hx hh (Submodule.mem_sup_left (bK 0).2)
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (w 1).2)) ?_
    show eichler Q (x (bK 0 : V)) (x (c • (w 1 : V))) = eichler Q (bK 0 : V) (c • (w 1 : V))
    rw [heig _ (bK 0).2, map_smul, heig' _ (w 1).2, eichler_smul_left, smul_smul, smul_smul]
    congr 2
    field_simp
  have hS₂ : ∀ c : K, eichler Q B.e (c • A.f) ∈ specialBlock Q x h := fun c => by
    refine eichler_mem_specialBlock hx hh (Submodule.mem_sup_left (bK 1).2)
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (w 0).2)) ?_
    show eichler Q (x (bK 1 : V)) (x (c • (w 0 : V))) = eichler Q (bK 1 : V) (c • (w 0 : V))
    rw [heig _ (bK 1).2, map_smul, heig' _ (w 0).2, eichler_smul_left, smul_smul, smul_smul]
    congr 2
    field_simp
  have hsur := fun g : ↥(specialBlock Q x h) =>
    thetaSL_surjective hsurj hinj bE (specialToSL Q x h g)
  refine ⟨A, B, hAB, ?_, specialBlock_eq_levi_of hx hh A B hAB bE hb0 hb1 hS₁ hS₂ hsur⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Submodule.mem_sup_left (bK 0).2
    · exact Submodule.mem_sup_right (w 0).2
    · exact Submodule.mem_sup_left (bK 1).2
    · exact Submodule.mem_sup_right (w 1).2
  · refine sup_le ?_ ?_
    · intro u hu
      have hsum : (∑ i, ((bK.repr ⟨u, hu⟩ i • bK i : primaryComponent x.toLinearMap h) : V)) =
          u := by
        have := congrArg Subtype.val (bK.sum_repr ⟨u, hu⟩)
        rw [Submodule.coe_sum] at this
        exact this
      rw [← hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      fin_cases i <;> simp [A, B]
    · intro u hu
      have hu' : (⟨u, hu⟩ : primaryComponent x.toLinearMap (reciprocalPolynomial h)) =
          ∑ i, (Φ ⟨u, hu⟩) (bK i) • w i := by
        calc (⟨u, hu⟩ : primaryComponent x.toLinearMap (reciprocalPolynomial h))
            = Φ.symm (Φ ⟨u, hu⟩) := (Φ.symm_apply_apply _).symm
          _ = Φ.symm (∑ i, (Φ ⟨u, hu⟩) (bK i) • bK.coord i) := by
            rw [bK.sum_dual_apply_smul_coord]
          _ = ∑ i, (Φ ⟨u, hu⟩) (bK i) • w i := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => map_smul Φ.symm _ _
      have hsum : u = ∑ i, (((Φ ⟨u, hu⟩) (bK i) • w i :
          primaryComponent x.toLinearMap (reciprocalPolynomial h)) : V) := by
        have := congrArg Subtype.val hu'
        rw [Submodule.coe_sum] at this
        exact this
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      fin_cases i <;> simp [A, B]

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem eichler_mem_supportedBlock_fixed {p : ℕ} (hx : OddOrderIsometry Q p x) {u w : V}
    (hu : u ∈ fixedSpace x) (hw : w ∈ fixedSpace x) :
    eichler Q u w ∈ supportedBlock Q x (X - 1) := by
  rw [mem_supportedBlock]
  refine ⟨mem_isometryCentralizer.mpr ⟨?_, ?_⟩, ?_⟩
  · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (eichler_mem_orthogonalGroup Q u w)
  · intro v
    have h1 := eichler_conj hx.mem u w
    rw [mem_fixedSpace.mp hu, mem_fixedSpace.mp hw] at h1
    have h2 : x * eichler Q u w = eichler Q u w * x := by
      calc x * eichler Q u w = x * eichler Q u w * x⁻¹ * x := by group
        _ = eichler Q u w * x := by rw [h1]
    exact (congrArg (fun f : V ≃ₗ[K] V => f v) h2).symm
  · intro r hr
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · rw [polar_comm]; exact hx.fixed_others.2 u hu r hr
    · rw [polar_comm]; exact hx.fixed_others.2 w hw r hr

section Coordinates

theorem eichler_left_upper (A B : HypPair Q) (hAB : A.Orth B) (X : Matrix (Fin 2) (Fin 2) K)
    (c : K) :
    eichler Q A.e (c • B.e) (matrixToOriginal A B X) =
      matrixToOriginal A B ((sl2Upper K c : Matrix (Fin 2) (Fin 2) K) * X) := by
  have hpol : polar Q A.e (c • B.e) = 0 := by rw [polar_smul_right_eq, hAB.ee, mul_zero]
  have hQ : Q (c • B.e) = 0 := by rw [map_smul_eq_sq, B.Q_e, mul_zero]
  obtain ⟨h1, h2, h3, h4⟩ := matrixToOriginal_polar A B hAB X
  rw [eichler_apply A.Q_e hpol, polar_smul_right_eq, h3, h4, hQ]
  simp only [matrixToOriginal_apply, coe_sl2Upper, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  module

theorem eichler_left_lower (A B : HypPair Q) (hAB : A.Orth B) (X : Matrix (Fin 2) (Fin 2) K)
    (c : K) :
    eichler Q B.f (c • A.f) (matrixToOriginal A B X) =
      matrixToOriginal A B ((sl2Lower K c : Matrix (Fin 2) (Fin 2) K) * X) := by
  have hpol : polar Q B.f (c • A.f) = 0 := by rw [polar_smul_right_eq, hAB.symm.ff, mul_zero]
  have hQ : Q (c • A.f) = 0 := by rw [map_smul_eq_sq, A.Q_f, mul_zero]
  obtain ⟨h1, h2, h3, h4⟩ := matrixToOriginal_polar A B hAB X
  rw [eichler_apply B.Q_f hpol, polar_smul_right_eq, h1, h2, hQ]
  simp only [matrixToOriginal_apply, coe_sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  module

theorem eichler_right_lower (A B : HypPair Q) (hAB : A.Orth B) (X : Matrix (Fin 2) (Fin 2) K)
    (c : K) :
    eichler Q A.e (c • B.f) (matrixToOriginal A B X) =
      matrixToOriginal A B (X * (sl2Lower K (-c) : Matrix (Fin 2) (Fin 2) K)) := by
  have hpol : polar Q A.e (c • B.f) = 0 := by rw [polar_smul_right_eq, hAB.ef, mul_zero]
  have hQ : Q (c • B.f) = 0 := by rw [map_smul_eq_sq, B.Q_f, mul_zero]
  obtain ⟨h1, h2, h3, h4⟩ := matrixToOriginal_polar A B hAB X
  rw [eichler_apply A.Q_e hpol, polar_smul_right_eq, h2, h3, hQ]
  simp only [matrixToOriginal_apply, coe_sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  module

theorem eichler_right_upper (A B : HypPair Q) (hAB : A.Orth B) (X : Matrix (Fin 2) (Fin 2) K)
    (c : K) :
    eichler Q B.e (c • A.f) (matrixToOriginal A B X) =
      matrixToOriginal A B (X * (sl2Upper K (-c) : Matrix (Fin 2) (Fin 2) K)) := by
  have hpol : polar Q B.e (c • A.f) = 0 := by
    rw [polar_smul_right_eq, polar_comm, hAB.fe, mul_zero]
  have hQ : Q (c • A.f) = 0 := by rw [map_smul_eq_sq, A.Q_f, mul_zero]
  obtain ⟨h1, h2, h3, h4⟩ := matrixToOriginal_polar A B hAB X
  rw [eichler_apply B.Q_e hpol, polar_smul_right_eq, h1, h4, hQ]
  simp only [matrixToOriginal_apply, coe_sl2Upper, Matrix.mul_apply, Fin.sum_univ_two]
  simp
  module

end Coordinates

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem range_le_of_sl2_generators {G : Type*} [Group G] (f : SL(2, K) →* G) (H : Subgroup G)
    (hU : ∀ c, f (sl2Upper K c) ∈ H) (hL : ∀ c, f (sl2Lower K c) ∈ H) : f.range ≤ H := by
  rw [MonoidHom.range_eq_map, ← sl2_closure_upper_lower, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨M, (⟨c, rfl⟩ | ⟨c, rfl⟩), rfl⟩
  exacts [hU c, hL c]

theorem supportedFixedDerived_eq_levi (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q 3 x) (A B : HypPair Q) (hAB : A.Orth B)
    (hspan : Submodule.span K {A.e, A.f, B.e, B.f} = fixedSpace x) (hK : Nat.card K ≠ 2) :
    supportedFixedDerived Q x = leviV Q A.e B.e A.f B.f ⊔ leviV Q A.e B.f A.f B.e := by
  classical
  have _hQ := hQ
  have hK3 : Nat.card K ≠ 3 := by
    intro h3
    apply hx.cast_ne_zero
    haveI := Fintype.ofFinite K
    have := FiniteField.cast_card_eq_zero K
    rwa [← Nat.card_eq_fintype_card, h3] at this
  let m : Matrix (Fin 2) (Fin 2) K →ₗ[K] V := matrixToOriginal A B
  have hinj : Function.Injective m := matrixToOriginal_injective A B hAB
  have hrange : LinearMap.range m = fixedSpace x := by
    rw [← hspan]
    apply le_antisymm
    · rintro _ ⟨X, rfl⟩
      rw [show m X = matrixToOriginal A B X from rfl, matrixToOriginal_apply]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨!![1, 0; 0, 0], by simp [m, matrixToOriginal_apply]⟩
      · exact ⟨!![0, 0; 0, 1], by simp [m, matrixToOriginal_apply]⟩
      · exact ⟨!![0, 1; 0, 0], by simp [m, matrixToOriginal_apply]⟩
      · exact ⟨!![0, 0; -1, 0], by simp [m, matrixToOriginal_apply]⟩
  let ePsi : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] fixedSpace x :=
    (LinearEquiv.ofInjective m hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hePsi : ∀ X, ((ePsi X : fixedSpace x) : V) = m X := fun X => rfl
  let psi : (Q.comp (fixedSpace x).subtype).IsometryEquiv (determinantForm K) :=
    { toLinearEquiv := ePsi.symm
      map_app' := fun w => by
        obtain ⟨X, rfl⟩ := ePsi.surjective w
        show determinantForm K (ePsi.symm (ePsi X)) = Q ((ePsi X : fixedSpace x) : V)
        rw [LinearEquiv.symm_apply_apply, hePsi, determinantForm_apply]
        exact (matrixToOriginal_form A B hAB X).symm }
  let Θ := TauCeti.QuadraticMap.orthogonalGroupCongr psi
  let Φ : ↥(supportedBlock Q x (X - 1)) ≃* DeterminantIsometries K :=
    (fixedBlockEquiv hx).trans Θ
  have hΦ : ∀ (g : ↥(supportedBlock Q x (X - 1)))
      (T : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K),
      (∀ X, g.1 (m X) = m (T X)) → ∀ X, (Φ g).val X = T X := by
    intro g T hT X
    have h1 : (Φ g).val X = ePsi.symm ((fixedBlockEquiv hx g).val (ePsi X)) :=
      TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply psi (fixedBlockEquiv hx g) X
    rw [h1]
    apply ePsi.injective
    rw [LinearEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [coe_fixedBlockEquiv, hePsi, hePsi]
    exact hT X
  have hsFD : ∀ g : V ≃ₗ[K] V, g ∈ supportedFixedDerived Q x ↔
      ∃ hg : g ∈ supportedBlock Q x (X - 1), Φ ⟨g, hg⟩ ∈ specialImage K := by
    intro g
    rw [mem_supportedFixedDerived]
    refine exists_congr fun hg => ?_
    have e1 : restrictFixed Q x ⟨g, hg⟩ =
        ((fixedBlockEquiv hx ⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (fixedSpace x).subtype))) : fixedSpace x ≃ₗ[K] fixedSpace x) := rfl
    rw [e1, orthDerived, ← Subgroup.map_subtype_commutator]
    have hmem : ∀ y : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)),
        (y : fixedSpace x ≃ₗ[K] fixedSpace x) ∈
          (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))).map
            (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype ↔
          y ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
            (Q.comp (fixedSpace x).subtype)) := fun y =>
      Subgroup.mem_map_iff_mem (Subgroup.subtype_injective
        (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    refine (hmem _).trans ?_
    have hcomm : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace x).subtype))).map Θ.toMonoidHom =
          commutator (DeterminantIsometries K) := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr Θ.surjective, ← commutator_def]
    rw [← determinant_commutator_eq hK hK3, ← hcomm]
    exact (Subgroup.mem_map_iff_mem Θ.injective).symm
  have hAe : A.e ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hAf : A.f ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hBe : B.e ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hBf : B.f ∈ fixedSpace x := hspan ▸ Submodule.subset_span (by simp)
  have hm₁ : ∀ c : K, eichler Q A.e (c • B.f) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hAe (Submodule.smul_mem _ c hBf)
  have hm₂ : ∀ c : K, eichler Q B.e (c • A.f) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hBe (Submodule.smul_mem _ c hAf)
  have hm₃ : ∀ c : K, eichler Q A.e (c • B.e) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hAe (Submodule.smul_mem _ c hBe)
  have hm₄ : ∀ c : K, eichler Q B.f (c • A.f) ∈ supportedBlock Q x (X - 1) := fun c =>
    eichler_mem_supportedBlock_fixed hx hBf (Submodule.smul_mem _ c hAf)
  have hΦ₁ : ∀ c : K, Φ ⟨eichler Q A.e (c • B.f), hm₁ c⟩ = specialRho (1, sl2Lower K c) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => X * (sl2Lower K (-c) : Matrix (Fin 2) (Fin 2) K))
      (fun X => eichler_right_lower A B hAB X c), specialRho_apply]
    simp [sl2Lower_neg]
  have hΦ₂ : ∀ c : K, Φ ⟨eichler Q B.e (c • A.f), hm₂ c⟩ = specialRho (1, sl2Upper K c) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => X * (sl2Upper K (-c) : Matrix (Fin 2) (Fin 2) K))
      (fun X => eichler_right_upper A B hAB X c), specialRho_apply]
    simp [sl2Upper_neg]
  have hΦ₃ : ∀ c : K, Φ ⟨eichler Q A.e (c • B.e), hm₃ c⟩ = specialRho (sl2Upper K c, 1) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => (sl2Upper K c : Matrix (Fin 2) (Fin 2) K) * X)
      (fun X => eichler_left_upper A B hAB X c), specialRho_apply]
    simp
  have hΦ₄ : ∀ c : K, Φ ⟨eichler Q B.f (c • A.f), hm₄ c⟩ = specialRho (sl2Lower K c, 1) := by
    intro c
    refine Subtype.ext (LinearEquiv.ext fun X => ?_)
    rw [hΦ _ (fun X => (sl2Lower K c : Matrix (Fin 2) (Fin 2) K) * X)
      (fun X => eichler_left_lower A B hAB X c), specialRho_apply]
    simp
  have hgen : ∀ (g : V ≃ₗ[K] V) (hg : g ∈ supportedBlock Q x (X - 1)) (z : SL(2, K) × SL(2, K)),
      Φ ⟨g, hg⟩ = specialRho z → g ∈ supportedFixedDerived Q x := fun g hg z hz =>
    (hsFD g).mpr ⟨hg, by rw [hz]; exact ⟨z, rfl⟩⟩
  apply le_antisymm
  · intro g hg
    obtain ⟨hgF, hΦg⟩ := (hsFD g).mp hg
    set H : Subgroup (DeterminantIsometries K) := Subgroup.map Φ.toMonoidHom
      (Subgroup.comap (supportedBlock Q x (X - 1)).subtype
        (leviV Q A.e B.e A.f B.f ⊔ leviV Q A.e B.f A.f B.e)) with hH
    have hmemH : specialImage K ≤ H := by
      rw [← determinantFactors_sup]
      refine sup_le ?_ ?_
      · refine range_le_of_sl2_generators (specialRho.comp (MonoidHom.inl _ _)) H ?_ ?_
        · intro c
          exact ⟨⟨eichler Q A.e (c • B.e), hm₃ c⟩,
            Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)), hΦ₃ c⟩
        · intro c
          exact ⟨⟨eichler Q B.f (c • A.f), hm₄ c⟩,
            Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)), hΦ₄ c⟩
      · refine range_le_of_sl2_generators (specialRho.comp (MonoidHom.inr _ _)) H ?_ ?_
        · intro c
          exact ⟨⟨eichler Q B.e (c • A.f), hm₂ c⟩,
            Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)), hΦ₂ c⟩
        · intro c
          exact ⟨⟨eichler Q A.e (c • B.f), hm₁ c⟩,
            Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)), hΦ₁ c⟩
    obtain ⟨l, hl, hΦl⟩ := hmemH hΦg
    have hlg : l = ⟨g, hgF⟩ := Φ.injective hΦl
    rw [hlg] at hl
    exact hl
  · refine sup_le ?_ ?_
    · rw [leviV, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hgen _ (hm₁ c) (1, sl2Lower K c) (hΦ₁ c)
      · exact hgen _ (hm₂ c) (1, sl2Upper K c) (hΦ₂ c)
    · rw [leviV, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hgen _ (hm₃ c) (sl2Upper K c, 1) (hΦ₃ c)
      · exact hgen _ (hm₄ c) (sl2Lower K c, 1) (hΦ₄ c)

end

section

section FiniteFieldE

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] [Finite E]

theorem trace_surjective_ff : Function.Surjective (Algebra.trace K E) := by
  have : Module.Finite K E := Module.Finite.of_finite
  exact Algebra.trace_surjective K E

theorem algebraMap_trace_eq_add (hd : finrank K E = 2) (z : E) :
    algebraMap K E (Algebra.trace K E z) = z + z ^ Nat.card K := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hd]
  simp [Finset.sum_range_succ]

theorem algebraMap_norm_eq_mul (hd : finrank K E = 2) (z : E) :
    algebraMap K E (Algebra.norm K z) = z * z ^ Nat.card K := by
  rw [FiniteField.algebraMap_norm_eq_pow, Module.natCard_eq_pow_finrank (K := K) (V := E), hd]
  have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  obtain ⟨k, hk⟩ : ∃ k, Nat.card K = k + 2 := ⟨Nat.card K - 2, by omega⟩
  rw [hk]
  have h1 : ((k + 2) ^ 2 - 1) / (k + 2 - 1) = k + 2 + 1 := by
    apply Nat.div_eq_of_eq_mul_left (by omega)
    rw [show (k + 2) ^ 2 = (k + 2 + 1) * (k + 2 - 1) + 1 by
      obtain ⟨j, rfl⟩ : ∃ j, k = j := ⟨k, rfl⟩
      rw [show k + 2 - 1 = k + 1 by omega]; ring]
    simp
  rw [h1, pow_succ']

theorem exists_algebraMap_of_pow_card_eq (hd : finrank K E = 2) {z : E}
    (hz : z ^ Nat.card K = z) : ∃ k : K, algebraMap K E k = z := by
  have hz' : z ∈ fixedSubfield K E 1 := (mem_fixedSubfield K E 1 z).mpr (by simpa using hz)
  have hbot : fixedSubfield K E 1 = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp (finrank_fixedSubfield K E (d := 1) (by simpa using hd))
  rw [hbot] at hz'
  exact IntermediateField.mem_bot.mp hz'

end FiniteFieldE

end

section

section Hermitian

variable {K E M : Type} [Field K] [Finite K] [Field E] [Algebra K E] [Finite E]
  [AddCommGroup M] [Module E M]

theorem exists_hermitian_isotropic_pair (hd : finrank K E = 2) (σ : E →+* E)
    (hσ : ∀ z, σ z = z ^ Nat.card K) (B : M →ₛₗ[σ] M →ₗ[E] E)
    (hherm : ∀ u w, B w u = σ (B u w)) (hnd : ∀ u, (∀ w, B u w = 0) → u = 0)
    (hM : finrank E M = 2) (ε : E) :
    ∃ a b : M, B a a = 0 ∧ B b b = 0 ∧ B a b = ε := by
  classical
  have hcardE : Nat.card E = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hd]
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← hcardE]
    haveI := Fintype.ofFinite E
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card z
  have hfix : ∀ z, σ z = z → ∃ k : K, algebraMap K E k = z := fun z hz =>
    exists_algebraMap_of_pow_card_eq hd (by rw [← hσ]; exact hz)
  have hdiag : ∀ u, σ (B u u) = B u u := fun u => (hherm u u).symm
  have hl : ∀ (c : E) (u w : M), B (c • u) w = σ c * B u w := fun c u w => by
    rw [map_smulₛₗ]; rfl
  have hr : ∀ (c : E) (u w : M), B u (c • w) = c * B u w := fun c u w => by
    rw [map_smul]; rfl
  have hI : ∃ a : M, a ≠ 0 ∧ B a a = 0 := by
    by_contra hno
    push Not at hno
    haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := E) (by omega)
    obtain ⟨u₁, hu₁⟩ := exists_ne (0 : M)
    have hα0 : B u₁ u₁ ≠ 0 := hno u₁ hu₁
    have hex : ∃ w : M, ∀ c : E, c • u₁ ≠ w := by
      by_contra hcon
      push Not at hcon
      have h1 : finrank E M = 1 := (finrank_eq_one_iff_of_nonzero' u₁ hu₁).mpr hcon
      omega
    obtain ⟨w, hw⟩ := hex
    set u₂ : M := w - ((B u₁ u₁)⁻¹ * B u₁ w) • u₁ with hu₂def
    have hu₂ : u₂ ≠ 0 := fun h0 => hw ((B u₁ u₁)⁻¹ * B u₁ w) (sub_eq_zero.mp h0).symm
    have hB12 : B u₁ u₂ = 0 := by
      rw [hu₂def, map_sub, hr, sub_eq_zero]
      field_simp
    have hB21 : B u₂ u₁ = 0 := by rw [hherm, hB12, map_zero]
    have hβ0 : B u₂ u₂ ≠ 0 := hno u₂ hu₂
    obtain ⟨γ₀, hγ₀⟩ := hfix (-(B u₂ u₂ / B u₁ u₁)) (by
      rw [map_neg, map_div₀, hdiag, hdiag])
    have hγ0 : -(B u₂ u₂ / B u₁ u₁) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hβ0 hα0)
    have hγ₀0 : γ₀ ≠ 0 := fun h0 => hγ0 (by rw [← hγ₀, h0, map_zero])
    obtain ⟨s, hs⟩ := FiniteField.norm_surjective K E γ₀
    have hsnorm : s * σ s = -(B u₂ u₂ / B u₁ u₁) := by
      rw [← hγ₀, ← hs, algebraMap_norm_eq_mul hd, hσ]
    set v : M := s • u₁ + u₂ with hvdef
    have hvv : B v v = 0 := by
      simp only [hvdef, map_add, LinearMap.add_apply, hl, hr, hB12, hB21, mul_zero, add_zero,
        zero_add]
      have : σ s * (s * B u₁ u₁) = (s * σ s) * B u₁ u₁ := by ring
      rw [this, hsnorm]
      field_simp
      ring
    have hv0 : v ≠ 0 := by
      intro h0
      have h1 : B u₁ v = 0 := by rw [h0, map_zero]
      rw [hvdef, map_add, hr, hB12, add_zero] at h1
      have hs0 : s = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h hα0
      apply hγ0
      rw [← hsnorm, hs0, zero_mul]
    exact hno v hv0 hvv
  obtain ⟨a, ha0, haa⟩ := hI
  have hex : ∃ w, B a w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha0 (hnd a hcon)
  obtain ⟨w, hw⟩ := hex
  set v : M := (B a w)⁻¹ • w with hvdef
  have hav : B a v = 1 := by
    rw [hvdef, hr, inv_mul_cancel₀ hw]
  have hκ : σ (B v v) = B v v := hdiag v
  obtain ⟨κ₀, hκ₀⟩ := hfix _ hκ
  obtain ⟨t, ht⟩ := trace_surjective_ff (K := K) (E := E) (-κ₀)
  have htt : t + σ t = -(B v v) := by
    have := algebraMap_trace_eq_add hd t
    rw [ht, map_neg, hκ₀] at this
    rw [hσ]
    linear_combination -this
  set v₁ : M := v + t • a with hv₁def
  have hav₁ : B a v₁ = 1 := by
    rw [hv₁def, map_add, hr t a a, haa, mul_zero, add_zero, hav]
  have hvv₁ : B v₁ v₁ = 0 := by
    have hva : B v a = 1 := by rw [hherm, hav, map_one]
    simp only [hv₁def, map_add, LinearMap.add_apply, hl, hr, hva, hav, haa, mul_zero, add_zero]
    linear_combination htt
  refine ⟨a, ε • v₁, haa, ?_, ?_⟩
  · rw [hl, hr, hvv₁, mul_zero, mul_zero]
  · rw [hr, hav₁, mul_one]

end Hermitian

end

section

section UnitaryEntries

variable {E : Type} [Field E]

theorem entries_fixed_of_unitary (σ : E →+* E) {p r s t : E}
    (e1 : σ p * r = σ r * p) (e2 : σ s * t = σ t * s) (e3 : σ p * t - σ r * s = 1)
    (e5 : σ s * r - σ t * p = -1) (hdet : p * t - r * s = 1) :
    σ p = p ∧ σ r = r ∧ σ s = s ∧ σ t = t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination p * e3 - s * e1 - σ p * hdet
  · linear_combination (-t) * e1 + r * e3 - σ r * hdet
  · linear_combination p * e2 - s * e5 - σ s * hdet
  · linear_combination r * e2 - t * e5 - σ t * hdet

variable {M : Type} [AddCommGroup M] [Module E M]

theorem unitary_entries_fixed (σ : E →+* E) (B : M →ₛₗ[σ] M →ₗ[E] E) {a b : M} {ε : E}
    (hε : ε ≠ 0) (hσε : σ ε = -ε) (haa : B a a = 0) (hbb : B b b = 0) (hab : B a b = ε)
    (hba : B b a = -ε) {p r s t : E}
    (h1 : B (p • a + r • b) (p • a + r • b) = B a a)
    (h2 : B (s • a + t • b) (s • a + t • b) = B b b)
    (h3 : B (p • a + r • b) (s • a + t • b) = B a b)
    (h4 : B (s • a + t • b) (p • a + r • b) = B b a) (hdet : p * t - r * s = 1) :
    σ p = p ∧ σ r = r ∧ σ s = s ∧ σ t = t := by
  have hl : ∀ (c : E) (u w : M), B (c • u) w = σ c * B u w := fun c u w => by
    rw [map_smulₛₗ]; rfl
  have hr : ∀ (c : E) (u w : M), B u (c • w) = c * B u w := fun c u w => by
    rw [map_smul]; rfl
  simp only [map_add, LinearMap.add_apply, hl, hr, haa, hbb, hab, hba, mul_zero, zero_add,
    add_zero] at h1 h2 h3 h4
  have e1 : σ p * r = σ r * p := by
    apply mul_right_cancel₀ hε
    linear_combination h1
  have e2 : σ s * t = σ t * s := by
    apply mul_right_cancel₀ hε
    linear_combination h2
  have e3 : σ p * t - σ r * s = 1 := by
    apply mul_right_cancel₀ hε
    linear_combination h3
  have e5 : σ s * r - σ t * p = -1 := by
    apply mul_right_cancel₀ hε
    linear_combination h4
  exact entries_fixed_of_unitary σ e1 e2 e3 e5 hdet

end UnitaryEntries

end

section

section SelfDual

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem eichler_swap {u v : V} (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 0) :
    eichler Q u v = eichler Q v (-u) := by
  have hvu : polar Q v (-u) = 0 := by rw [polar_neg_right, polar_comm, huv, neg_zero]
  refine LinearEquiv.ext fun y => ?_
  rw [eichler_apply hu huv, eichler_apply hv hvu, polar_neg_right, QuadraticMap.map_neg, hu, hv]
  module

theorem polar_apply_self_of_sq {p : ℕ} (hx : OddOrderIsometry Q p x) {u : V}
    (hsq : x (x u) = -u - x u) : polar Q u (x u) = - Q u := by
  have h1 : Q (x (x u)) = Q u := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem]
  have h2 : Q (x u) = Q u := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem u
  rw [hsq, show -u - x u = -(u + x u) by abel, QuadraticMap.map_neg,
    QuadraticMap.map_add Q u (x u), h2] at h1
  linear_combination h1

variable {h : K[X]} [Fact (Irreducible h)]

theorem x_sq_of_root (hlam : AdjoinRoot.root h ^ 2 + AdjoinRoot.root h + 1 = 0)
    (u : primaryComponent x.toLinearMap h) : x (x (u : V)) = -(u : V) - x (u : V) := by
  have h0 : ((AdjoinRoot.root h ^ 2 + AdjoinRoot.root h + 1) • u :
      primaryComponent x.toLinearMap h) = 0 := by rw [hlam, zero_smul]
  have h1 := congrArg Subtype.val h0
  rw [add_smul, add_smul, pow_two, mul_smul, one_smul] at h1
  simp only [Submodule.coe_add, coe_root_smul_primaryComponent, ZeroMemClass.coe_zero] at h1
  linear_combination (norm := module) h1

theorem x_mem_of_mem (u : primaryComponent x.toLinearMap h) :
    x (u : V) ∈ primaryComponent x.toLinearMap h := by
  have h1 := (AdjoinRoot.root h • u).2
  rw [coe_root_smul_primaryComponent] at h1
  exact h1

theorem eichler_mem_specialBlock_selfDual {p : ℕ} (hx : OddOrderIsometry Q p x)
    (hh : h ∈ primaryFactors x.toLinearMap) (hself : h = reciprocalPolynomial h)
    (hlam : AdjoinRoot.root h ^ 2 + AdjoinRoot.root h + 1 = 0) {u : V}
    (hu : u ∈ primaryComponent x.toLinearMap h) (hQu : Q u = 0) (μ : K) :
    eichler Q u (μ • x u) ∈ specialBlock Q x h := by
  have horb : orbitSpace x.toLinearMap h = primaryComponent x.toLinearMap h := by
    rw [orbitSpace, ← hself, sup_idem]
  have hxu : x u ∈ primaryComponent x.toLinearMap h := x_mem_of_mem (x := x) ⟨u, hu⟩
  have hsq : x (x u) = -u - x u := x_sq_of_root hlam ⟨u, hu⟩
  have hQxu : Q (x u) = 0 := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem u, hQu]
  have hpol : polar Q u (x u) = 0 := by rw [polar_apply_self_of_sq hx hsq, hQu, neg_zero]
  refine eichler_mem_specialBlock hx hh (horb ▸ hu) (horb ▸ Submodule.smul_mem _ μ hxu) ?_
  have hQ1 : Q ((-μ) • u) = 0 := by rw [map_smul_eq_sq, hQu, mul_zero]
  have hp1 : polar Q (x u) ((-μ) • u) = 0 := by
    rw [polar_smul_right_eq, polar_comm, hpol, mul_zero]
  calc eichler Q (x u) (x (μ • x u)) = eichler Q (x u) (μ • (-u - x u)) := by
        rw [map_smul, hsq]
    _ = eichler Q (x u) ((-μ) • u) := by
        rw [show μ • (-u - x u) = (-μ) • u + (-μ) • x u by module]
        exact eichler_add_smul_self hQxu _ _
    _ = eichler Q ((-μ) • u) (-(x u)) := eichler_swap hQxu hQ1 hp1
    _ = eichler Q u (μ • x u) := by
        rw [eichler_smul_left, show (-μ) • -(x u) = μ • x u by module]

end SelfDual

end

section

section Spans

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem range_matrixToOriginal (A B : HypPair Q) :
    LinearMap.range (matrixToOriginal A B) = Submodule.span K {A.e, A.f, B.e, B.f} := by
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [matrixToOriginal_apply]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨!![1, 0; 0, 0], by simp [matrixToOriginal_apply]⟩
    · exact ⟨!![0, 0; 0, 1], by simp [matrixToOriginal_apply]⟩
    · exact ⟨!![0, 1; 0, 0], by simp [matrixToOriginal_apply]⟩
    · exact ⟨!![0, 0; -1, 0], by simp [matrixToOriginal_apply]⟩

theorem finrank_span_two_hypPairs (A B : HypPair Q) (hAB : A.Orth B) :
    finrank K (Submodule.span K {A.e, A.f, B.e, B.f}) = 4 := by
  rw [← range_matrixToOriginal, LinearMap.finrank_range_of_inj (matrixToOriginal_injective A B hAB),
    Module.finrank_matrix]
  simp

end Spans

section ThetaEntries

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {x : V ≃ₗ[K] V} {h : K[X]}

theorem exists_thetaSL_eq_of_entries
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (hinj : Function.Injective (algebraMap K (AdjoinRoot h)))
    (γ : SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (hent : ∀ i j, ∃ k : K, algebraMap K (AdjoinRoot h) k =
      (((Matrix.SpecialLinearGroup.toLin_equiv bE).symm γ : SL(2, AdjoinRoot h)) :
        Matrix (Fin 2) (Fin 2) (AdjoinRoot h)) i j) :
    ∃ m : SL(2, K), thetaSL x h bE m = γ := by
  set X : SL(2, AdjoinRoot h) := (Matrix.SpecialLinearGroup.toLin_equiv bE).symm γ with hX
  choose f hf using hent
  let M' : Matrix (Fin 2) (Fin 2) K := Matrix.of f
  have hmap : (algebraMap K (AdjoinRoot h)).mapMatrix M' = (X : Matrix (Fin 2) (Fin 2) _) := by
    ext i j
    exact hf i j
  have hdet : M'.det = 1 := by
    apply hinj
    rw [RingHom.map_det, hmap, map_one]
    exact X.2
  refine ⟨⟨M', hdet⟩, ?_⟩
  have h1 : Matrix.SpecialLinearGroup.map (algebraMap K (AdjoinRoot h)) ⟨M', hdet⟩ = X :=
    Subtype.ext hmap
  show Matrix.SpecialLinearGroup.toLin_equiv bE
    (Matrix.SpecialLinearGroup.map (algebraMap K (AdjoinRoot h)) ⟨M', hdet⟩) = γ
  rw [h1, hX, MulEquiv.apply_symm_apply]

theorem sl_apply_basis
    (bE : Module.Basis (Fin 2) (AdjoinRoot h) (primaryComponent x.toLinearMap h))
    (γ : SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (j : Fin 2) :
    γ.1 (bE j) = ∑ i, (((Matrix.SpecialLinearGroup.toLin_equiv bE).symm γ : SL(2, AdjoinRoot h)) :
      Matrix (Fin 2) (Fin 2) (AdjoinRoot h)) i j • bE i := by
  have h1 := Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq bE
    ((Matrix.SpecialLinearGroup.toLin_equiv bE).symm γ)
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 := LinearMap.congr_fun h1 (bE j)
  change _ = _ at h2
  rw [Matrix.toLin_self] at h2
  exact h2

end ThetaEntries

end

section

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem specialBlock_eq_levi_selfDual (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q 3 x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : primaryMultiplicity x.toLinearMap h = 2) :
    ∃ A B : HypPair Q, A.Orth B ∧
      Submodule.span K {A.e, A.f, B.e, B.f} = orbitSpace x.toLinearMap h ∧
      specialBlock Q x h = leviV Q A.e B.e A.f B.f := by
  classical
  have _hQ := hQ
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Module.Finite K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  obtain ⟨d, H, hdeg2d, hroot, hHtr, hHadd1, hHadd2, hHsm1, hHsm2, hHsymm⟩ :=
    hx.exists_selfDual_hermitian (by decide) hh hne1 hself
  have hdvd := hx.dvd_X_pow_sub_one hh
  have hle : h.natDegree ≤ 3 := by
    have hmon : (X ^ 3 - 1 : K[X]).Monic := by monicity!
    have := natDegree_le_of_dvd hdvd hmon.ne_zero
    have h3 : (X ^ 3 - 1 : K[X]).natDegree = 3 := by compute_degree!
    omega
  have hpos : 0 < h.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible Fact.out)
  have hd1 : d = 1 := by omega
  subst hd1
  have hdeg : h.natDegree = 2 := by omega
  have hfinE : finrank K (AdjoinRoot h) = 2 := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hm' : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := hm
  have hfinM : finrank K (primaryComponent x.toLinearMap h) = 4 := by
    rw [finrank_primaryComponent, hdeg, hm']
  set lam : AdjoinRoot h := AdjoinRoot.root h with hlamdef
  have hlam3 : lam ^ 3 = 1 := root_pow_eq_one hdvd
  have hlam1 : lam ≠ 1 := root_ne_one (monic_of_mem_primaryFactors hh) hne1
  have hlam0 : lam ≠ 0 := fun h0 => by rw [h0] at hlam3; simp at hlam3
  have hlam2 : lam ^ 2 + lam + 1 = 0 := by
    have : (lam - 1) * (lam ^ 2 + lam + 1) = 0 := by linear_combination hlam3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hlam1)
  let σ : AdjoinRoot h →+* AdjoinRoot h := (frobPow K (AdjoinRoot h) 1).toAlgHom.toRingHom
  have hσ : ∀ z, σ z = z ^ Nat.card K := fun z => by
    show frobPow K (AdjoinRoot h) 1 z = _
    rw [frobPow_apply, pow_one]
  have hσlam : σ lam = lam ^ 2 := by
    rw [hσ]
    have : lam ^ Nat.card K = lam⁻¹ := by simpa using hroot
    rw [this]
    exact inv_eq_of_mul_eq_one_right (by linear_combination hlam3)
  have hσlam2 : σ (lam ^ 2) = lam := by
    rw [map_pow, hσlam]
    linear_combination lam * hlam3
  set ε₀ : AdjoinRoot h := lam - lam ^ 2 with hε₀def
  have hσε : σ ε₀ = -ε₀ := by
    rw [hε₀def, map_sub, hσlam, hσlam2]; ring
  have hε0 : ε₀ ≠ 0 := by
    intro h0
    have : lam * (1 - lam) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact hlam0 h
    · exact hlam1 (sub_eq_zero.mp h).symm
  have hinj : Function.Injective (algebraMap K (AdjoinRoot h)) :=
    (algebraMap K (AdjoinRoot h)).injective
  have hTr : ∀ z, algebraMap K (AdjoinRoot h) (Algebra.trace K (AdjoinRoot h) z) = z + σ z :=
      fun z => by
    rw [algebraMap_trace_eq_add hfinE, hσ]
  have hT0 : Algebra.trace K (AdjoinRoot h) ε₀ = 0 := hinj (by rw [hTr, hσε]; simp)
  have hT1 : Algebra.trace K (AdjoinRoot h) (ε₀ * lam) = -3 := hinj (by
    rw [hTr, map_mul, hσε, hσlam, map_neg, map_ofNat, hε₀def]
    linear_combination (lam - 2) * hlam3 + hlam2)
  let Bs : primaryComponent x.toLinearMap h →ₛₗ[σ] primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h]
      AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ σ (RingHom.id _) H hHadd1 (fun c u w => by rw [hHsm1, smul_eq_mul]; rfl)
      hHadd2 (fun c u w => by rw [hHsm2, smul_eq_mul, RingHom.id_apply])
  have hB : ∀ u w, Bs u w = H u w := fun u w => rfl
  have hherm : ∀ u w, Bs w u = σ (Bs u w) := fun u w => hHsymm u w
  have hpol1 : ∀ u w : primaryComponent x.toLinearMap h,
      polar Q (u : V) (w : V) = Algebra.trace K (AdjoinRoot h) (H u w) := fun u w => by
    have := hHtr u w 1
    rw [mul_one, one_smul] at this
    exact this.symm
  have hpolx : ∀ u w : primaryComponent x.toLinearMap h,
      polar Q (u : V) (x (w : V)) = Algebra.trace K (AdjoinRoot h) (H u w * lam) := fun u w => by
    have := hHtr u w lam
    rw [coe_root_smul_primaryComponent] at this
    exact this.symm
  have hnd : ∀ u, (∀ w, Bs u w = 0) → u = 0 := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    rw [show polar Q (u : V) w = polar Q (u : V) ((⟨w, hw⟩ : primaryComponent x.toLinearMap h) : V)
      from rfl, hpol1, ← hB, hu, map_zero]
  obtain ⟨a, b, haa, hbb, hab⟩ :=
    exists_hermitian_isotropic_pair hfinE σ hσ Bs hherm hnd hm' ε₀
  have hba : Bs b a = -ε₀ := by rw [hherm, hab, hσε]
  have hQH : ∀ u : primaryComponent x.toLinearMap h, Bs u u = 0 → Q (u : V) = 0 := by
    intro u hu
    have hsq := x_sq_of_root hlam2 u
    have h1 := polar_apply_self_of_sq hx hsq
    rw [hpolx, ← hB, hu, zero_mul, map_zero] at h1
    exact neg_eq_zero.mp h1.symm
  have hQa : Q (a : V) = 0 := hQH a haa
  have hQb : Q (b : V) = 0 := hQH b hbb
  have h3 : (3 : K) ≠ 0 := by
    have := hx.cast_ne_zero
    simpa using this
  have hxpol : ∀ u w : V, polar Q (x u) (x w) = polar Q u w := fun u w =>
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem u w
  have hxQ : ∀ u : V, Q (x u) = Q u := fun u =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem u
  have P_ab : polar Q (a : V) (b : V) = 0 := by rw [hpol1, ← hB, hab, hT0]
  have P_aXa : polar Q (a : V) (x (a : V)) = 0 := by rw [hpolx, ← hB, haa, zero_mul, map_zero]
  have P_bXb : polar Q (b : V) (x (b : V)) = 0 := by rw [hpolx, ← hB, hbb, zero_mul, map_zero]
  have P_aXb : polar Q (a : V) (x (b : V)) = -3 := by rw [hpolx, ← hB, hab, hT1]
  have P_bXa : polar Q (b : V) (x (a : V)) = 3 := by
    rw [hpolx, ← hB, hba, neg_mul, map_neg, hT1, neg_neg]
  set κ : K := (3 : K)⁻¹ with hκdef
  have hκ3 : κ * 3 = 1 := inv_mul_cancel₀ h3
  have hQa' : Q ((-κ) • x (b : V)) = 0 := by rw [map_smul_eq_sq, hxQ, hQb, mul_zero]
  have hQb' : Q (κ • x (a : V)) = 0 := by rw [map_smul_eq_sq, hxQ, hQa, mul_zero]
  have hpolA : polar Q (a : V) ((-κ) • x (b : V)) = 1 := by
    rw [polar_smul_right_eq, P_aXb]; linear_combination hκ3
  have hpolB : polar Q (b : V) (κ • x (a : V)) = 1 := by
    rw [polar_smul_right_eq, P_bXa]; exact hκ3
  let PA : HypPair Q := ⟨(a : V), (-κ) • x (b : V), hQa, hQa', hpolA⟩
  let PB : HypPair Q := ⟨(b : V), κ • x (a : V), hQb, hQb', hpolB⟩
  have hAB : PA.Orth PB := by
    refine ⟨P_ab, ?_, ?_, ?_⟩
    · show polar Q (a : V) (κ • x (a : V)) = 0
      rw [polar_smul_right_eq, P_aXa, mul_zero]
    · show polar Q ((-κ) • x (b : V)) (b : V) = 0
      rw [polar_comm, polar_smul_right_eq, P_bXb, mul_zero]
    · show polar Q ((-κ) • x (b : V)) (κ • x (a : V)) = 0
      rw [polar_smul_left_eq, polar_smul_right_eq, hxpol, polar_comm Q (b : V) (a : V), P_ab]
      simp
  have hli : LinearIndependent (AdjoinRoot h) ![a, b] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have e1 : g 1 * ε₀ = 0 := by
      have := congrArg (Bs a) hg
      simp only [map_add, map_smul, map_zero, smul_eq_mul, haa, hab, mul_zero, zero_add] at this
      linear_combination this
    have e2 : g 0 * (-ε₀) = 0 := by
      have := congrArg (Bs b) hg
      simp only [map_add, map_smul, map_zero, smul_eq_mul, hba, hbb, mul_zero, add_zero] at this
      linear_combination this
    intro i
    fin_cases i
    · exact (mul_eq_zero.mp e2).resolve_right (neg_ne_zero.mpr hε0)
    · exact (mul_eq_zero.mp e1).resolve_right hε0
  let bE := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hm'])
  have hb0 : (bE 0 : V) = (a : V) := by simp [bE]
  have hb1 : (bE 1 : V) = (b : V) := by simp [bE]
  have hS₁ : ∀ c : K, eichler Q PA.e (c • PB.f) ∈ specialBlock Q x h := fun c => by
    have := eichler_mem_specialBlock_selfDual hx hh hself hlam2 a.2 hQa (c * κ)
    show eichler Q (a : V) (c • κ • x (a : V)) ∈ specialBlock Q x h
    rw [smul_smul]
    exact this
  have hS₂ : ∀ c : K, eichler Q PB.e (c • PA.f) ∈ specialBlock Q x h := fun c => by
    have := eichler_mem_specialBlock_selfDual hx hh hself hlam2 b.2 hQb (c * (-κ))
    show eichler Q (b : V) (c • (-κ) • x (b : V)) ∈ specialBlock Q x h
    rw [smul_smul]
    exact this
  have hbE0 : bE 0 = a := by simp [bE]
  have hbE1 : bE 1 = b := by simp [bE]
  have hsur : ∀ g : ↥(specialBlock Q x h),
      ∃ m : SL(2, K), thetaSL x h bE m = specialToSL Q x h g := by
    intro g
    set γ := specialToSL Q x h g with hγ
    set X : SL(2, AdjoinRoot h) := (Matrix.SpecialLinearGroup.toLin_equiv bE).symm γ with hX
    have hpres : ∀ u w : primaryComponent x.toLinearMap h, Bs (γ.1 u) (γ.1 w) = Bs u w := by
      intro u w
      have hgS : g.1 ∈ supportedBlock Q x h := specialBlock_le_supportedBlock h g.2
      have hrange : blockGL Q x h ⟨g.1, hgS⟩ ∈ (blockGL Q x h).range := ⟨_, rfl⟩
      have key := (hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hHtr _).mp hrange u w
      have e : ∀ v, γ.1 v = ((blockGL Q x h ⟨g.1, hgS⟩ : BlockGL x h) :
          Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) v := fun v =>
        Subtype.ext (by rw [hγ, specialToSL_apply, coe_blockGL])
      rw [hB, hB, e u, e w]
      exact key
    have hγa : γ.1 a = X 0 0 • a + X 1 0 • b := by
      rw [← hbE0, sl_apply_basis bE γ 0, Fin.sum_univ_two, hbE0, hbE1]
    have hγb : γ.1 b = X 0 1 • a + X 1 1 • b := by
      rw [← hbE1, sl_apply_basis bE γ 1, Fin.sum_univ_two, hbE0, hbE1]
    have hdet : X 0 0 * X 1 1 - X 1 0 * X 0 1 = 1 := by
      have := X.2
      rw [Matrix.det_fin_two] at this
      linear_combination this
    have h1 : Bs (X 0 0 • a + X 1 0 • b) (X 0 0 • a + X 1 0 • b) = Bs a a := by
      rw [← hγa]; exact hpres a a
    have h2 : Bs (X 0 1 • a + X 1 1 • b) (X 0 1 • a + X 1 1 • b) = Bs b b := by
      rw [← hγb]; exact hpres b b
    have h3 : Bs (X 0 0 • a + X 1 0 • b) (X 0 1 • a + X 1 1 • b) = Bs a b := by
      rw [← hγa, ← hγb]; exact hpres a b
    have h4 : Bs (X 0 1 • a + X 1 1 • b) (X 0 0 • a + X 1 0 • b) = Bs b a := by
      rw [← hγa, ← hγb]; exact hpres b a
    obtain ⟨hp, hr, hs, ht⟩ := unitary_entries_fixed σ Bs hε0 hσε haa hbb hab hba h1 h2 h3 h4 hdet
    have hent : ∀ i j, ∃ k : K, algebraMap K (AdjoinRoot h) k = X i j := by
      intro i j
      refine exists_algebraMap_of_pow_card_eq hfinE ?_
      rw [← hσ]
      fin_cases i <;> fin_cases j
      · exact hp
      · exact hs
      · exact hr
      · exact ht
    exact exists_thetaSL_eq_of_entries bE hinj γ hent
  have hspan : Submodule.span K {PA.e, PA.f, PB.e, PB.f} = orbitSpace x.toLinearMap h := by
    have horb : orbitSpace x.toLinearMap h = primaryComponent x.toLinearMap h := by
      rw [orbitSpace, ← hself, sup_idem]
    rw [horb]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact a.2
      · exact Submodule.smul_mem _ _ (x_mem_of_mem b)
      · exact b.2
      · exact Submodule.smul_mem _ _ (x_mem_of_mem a)
    · rw [hfinM, finrank_span_two_hypPairs PA PB hAB]
  exact ⟨PA, PB, hAB, hspan, specialBlock_eq_levi_of hx hh PA PB hAB bE hb0 hb1 hS₁ hS₂ hsur⟩

end

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
