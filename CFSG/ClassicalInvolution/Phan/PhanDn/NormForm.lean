module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Embed
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalHermitianBlock
public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary
open QuadraticMap

theorem quadExt_of_card_of_char_two {F K : Type} [Field F] [Field K] [Finite K]
    [Algebra F K] (f : ℕ) [CharP K 2]
    (hF : Nat.card F = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    QuadExt F K (unitaryInvolution K 2 f) :=
  letI : Finite F := Nat.finite_of_card_ne_zero (α := F) (by
    rw [hF]
    exact (pow_pos (by norm_num) f).ne')
  { isUnitary := isUnitaryInvolution_unitaryInvolution hK
    fix := Aniso.sigma_algebraMap hF
    exists_of_fix := fun x hx => Aniso.exists_algebraMap_of_fixed hF hK hx
    isSquare := fun a =>
      FiniteField.isSquare_of_char_two (ringChar.eq K 2) (algebraMap F K a)
    finrank_eq := Aniso.finrank_eq_two hF hK }

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K}

@[expose] noncomputable def normTailData (E : QuadExt F K σ) : NormTailData F K where
  bar := AlgEquiv.ofRingEquiv (f := σ) E.fix
  bar_bar z := by
    rw [AlgEquiv.ofRingEquiv_apply, AlgEquiv.ofRingEquiv_apply]
    exact E.isUnitary.invol z
  exists_eq_of_bar_eq z hz := by
    refine E.exists_of_fix z ?_
    rwa [AlgEquiv.ofRingEquiv_apply] at hz

@[simp] theorem normTailData_bar (E : QuadExt F K σ) (x : K) :
    (normTailData E).bar x = σ x := by
  rw [normTailData, AlgEquiv.ofRingEquiv_apply]

@[expose] noncomputable def normQuad (E : QuadExt F K σ) : QuadraticForm F K :=
  normForm (normTailData E)

theorem normQuad_apply (E : QuadExt F K σ) (x : K) :
    normQuad E x = retr F K (x * σ x) := by
  rw [normQuad, normForm_apply, normTailData_bar]

theorem algebraMap_normQuad (E : QuadExt F K σ) (x : K) :
    algebraMap F K (normQuad E x) = x * σ x := by
  rw [normQuad, algebraMap_normForm, normTailData_bar]

theorem algebraMap_polar_normQuad (E : QuadExt F K σ) (x y : K) :
    algebraMap F K (polar (normQuad E) x y) = x * σ y + y * σ x := by
  rw [normQuad, algebraMap_polar_normForm, normTailData_bar, normTailData_bar]

theorem normQuad_one (E : QuadExt F K σ) : normQuad E 1 = 1 := by
  apply (algebraMap F K).injective
  rw [algebraMap_normQuad]
  simp

theorem normQuad_polarBilin_nondegenerate [CharP K 2] (E : QuadExt F K σ) :
    (polarBilin (normQuad E)).Nondegenerate :=
  letI : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  show (polarBilin (normForm (normTailData E))).Nondegenerate from
    nondegenerate_polarBilin_normForm (T := normTailData E) E.finrank_eq

theorem algebraMap_retr_trace (E : QuadExt F K σ) (x : K) :
    algebraMap F K (retr F K (x + σ x)) = x + σ x := by
  apply algebraMap_retr (T := normTailData E)
  rw [normTailData_bar, map_add, E.isUnitary.invol, add_comm]

theorem exists_trace_eq (E : QuadExt F K σ) (x : K) :
    ∃ a : F, algebraMap F K a = x + σ x :=
  ⟨_, algebraMap_retr_trace E x⟩

theorem normQuad_surjective (E : QuadExt F K σ) : Function.Surjective (normQuad E) := by
  intro a
  obtain ⟨x, hx⟩ := E.isUnitary.exists_norm (E.fix a)
  refine ⟨x, ?_⟩
  apply (algebraMap F K).injective
  rw [algebraMap_normQuad, mul_comm, hx]

@[expose] noncomputable def Qn (E : QuadExt F K σ) (n : ℕ) : QuadraticForm F (Fin n → K) :=
  QuadraticMap.pi fun _ : Fin n => normQuad E

theorem Qn_apply (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) :
    Qn E n x = ∑ i, normQuad E (x i) :=
  QuadraticMap.pi_apply _ _

theorem algebraMap_Qn (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) :
    algebraMap F K (Qn E n x) = ∑ i, x i * σ (x i) := by
  rw [Qn_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => algebraMap_normQuad E (x i)

theorem polar_Qn (E : QuadExt F K σ) (n : ℕ) (x y : Fin n → K) :
    polar (Qn E n) x y = ∑ i, polar (normQuad E) (x i) (y i) := by
  rw [Qn, QuadraticMap.Ring.polar_pi]

theorem algebraMap_polar_Qn (E : QuadExt F K σ) (n : ℕ) (x y : Fin n → K) :
    algebraMap F K (polar (Qn E n) x y) =
      (∑ i, x i * σ (y i)) + σ (∑ i, x i * σ (y i)) := by
  rw [polar_Qn, map_sum]
  have hsplit :
      (∑ i, algebraMap F K (polar (normQuad E) (x i) (y i))) =
        (∑ i, x i * σ (y i)) + ∑ i, y i * σ (x i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => algebraMap_polar_normQuad E (x i) (y i)
  rw [hsplit, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by
    rw [map_mul, E.isUnitary.invol, mul_comm]

theorem polar_Qn_single (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) (i : Fin n) (y : K) :
    polar (Qn E n) x (Pi.single i y) = polar (normQuad E) (x i) y := by
  rw [polar_Qn, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, QuadraticMap.polar_zero_right]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem Qn_single_one (E : QuadExt F K σ) {n : ℕ} (k : Fin n) :
    Qn E n (Pi.single k 1) = 1 := by
  rw [Qn_apply, Finset.sum_eq_single k]
  · simp [normQuad_one]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, QuadraticMap.map_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem polar_Qn_single_one_eq (E : QuadExt F K σ) {n : ℕ} (k : Fin n) (x : Fin n → K) :
    polar (Qn E n) (Pi.single k 1) x = retr F K (x k + σ (x k)) := by
  apply (algebraMap F K).injective
  rw [QuadraticMap.polar_comm, polar_Qn_single E, algebraMap_polar_normQuad E,
    algebraMap_retr_trace E]
  simp

theorem Qn_polarBilin_nondegenerate [CharP K 2] (E : QuadExt F K σ) (n : ℕ) :
    (polarBilin (Qn E n)).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
  funext i
  by_contra hi
  exact hi ((normQuad_polarBilin_nondegenerate E).1 (v i) fun y => by
    have h := hv (Pi.single i y)
    rwa [polar_Qn_single E] at h)

@[expose] noncomputable def suEndNLinear (σ : K ≃+* K) (n : ℕ)
    (g : SUid σ n) : (Fin n → K) →ₗ[F] (Fin n → K) where
  toFun := fun v => g • v
  map_add' := fun v w => smul_add g v w
  map_smul' := fun c v => by
    rw [← algebraMap_smul K c v, smul_comm, algebraMap_smul]
    simp

theorem suEndNLinear_apply (σ : K ≃+* K) (n : ℕ) (g : SUid σ n) (v : Fin n → K) :
    suEndNLinear (F := F) σ n g v = g • v :=
  rfl

@[expose] noncomputable def suEndNEquiv (σ : K ≃+* K) (n : ℕ) (g : SUid σ n) :
    (Fin n → K) ≃ₗ[F] (Fin n → K) :=
  LinearEquiv.ofLinearMap (f := suEndNLinear (F := F) σ n g)
    (g := suEndNLinear (F := F) σ n g⁻¹)
    (by
      ext v
      simp [LinearMap.comp_apply, suEndNLinear_apply])
    (by
      ext v
      simp [LinearMap.comp_apply, suEndNLinear_apply])

theorem suEndNEquiv_apply (σ : K ≃+* K) (n : ℕ) (g : SUid σ n) (v : Fin n → K) :
    suEndNEquiv (F := F) σ n g v = g • v := by
  rw [suEndNEquiv, LinearEquiv.coe_ofLinearMap]
  rfl

@[expose] noncomputable def suEndN (σ : K ≃+* K) (n : ℕ) :
    SUid σ n →* ((Fin n → K) ≃ₗ[F] (Fin n → K)) where
  toFun := fun g => suEndNEquiv (F := F) σ n g
  map_one' := by
    apply LinearEquiv.ext
    intro v
    simp [suEndNEquiv_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    simp [suEndNEquiv_apply, mul_smul]

theorem suEndN_apply (σ : K ≃+* K) (n : ℕ) (g : SUid σ n) (v : Fin n → K) :
    suEndN (F := F) σ n g v = g • v := by
  simp [suEndN, suEndNEquiv_apply]

theorem suEndN_injective (σ : K ≃+* K) (n : ℕ) :
    Function.Injective (suEndN (F := F) σ n) := by
  intro g h hgh
  apply ext_smul σ
  intro v
  have := congrArg (fun e : (Fin n → K) ≃ₗ[F] (Fin n → K) => e v) hgh
  simpa [suEndN_apply] using this

theorem suEndN_mem_orthogonalGroup (E : QuadExt F K σ) (n : ℕ) (g : SUid σ n) :
    suEndN (F := F) σ n g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  apply (algebraMap F K).injective
  rw [algebraMap_Qn, algebraMap_Qn, suEndN_apply]
  have h := herm_smul_smul σ g x x
  calc
    (∑ i, (g • x) i * σ ((g • x) i))
        = ∑ i, σ ((g • x) i) * (g • x) i := by
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = herm σ (g • x) (g • x) := rfl
    _ = herm σ x x := h
    _ = ∑ i, σ (x i) * x i := rfl
    _ = ∑ i, x i * σ (x i) := by
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _

@[expose] noncomputable def tauAt (E : QuadExt F K σ) {n : ℕ} (k : Fin n) :
    (Fin n → K) ≃ₗ[F] (Fin n → K) :=
  LinearEquiv.piCongrRight fun i =>
    if i = k then E.sigmaEquiv else LinearEquiv.refl F K

theorem tauAt_apply (E : QuadExt F K σ) {n : ℕ} (k : Fin n) (x : Fin n → K) (i : Fin n) :
    tauAt E k x i = if i = k then σ (x i) else x i := by
  rw [tauAt, LinearEquiv.piCongrRight_apply]
  by_cases h : i = k
  · rw [h]
    simp [QuadExt.sigmaEquiv]
  · simp [h]

theorem tauAt_mem_orthogonalGroup (E : QuadExt F K σ) {n : ℕ} (k : Fin n) :
    tauAt E k ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  apply (algebraMap F K).injective
  rw [algebraMap_Qn, algebraMap_Qn]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases h : i = k
    · rw [h]
      rw [tauAt_apply E, if_pos rfl, E.isUnitary.invol, mul_comm]
    · rw [tauAt_apply E, if_neg h]

theorem tauAt_mul_self (E : QuadExt F K σ) {n : ℕ} (k : Fin n) :
    tauAt E k * tauAt E k = 1 := by
  apply LinearEquiv.ext
  intro x
  funext i
  rw [LinearEquiv.mul_apply]
  by_cases h : i = k
  · rw [h]
    simp [tauAt_apply, E.isUnitary.invol]
  · simp [tauAt_apply, h]

theorem smul_single_apply {n : ℕ} (c : F) (k i : Fin n) :
    (c • (Pi.single k (1 : K) : Fin n → K)) i =
      if i = k then algebraMap F K c else 0 := by
  by_cases h : i = k
  · rw [h]
    simp [Algebra.smul_def]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne h, smul_zero, if_neg h]

theorem tauAt_eq_reflect [CharP K 2] (E : QuadExt F K σ) {n : ℕ} (k : Fin n) :
    tauAt E k = CFSG.ClassicalGroups.Orthogonal.reflect (Qn E n) (Pi.single k 1) := by
  have hQ : Qn E n (Pi.single k 1) = 1 := Qn_single_one E k
  have hv : Qn E n (Pi.single k 1) ≠ 0 := by
    rw [hQ]
    exact one_ne_zero
  apply LinearEquiv.ext
  intro x
  funext i
  rw [tauAt_apply E]
  have hrefl := congrFun
    (CFSG.ClassicalGroups.Orthogonal.reflect_apply (Q := Qn E n) hv x) i
  rw [hrefl]
  have hp : polar (Qn E n) (Pi.single k 1) x = retr F K (x k + σ (x k)) :=
    polar_Qn_single_one_eq E k x
  rw [hQ, div_one, hp]
  by_cases h : i = k
  · rw [h]
    rw [if_pos rfl, Pi.sub_apply, smul_single_apply, if_pos rfl, algebraMap_retr_trace E,
      CharTwo.sub_eq_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · rw [if_neg h, Pi.sub_apply, smul_single_apply, if_neg h, sub_zero]

theorem dicksonInvariant_tauAt_eq_one [CharP K 2] (E : QuadExt F K σ) {n : ℕ} (k : Fin n)
    {X₀ : Submodule F (Fin n → K)}
    (hX₀ : (CFSG.RankThree.OrthogonalInvolutions.toQuadForm (Qn E n)
      (Qn_polarBilin_nondegenerate E n)).IsLagrangian X₀) :
    CFSG.LieType.BorelTits.dicksonInvariant X₀
      (tauAt E k : Module.End F (Fin n → K)) = 1 := by
  let Φ := CFSG.RankThree.OrthogonalInvolutions.toQuadForm (Qn E n)
    (Qn_polarBilin_nondegenerate E n)
  have hg : ∀ v, Φ.Q ((tauAt E k : Module.End F (Fin n → K)) v) = Φ.Q v := by
    intro v
    rw [CFSG.RankThree.OrthogonalInvolutions.toQuadForm_Q]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (tauAt_mem_orthogonalGroup E k) v
  have hQa : Φ.Q (Pi.single k 1) ≠ 0 := by
    rw [CFSG.RankThree.OrthogonalInvolutions.toQuadForm_Q, Qn_single_one E]
    exact one_ne_zero
  exact letI : FiniteDimensional F K :=
      FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
    (by
      refine CFSG.LieType.BorelTits.QuadForm.dicksonInvariant_eq_one_of_reflection
        (Φ := Φ) hX₀ hg (Z := ⊥) (a := Pi.single k 1)
        (CFSG.LieType.BorelTits.QuadForm.isTotallySingular_bot (Φ := Φ)) ?_ hQa ?_
      · rw [CFSG.LieType.BorelTits.ReflForm.perp_bot]
        exact Submodule.mem_top
      · intro v _
        rw [Submodule.mem_bot]
        have hv : Qn E n (Pi.single k 1) ≠ 0 := by
          rw [Qn_single_one E]
          exact one_ne_zero
        have hrefl : (tauAt E k : Module.End F (Fin n → K)) v =
            v - ((polar (Qn E n) v (Pi.single k 1) / Qn E n (Pi.single k 1)) •
              (Pi.single k 1 : Fin n → K)) := by
          rw [tauAt_eq_reflect E]
          rw [QuadraticMap.polar_comm]
          exact CFSG.ClassicalGroups.Orthogonal.reflect_apply hv v
        rw [CFSG.RankThree.OrthogonalInvolutions.toQuadForm_polar_β
            (Q := Qn E n) (hQ := Qn_polarBilin_nondegenerate E n),
          CFSG.RankThree.OrthogonalInvolutions.toQuadForm_Q
            (Q := Qn E n) (hQ := Qn_polarBilin_nondegenerate E n),
          hrefl]
        simp only [Qn_single_one E, div_one]
        exact sub_self _)

theorem suEndN_apply_tauAt_comm (E : QuadExt F K σ) {n : ℕ}
    (g : SUid σ n) (k : Fin n)
    (hfix : g • (Pi.single k (1 : K) : Fin n → K) = Pi.single k (1 : K))
    (hpres : ∀ x : Fin n → K, x k = 0 → (g • x) k = 0) (x : Fin n → K) :
    suEndN (F := F) σ n g (tauAt E k x) =
      tauAt E k (suEndN (F := F) σ n g x) := by
  have hrow : ∀ y : Fin n → K, (g • y) k = y k := by
    intro y
    have hdec : y = y k • (Pi.single k (1 : K) : Fin n → K) +
        (y - y k • (Pi.single k (1 : K) : Fin n → K)) := by
      ext j
      by_cases hj : j = k <;> simp [hj]
    have hzero : (y - y k • (Pi.single k (1 : K) : Fin n → K)) k = 0 := by
      simp
    have hsmul : g • (y k • (Pi.single k (1 : K) : Fin n → K)) =
        y k • (g • (Pi.single k (1 : K) : Fin n → K)) :=
      (SMulCommClass.smul_comm (y k) g _).symm
    calc
      (g • y) k = (g • (y k • (Pi.single k (1 : K) : Fin n → K) +
        (y - y k • (Pi.single k (1 : K) : Fin n → K)))) k := by conv_lhs => rw [hdec]
      _ = (g • (y k • (Pi.single k (1 : K) : Fin n → K)) +
        g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) k := by rw [smul_add]
      _ = (y k • (g • (Pi.single k (1 : K) : Fin n → K)) +
        g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) k := by rw [hsmul]
      _ = (y k • (Pi.single k (1 : K) : Fin n → K) +
        g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) k := by rw [hfix]
      _ = (y k • (Pi.single k (1 : K) : Fin n → K)) k +
        (g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) k := rfl
      _ = y k + 0 := by
            rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hpres _ hzero]
      _ = y k := add_zero _
  have hcol : ∀ (y : Fin n → K) (i : Fin n), i ≠ k →
      (g • y) i = (g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) i := by
    intro y i hi
    have hdec : y = y k • (Pi.single k (1 : K) : Fin n → K) +
        (y - y k • (Pi.single k (1 : K) : Fin n → K)) := by
      ext j
      by_cases hj : j = k <;> simp [hj]
    have hsmul : g • (y k • (Pi.single k (1 : K) : Fin n → K)) =
        y k • (g • (Pi.single k (1 : K) : Fin n → K)) :=
      (SMulCommClass.smul_comm (y k) g _).symm
    calc
      (g • y) i = (g • (y k • (Pi.single k (1 : K) : Fin n → K) +
        (y - y k • (Pi.single k (1 : K) : Fin n → K)))) i := by conv_lhs => rw [hdec]
      _ = (g • (y k • (Pi.single k (1 : K) : Fin n → K)) +
        g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) i := by rw [smul_add]
      _ = (y k • (g • (Pi.single k (1 : K) : Fin n → K)) +
        g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) i := by rw [hsmul]
      _ = (y k • (Pi.single k (1 : K) : Fin n → K) +
        g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) i := by rw [hfix]
      _ = (y k • (Pi.single k (1 : K) : Fin n → K)) i +
        (g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) i := rfl
      _ = 0 + (g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) i := by
            rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero]
      _ = (g • (y - y k • (Pi.single k (1 : K) : Fin n → K))) i := zero_add _
  funext i
  rw [suEndN_apply (F := F) σ n, suEndN_apply (F := F) σ n]
  by_cases hi : i = k
  · rw [hi]
    rw [hrow (tauAt E k x)]
    simp only [tauAt_apply E, hrow x]
  · rw [tauAt_apply E, if_neg hi]
    have hrest : tauAt E k x - (tauAt E k x) k •
        (Pi.single k (1 : K) : Fin n → K) =
        x - x k • (Pi.single k (1 : K) : Fin n → K) := by
      ext j
      by_cases hj : j = k <;> simp [tauAt_apply, hj]
    rw [hcol (tauAt E k x) i hi, hcol x i hi, hrest]

theorem suEndN_commute_tauAt (E : QuadExt F K σ) {n : ℕ}
    (g : SUid σ n) (k : Fin n)
    (hfix : g • (Pi.single k (1 : K) : Fin n → K) = Pi.single k (1 : K))
    (hpres : ∀ x : Fin n → K, x k = 0 → (g • x) k = 0) :
    Commute (suEndN (F := F) σ n g) (tauAt E k) := by
  rw [Commute]
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact suEndN_apply_tauAt_comm E g k hfix hpres x

theorem tauAt_conj_mem_orthogonalGroup (E : QuadExt F K σ) {n : ℕ} (k : Fin n)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n)) :
    tauAt E k * g * (tauAt E k)⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) :=
  mul_mem (mul_mem (tauAt_mem_orthogonalGroup E k) hg)
    (inv_mem (tauAt_mem_orthogonalGroup E k))

end CFSG.ClassicalInvolution.PhanDn
