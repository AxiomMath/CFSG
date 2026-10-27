module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LinearAlgebra

theorem b_inv_mul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (b : F →ₗ[K] F →ₗ[K] K) {t : F} (ht0 : t ≠ 0)
    (hiso : ∀ a a', b (t * a) (t * a') = b a a') (a a' : F) :
    b (t⁻¹ * a) a' = b a (t * a') := by
  have h := hiso (t⁻¹ * a) a'
  rw [← mul_assoc, mul_inv_cancel₀ ht0, one_mul] at h
  exact h.symm

theorem b_pow_inv_mul {K F : Type*} [Field K] [Field F] [Algebra K F]
    (b : F →ₗ[K] F →ₗ[K] K) {t : F} (ht0 : t ≠ 0)
    (hiso : ∀ a a', b (t * a) (t * a') = b a a') :
    ∀ (n : ℕ) (a a' : F), b ((t⁻¹) ^ n * a) a' = b a (t ^ n * a') := by
  intro n
  induction n with
  | zero =>
      intro a a'
      simp
  | succ n ih =>
      intro a a'
      calc
        b ((t⁻¹) ^ (n + 1) * a) a' = b (t⁻¹ * ((t⁻¹) ^ n * a)) a' := by
          rw [pow_succ', mul_assoc]
        _ = b ((t⁻¹) ^ n * a) (t * a') := b_inv_mul b ht0 hiso _ _
        _ = b a (t ^ n * (t * a')) := ih _ _
        _ = b a (t ^ (n + 1) * a') := by
          congr 1
          rw [pow_succ, ← mul_assoc]

theorem b_aeval_C_mul_X_pow {K F : Type*} [Field K] [Field F] [Algebra K F]
    (b : F →ₗ[K] F →ₗ[K] K) {t : F} (ht0 : t ≠ 0)
    (hiso : ∀ a a', b (t * a) (t * a') = b a a') (n : ℕ) (c : K) (a a' : F) :
    b (Polynomial.aeval (t⁻¹) (Polynomial.C c * Polynomial.X ^ n) * a) a'
      = b a (Polynomial.aeval t (Polynomial.C c * Polynomial.X ^ n) * a') := by
  simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  have h1 : algebraMap K F c * (t⁻¹) ^ n * a
      = algebraMap K F c * ((t⁻¹) ^ n * a) := by rw [mul_assoc]
  have h2 : algebraMap K F c * t ^ n * a'
      = algebraMap K F c * (t ^ n * a') := by rw [mul_assoc]
  rw [h1, h2, ← Algebra.smul_def, ← Algebra.smul_def]
  rw [map_smul, LinearMap.smul_apply, map_smul, b_pow_inv_mul b ht0 hiso]

theorem b_aeval_inv {K F : Type*} [Field K] [Field F] [Algebra K F]
    (b : F →ₗ[K] F →ₗ[K] K) {t : F} (ht0 : t ≠ 0)
    (hiso : ∀ a a', b (t * a) (t * a') = b a a') (P : Polynomial K) :
    ∀ a a', b (Polynomial.aeval (t⁻¹) P * a) a'
      = b a (Polynomial.aeval t P * a') := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      intro a a'
      simp only [map_add, add_mul, LinearMap.add_apply]
      rw [hP a a', hQ a a']
  | monomial n c =>
      intro a a'
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      exact b_aeval_C_mul_X_pow b ht0 hiso n c a a'

theorem aeval_inv_minpoly_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (b : F →ₗ[K] F →ₗ[K] K) (hnd : ∀ a, (∀ a', b a a' = 0) → a = 0)
    {t : F} (ht0 : t ≠ 0) (hiso : ∀ a a', b (t * a) (t * a') = b a a') :
    Polynomial.aeval (t⁻¹) (minpoly K t) = 0 := by
  apply hnd
  intro a'
  have h := b_aeval_inv b ht0 hiso (minpoly K t) 1 a'
  simpa [minpoly.aeval] using h

theorem adjoint_compat {K F : Type*} [Field K] [Field F] [Algebra K F]
    (b : F →ₗ[K] F →ₗ[K] K) (hsymm : ∀ a a', b a a' = b a' a)
    {t : F} (ht0 : t ≠ 0) (hgen : Algebra.adjoin K ({t} : Set F) = ⊤)
    (hiso : ∀ a a', b (t * a) (t * a') = b a a')
    (τ : F →ₐ[K] F) (hτt : τ t = t⁻¹) :
    ∀ y a a', b (y * a) a' = b a (τ y * a') := by
  intro y
  have hy : y ∈ Algebra.adjoin K ({t} : Set F) := by
    rw [hgen]
    exact trivial
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      subst z
      intro a a'
      calc
        b (t * a) a' = b a' (t * a) := hsymm _ _
        _ = b (t⁻¹ * a') a := (b_inv_mul b ht0 hiso a' a).symm
        _ = b a (t⁻¹ * a') := hsymm _ _
        _ = b a (τ t * a') := by rw [hτt]
  | algebraMap r =>
      intro a a'
      have h1 : b (algebraMap K F r * a) a' = r • b a a' := by
        rw [← Algebra.smul_def, map_smul, LinearMap.smul_apply]
      have h2 : b a (algebraMap K F r * a') = r • b a a' := by
        rw [← Algebra.smul_def, map_smul]
      rw [h1, AlgHom.commutes τ r, h2]
  | add x y _ _ ihx ihy =>
      intro a a'
      calc
        b ((x + y) * a) a' = b (x * a + y * a) a' := by rw [add_mul]
        _ = b (x * a) a' + b (y * a) a' := by rw [map_add, LinearMap.add_apply]
        _ = b a (τ x * a') + b a (τ y * a') := by rw [ihx, ihy]
        _ = b a (τ x * a' + τ y * a') := by rw [map_add]
        _ = b a ((τ x + τ y) * a') := by rw [add_mul]
        _ = b a (τ (x + y) * a') := by rw [map_add]
  | mul x y _ _ ihx ihy =>
      intro a a'
      calc
        b ((x * y) * a) a' = b (x * (y * a)) a' := by rw [mul_assoc]
        _ = b (y * a) (τ x * a') := ihx _ _
        _ = b a (τ y * (τ x * a')) := ihy _ _
        _ = b a ((τ y * τ x) * a') := by rw [mul_assoc]
        _ = b a ((τ x * τ y) * a') := by rw [mul_comm (τ y) (τ x)]
        _ = b a (τ (x * y) * a') := by rw [map_mul τ x y]

theorem generator_ne_zero_and_inv_ne_self {F : Type*} [Field F] {t : F}
    (ht1 : t ≠ 1) (hodd : Odd (orderOf t)) : t ≠ 0 ∧ t⁻¹ ≠ t := by
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hodd
    rcases hodd with ⟨k, hk⟩
    omega
  refine ⟨ht0, ?_⟩
  intro h
  have ht2 : t ^ 2 = 1 := by
    calc
      t ^ 2 = t * t := pow_two t
      _ = t * t⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel₀ ht0
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ht2
  have hord : orderOf t = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact h1
    · rw [h1] at hodd
      rcases hodd with ⟨k, hk⟩
      omega
  exact ht1 (orderOf_eq_one_iff.mp hord)

theorem exists_algHom_inv {K F : Type*} [Field K] [Fintype K] [Field F] [Finite F]
    [Algebra K F] (b : F →ₗ[K] F →ₗ[K] K) (hnd : ∀ a, (∀ a', b a a' = 0) → a = 0)
    {t : F} (ht0 : t ≠ 0) (hgen : Algebra.adjoin K ({t} : Set F) = ⊤)
    (hiso : ∀ a a', b (t * a) (t * a') = b a a') :
    ∃ τ : F →ₐ[K] F, τ t = t⁻¹ ∧ ∀ y, τ (τ y) = y := by
  have : Module.Finite K F := Module.Finite.of_finite
  have hint : IsIntegral K t := IsIntegral.of_finite K t
  let pb : PowerBasis K F := PowerBasis.ofAdjoinEqTop hint hgen
  have hpb : pb.gen = t := PowerBasis.ofAdjoinEqTop_gen hint hgen
  have hmininv : Polynomial.aeval (t⁻¹) (minpoly K t) = 0 :=
    aeval_inv_minpoly_eq_zero b hnd ht0 hiso
  have hroot : Polynomial.aeval (t⁻¹) (minpoly K pb.gen) = 0 := by
    rw [hpb]
    exact hmininv
  let τ : F →ₐ[K] F := pb.lift (t⁻¹) hroot
  have hτt : τ t = t⁻¹ := by
    have hgenτ : τ pb.gen = t⁻¹ := PowerBasis.lift_gen pb (t⁻¹) hroot
    simpa [hpb] using hgenτ
  have hττ : ∀ y : F, τ (τ y) = y := by
    have hcomp : τ.comp τ = AlgHom.id K F := by
      apply PowerBasis.algHom_ext pb
      rw [hpb]
      simp [hτt]
    intro y
    have := congrArg (fun f : F →ₐ[K] F => f y) hcomp
    simpa using this
  exact ⟨τ, hτt, hττ⟩

theorem exists_mul_pow_card_isometry {K F : Type*} [Field K] [Fintype K] [CharP K 2] [Field F]
    [Finite F] [Algebra K F] (b : F →ₗ[K] F →ₗ[K] K) (hsymm : ∀ a a', b a a' = b a' a)
    (hnd : ∀ a, (∀ a', b a a' = 0) → a = 0) {t : F} (ht1 : t ≠ 1) (hodd : Odd (orderOf t))
    (hgen : Algebra.adjoin K {t} = ⊤) (hiso : ∀ a a', b (t * a) (t * a') = b a a') :
    ∃ u : F, u ≠ 0 ∧ ∀ a a', b (u * a ^ Fintype.card K) (u * a' ^ Fintype.card K) = b a a' := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ht0, htinv⟩ := generator_ne_zero_and_inv_ne_self ht1 hodd
  have hmininv : Polynomial.aeval (t⁻¹) (minpoly K t) = 0 :=
    aeval_inv_minpoly_eq_zero b hnd ht0 hiso
  obtain ⟨τ, hτt, hττ⟩ := exists_algHom_inv b hnd ht0 hgen hiso
  have hadj : ∀ y a a', b (y * a) a' = b a (τ y * a') :=
    adjoint_compat b hsymm ht0 hgen hiso τ hτt
  let lam : F →ₗ[K] K := b 1
  have hlamτ : ∀ z, lam (τ z) = lam z := by
    intro z
    calc
      lam (τ z) = b z 1 := by
        simpa [lam] using (hadj z 1 1).symm
      _ = b 1 z := hsymm z 1
      _ = lam z := rfl
  have hba : ∀ a a', b a a' = lam (τ a * a') := by
    intro a a'
    simpa [lam] using hadj a 1 a'
  have hlam : lam ≠ 0 := by
    intro h
    have hzero : ∀ a', b 1 a' = 0 := by
      intro a'
      have := congrArg (fun f : F →ₗ[K] K => f a') h
      simpa [lam] using this
    exact one_ne_zero (hnd 1 hzero)
  let M : F →ₗ[K] Module.Dual K F :=
    { toFun := fun y => lam.comp (LinearMap.mulLeft K y)
      map_add' := by
        intro y z
        ext w
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.mulLeft_apply,
          add_mul, map_add]
      map_smul' := by
        intro c y
        ext w
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply]
        rw [Algebra.smul_def, mul_assoc, ← Algebra.smul_def, map_smul]
        rfl }
  have hM_inj : Function.Injective M := by
    intro y z h
    have hsub : M (y - z) = 0 := by rw [map_sub, h, sub_self]
    have hker : ∀ w, M w = 0 → w = 0 := by
      intro w hw
      by_contra hw0
      have hlamw : ∀ v, lam (w * v) = 0 := by
        intro v
        have := congrArg (fun φ : Module.Dual K F => φ v) hw
        simpa [M, LinearMap.comp_apply, LinearMap.mulLeft_apply] using this
      apply hlam
      ext v
      have hvv := hlamw (w⁻¹ * v)
      rw [← mul_assoc, mul_inv_cancel₀ hw0, one_mul] at hvv
      exact hvv
    exact sub_eq_zero.mp (hker (y - z) hsub)
  have : FiniteDimensional K F := Module.Finite.of_finite
  have hfin : Module.finrank K F = Module.finrank K (Module.Dual K F) :=
    (Subspace.dual_finrank_eq (K := K) (V := F)).symm
  have hM_surj : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hM_inj
  let fr : F →ₗ[K] F := (FiniteField.frobeniusAlgEquivOfAlgebraic K F).toLinearMap
  have hfr : ∀ z, fr z = z ^ Fintype.card K := by
    intro z
    rw [AlgEquiv.toLinearMap_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply]
  obtain ⟨y₀, hy₀⟩ := hM_surj (lam.comp fr)
  have hy₀_apply : ∀ z, lam (y₀ * z) = lam (z ^ Fintype.card K) := by
    intro z
    have := congrArg (fun φ : Module.Dual K F => φ z) hy₀
    simpa [M, LinearMap.comp_apply, LinearMap.mulLeft_apply, hfr] using this
  have hlamfr : lam.comp fr ≠ 0 := by
    intro h
    apply hlam
    ext z
    obtain ⟨w, rfl⟩ := (FiniteField.frobeniusAlgEquivOfAlgebraic K F).surjective z
    have := congrArg (fun φ : Module.Dual K F => φ w) h
    simpa [LinearMap.comp_apply, fr] using this
  have hy₀0 : y₀ ≠ 0 := by
    intro h0
    have hzero : lam.comp fr = 0 := by rw [← hy₀, h0, map_zero]
    exact hlamfr hzero
  have hτfr : ∀ z, τ (fr z) = fr (τ z) := by
    intro z
    rw [hfr, hfr, map_pow τ z (Fintype.card K)]
  have hτy₀ : τ y₀ = y₀ := by
    have hMeq : M (τ y₀) = M y₀ := by
      ext z
      change lam (τ y₀ * z) = lam (y₀ * z)
      calc
        lam (τ y₀ * z) = lam (τ (y₀ * τ z)) := by
          rw [map_mul τ y₀ (τ z), hττ z]
        _ = lam (y₀ * τ z) := hlamτ _
        _ = lam ((τ z) ^ Fintype.card K) := hy₀_apply (τ z)
        _ = lam (τ (z ^ Fintype.card K)) := by rw [map_pow τ z (Fintype.card K)]
        _ = lam (z ^ Fintype.card K) := hlamτ _
        _ = lam (y₀ * z) := (hy₀_apply z).symm
    exact hM_inj hMeq
  have : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  have hring : ringChar F = 2 := ringChar.eq (R := F) 2
  obtain ⟨u, hu⟩ := (isSquare_iff_exists_sq (fr (y₀⁻¹))).mp
    (FiniteField.isSquare_of_char_two hring (fr (y₀⁻¹)))
  have hu0 : u ≠ 0 := by
    intro h0
    have hr : fr (y₀⁻¹) ≠ 0 := by
      rw [hfr]
      exact pow_ne_zero _ (inv_ne_zero hy₀0)
    rw [hu] at hr
    exact hr (by simp [h0])
  have hu2 : u * u = (y₀⁻¹) ^ Fintype.card K := by
    rw [← pow_two, ← hu, hfr]
  have hτu : τ u = u := by
    have hsq : (τ u) ^ 2 = u ^ 2 := by
      calc
        (τ u) ^ 2 = τ (u ^ 2) := by rw [map_pow]
        _ = τ (fr (y₀⁻¹)) := by rw [← hu]
        _ = fr (τ (y₀⁻¹)) := hτfr _
        _ = fr ((τ y₀)⁻¹) := by rw [map_inv₀]
        _ = fr (y₀⁻¹) := by rw [hτy₀]
        _ = u ^ 2 := hu
    apply frobenius_inj F 2
    simpa [frobenius_def] using hsq
  have hstep : ∀ a a' : F,
      τ (u * a ^ Fintype.card K) * (u * a' ^ Fintype.card K)
        = u * u * ((τ a * a') ^ Fintype.card K) := by
    intro a a'
    rw [map_mul, map_pow, hτu, mul_pow]
    ring
  refine ⟨u, hu0, fun a a' => ?_⟩
  calc
    b (u * a ^ Fintype.card K) (u * a' ^ Fintype.card K)
        = lam (τ (u * a ^ Fintype.card K) * (u * a' ^ Fintype.card K)) := hba _ _
    _ = lam (u * u * ((τ a * a') ^ Fintype.card K)) := by rw [hstep a a']
    _ = lam (((y₀⁻¹) * (τ a * a')) ^ Fintype.card K) := by rw [hu2, ← mul_pow]
    _ = lam (y₀ * ((y₀⁻¹) * (τ a * a'))) := (hy₀_apply _).symm
    _ = lam (τ a * a') := by rw [← mul_assoc, mul_inv_cancel₀ hy₀0, one_mul]
    _ = b a a' := (hba a a').symm

theorem exists_algHom_inv_isometry {K F : Type*} [Field K] [Fintype K] [Field F] [Finite F]
    [Algebra K F] (b : F →ₗ[K] F →ₗ[K] K) (hsymm : ∀ a a', b a a' = b a' a)
    (hnd : ∀ a, (∀ a', b a a' = 0) → a = 0) {t : F} (ht0 : t ≠ 0)
    (hgen : Algebra.adjoin K ({t} : Set F) = ⊤) (hiso : ∀ a a', b (t * a) (t * a') = b a a') :
    ∃ τ : F →ₐ[K] F, (∀ y, τ (τ y) = y) ∧ (∀ a a', b (τ a) (τ a') = b a a') ∧
      ∀ y : F, y ≠ 0 → (∀ a a', b (y * a) (y * a') = b a a') → τ y = y⁻¹ := by
  obtain ⟨τ, hτt, hττ⟩ := exists_algHom_inv b hnd ht0 hgen hiso
  have hc := adjoint_compat b hsymm ht0 hgen hiso τ hτt
  refine ⟨τ, hττ, fun a a' => ?_, fun y hy0 hy => ?_⟩
  · have h1 : b (τ a) (τ a') = b 1 (a * τ a') := by
      have := hc (τ a) 1 (τ a')
      rwa [mul_one, hττ] at this
    have h2 : b a' a = b 1 (τ a' * a) := by
      have := hc a' 1 a
      rwa [mul_one] at this
    rw [h1, hsymm a a', h2, mul_comm]
  · have hadj : ∀ a, b a (τ y) = b a y⁻¹ := fun a => by
      have h1 := hc y a 1
      have h2 := hy a (y⁻¹ * 1)
      rw [← mul_assoc, mul_inv_cancel₀ hy0, one_mul] at h2
      rw [mul_one] at h1 h2
      rw [← h1, h2]
    have key : ∀ a, b (τ y - y⁻¹) a = 0 := fun a => by
      rw [hsymm, map_sub, hadj, sub_self]
    exact sub_eq_zero.mp (hnd _ key)

end CFSG.LinearAlgebra
