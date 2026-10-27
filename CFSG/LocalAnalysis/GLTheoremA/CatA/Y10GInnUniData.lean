module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU mem_heldGU)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamUni InnDiagKind InnDiagUni)

theorem exists_qplus1_root {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    {μ : K} (hμ : μ ≠ 0) (hμq : μ ^ q = μ) : ∃ c : K, c ≠ 0 ∧ c ^ (q + 1) = μ := by
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    by_contra hlt
    have hle1 : q ≤ 1 := by omega
    have := Nat.pow_le_pow_left hle1 2
    rw [one_pow] at this
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  let u : Kˣ := Units.mk0 μ hμ
  have hu : u ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]
    exact hg u
  obtain ⟨k, hk⟩ := hu
  have hk' : g ^ k = u := hk
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hK]
  have hμ1 : μ ^ (q - 1) = 1 := by
    have h1 : μ ^ (q - 1) * μ = 1 * μ := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
      exact hμq
    exact mul_right_cancel₀ hμ h1
  have hupow : g ^ (k * (q - 1)) = 1 := by
    have : u ^ (q - 1) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0]
      exact hμ1
    rw [pow_mul, hk', this]
  have hdvd : q ^ 2 - 1 ∣ k * (q - 1) := by
    rw [← hcard, ← hord, orderOf_dvd_iff_pow_eq_one]
    exact hupow
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [hfac] at hdvd
  have hq1 : 0 < q - 1 := by omega
  have hdvd' : q + 1 ∣ k := by
    rw [mul_comm k (q - 1)] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hq1 hdvd
  obtain ⟨j, hj⟩ := hdvd'
  refine ⟨((g ^ j : Kˣ) : K), (g ^ j).ne_zero, ?_⟩
  have : (g ^ j) ^ (q + 1) = u := by
    rw [← pow_mul, mul_comm j (q + 1), ← hj, hk']
  have h2 := congrArg (fun x : Kˣ => (x : K)) this
  simpa [u] using h2

theorem two_eq_zero_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    (2 : K) = 0 := by
  obtain ⟨p, hchar, k, hp, hQ⟩ := CFSG.LieType.SemisimpleCentralizers.Held.hct_exists_char_pow hK
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [pow_zero] at hQ
    rw [hK, hQ] at h1
    norm_num at h1
  have hdvd : p ∣ 2 ^ n := by
    rw [hQ]
    exact dvd_pow_self p hk0
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact_mod_cast CharP.cast_eq_zero K 2

theorem exists_frob_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ τ : K ≃+* K, (∀ x, τ x = x ^ 2 ^ n) ∧ ∀ x, τ (τ x) = x := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card hK
  have hchar : CharP K 2 := by
    obtain ⟨p, hchar, k, hp, hQ⟩ := CFSG.LieType.SemisimpleCentralizers.Held.hct_exists_char_pow hK
    have hp2 : p = 2 := by
      have hk0 : k ≠ 0 := by
        rintro rfl
        have h1 : 1 < Nat.card K := Finite.one_lt_card
        rw [hK] at h1
        have : 2 ^ n = 1 := by
          rw [pow_zero] at hQ
          omega
        have h3 : (2 ^ n) ^ 2 = 1 := by rw [this]; norm_num
        omega
      have hdvd : p ∣ 2 ^ n := by
        rw [hQ]
        exact dvd_pow_self p hk0
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
    subst hp2
    exact hchar
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let f : K →+* K := iterateFrobenius K 2 n
  have hf : Function.Bijective f := by
    constructor
    · exact f.injective
    · exact Finite.injective_iff_surjective.mp f.injective
  refine ⟨RingEquiv.ofBijective f hf, fun x => ?_, fun x => ?_⟩
  · show iterateFrobenius K 2 n x = x ^ 2 ^ n
    rw [iterateFrobenius_def]
  · haveI := Fintype.ofFinite K
    have hcard : Fintype.card K = (2 ^ n) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hK]
    show iterateFrobenius K 2 n (iterateFrobenius K 2 n x) = x
    rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul]
    rw [show (2 : ℕ) ^ n * 2 ^ n = Fintype.card K from by rw [hcard, sq]]
    exact FiniteField.pow_card x

theorem val_scalar_gl' {d : ℕ} {K : Type} [Field K] (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (c : K) • (1 : Matrix (Fin d) (Fin d) K) := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]

theorem scalar_comm_gl {d : ℕ} {K : Type} [Field K] (c : Kˣ) (x : GL (Fin d) K) :
    Matrix.GeneralLinearGroup.scalar (Fin d) c * x = x * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_scalar_gl', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

theorem map_smul_pow {d : ℕ} {K : Type} [Field K] (q : ℕ) (c : K) (M : Matrix (Fin d) (Fin d) K) :
    (c • M).map (fun x => x ^ q) = (c ^ q) • M.map (fun x => x ^ q) := by
  ext i j
  simp [mul_pow]

theorem exists_heldGU_of_GUSet {K : Type} [Field K] [Finite K] {d n : ℕ} {τ : K ≃+* K}
    (hτq : ∀ x, τ x = x ^ 2 ^ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hτ : ∀ x, τ (τ x) = x)
    (A₀ : GL (Fin d) K) (hA₀ : A₀ ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) :
    ∃ A : GL (Fin d) K, A ∈ heldGU d K τ hτ ∧ ∀ g : GL (Fin d) K, A * g * A⁻¹ = A₀ * g * A₀⁻¹ := by
  obtain ⟨μ, hμ0, hμq, hA⟩ := hA₀
  obtain ⟨c, hc0, hcμ⟩ := exists_qplus1_root hK hμ0 hμq
  let σ : Kˣ := Units.mk0 c⁻¹ (inv_ne_zero hc0)
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) σ * A₀, ?_, ?_⟩
  · rw [mem_heldGU]
    have hτf : (⇑τ) = fun x => x ^ 2 ^ n := funext hτq
    have hval : ((Matrix.GeneralLinearGroup.scalar (Fin d) σ * A₀ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = (c⁻¹ : K) • (A₀ : Matrix (Fin d) (Fin d) K) := by
      rw [Units.val_mul, val_scalar_gl', Matrix.smul_mul, Matrix.one_mul]
      rfl
    have hscal : (c⁻¹ : K) ^ 2 ^ n * c⁻¹ * μ = 1 := by
      rw [← hcμ, pow_succ, inv_pow]
      have hc' : c ^ 2 ^ n ≠ 0 := pow_ne_zero _ hc0
      field_simp
    rw [hval, hτf, map_smul_pow, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hA, smul_smul, hscal, one_smul]
  · intro g
    rw [mul_inv_rev, show Matrix.GeneralLinearGroup.scalar (Fin d) σ * A₀ * g * (A₀⁻¹ *
      (Matrix.GeneralLinearGroup.scalar (Fin d) σ)⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin d) σ * (A₀ * g * A₀⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) σ)⁻¹ by group]
    rw [scalar_comm_gl, mul_inv_cancel_right]

theorem unitary_marking_data {S : Type} [Group S] {α : MulAut S} {d n : ℕ}
    (hcen : Subgroup.center S = ⊥) {K : Type} [Field K] [Finite K] (hcard : Nat.card K = (2 ^ n) ^ 2)
    (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj (StatedSU d (2 ^ n) K))
    (u : MulAut (LargeEvenProj (StatedSU d (2 ^ n) K))) (A₀ : GL (Fin d) K)
    (hA₀ : A₀ ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hAu : LargeEvenGraphAut (LargeEvenProjMk (StatedSU d (2 ^ n) K))
      (fun h h' => (h' : GL (Fin d) K) = A₀ * (h : GL (Fin d) K) * A₀⁻¹) u)
    (hind : LargeEvenInduces θ (fun s s' => s' = α s) u) :
    ∃ (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x), (∀ x, τ x = x ^ 2 ^ n) ∧
      ∃ (A : GL (Fin d) K) (e : S ≃* LargeEvenProj (StatedSU d (2 ^ n) K)),
        A ∈ heldGU d K τ hτ ∧ (∀ l : S, e (α l) = u (e l)) ∧
        ∀ h h' : ↥(StatedSU d (2 ^ n) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
          u (LargeEvenProjMk (StatedSU d (2 ^ n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ n) K) h' := by
  obtain ⟨τ, hτq, hτ⟩ := exists_frob_equiv hcard
  obtain ⟨A, hA, hAconj⟩ := exists_heldGU_of_GUSet hτq hcard hτ A₀ hA₀
  let e0 : S ≃* LargeEvenProj (StatedSU d (2 ^ n) K) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ
  exact ⟨τ, hτ, hτq, A, e0, hA, fun l => (hind l (α l) rfl).symm,
    fun h h' hh' => hAu h h' (hh'.trans (hAconj _))⟩

theorem innDiag_unitary_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamUni labK) (hin : InnDiagKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x),
      (∀ x, τ x = x ^ 2 ^ labK.n) ∧ Nat.card K = (2 ^ labK.n) ^ 2 ∧ 3 ≤ d ∧ (d = 3 → 2 ≤ labK.n) ∧
      ∃ (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (StatedSU d (2 ^ labK.n) K)))
        (e : S ≃* LargeEvenProj (StatedSU d (2 ^ labK.n) K)),
        A ∈ heldGU d K τ hτ ∧ (∀ l : S, e (α l) = u (e l)) ∧
        ∀ h h' : ↥(StatedSU d (2 ^ labK.n) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
          u (LargeEvenProjMk (StatedSU d (2 ^ labK.n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ labK.n) K) h' := by
  unfold InnDiagKind at hin
  obtain ⟨_, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ⟨ht, hr⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeUnitary at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A₀, hA₀, hAu⟩ := hu
    simp only [LargeEvenInLambda2, ht] at hlam
    obtain ⟨τ, hτ, hτq, A, e, hA, hαu, hgraph⟩ := unitary_marking_data hcen hcard θ u A₀ hA₀ hAu hind
    exact ⟨K, hK, hKf, labK.rank + 1, τ, hτ, hτq, hcard, by omega, fun h3 => hlam.2.2 (by omega),
      A, u, e, hA, hαu, hgraph⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht, hr] at hraw
    unfold LargeEvenRecipeUnitary at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A₀, hA₀, hAu⟩ := hu
    obtain ⟨τ, hτ, hτq, A, e, hA, hαu, hgraph⟩ :=
      unitary_marking_data (d := 4) hcen hcard θ u A₀ hA₀ hAu hind
    exact ⟨K, hK, hKf, 4, τ, hτ, hτq, hcard, by norm_num, fun h => absurd h (by norm_num),
      A, u, e, hA, hαu, hgraph⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
