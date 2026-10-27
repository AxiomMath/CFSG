module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFields

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section FrobTwist

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] [CharP E 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem twistMat_frob (d m : ℕ) (g : SL(2, F)) (i j : Fin 2) :
    iterateFrobenius E 2 d (twistMat E m g i j) = twistMat E (m + d) g i j := by
  rw [twistMat_apply, twistMat_apply, iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]

omit [DecidableEq ι] in
theorem tmatE_frob (d : ℕ) (e : ι → ℕ) (g : SL(2, F)) :
    (tmatE E e g).map (iterateFrobenius E 2 d) = tmatE E (fun i => e i + d) g := by
  ext x' x
  simp only [Matrix.map_apply, tmatE, map_prod, twistMat_frob]

theorem tensorRep_eq_toLin (e : ι → ℕ) (g : SL(2, F)) :
    tensorRep F E e g = Matrix.toLin' (tmatE E e g) := rfl

theorem equiv_frob_twist (d : ℕ) (e : ι → ℕ) {m : ℕ} (A : SL(2, F) → Matrix (Fin m) (Fin m) E)
    (hA : ∀ g, (A g).map (iterateFrobenius E 2 d) = A g)
    (σ : Representation E SL(2, F) (Fin m → E)) (hσ : ∀ g x, σ g x = (A g).mulVec x)
    (Φ : σ.Equiv (tensorRep F E e)) :
    Nonempty (σ.Equiv (tensorRep F E (fun i => e i + d))) := by
  let τ := iterateFrobenius E 2 d
  let φ : (Fin m → E) →ₗ[E] ((ι → Fin 2) → E) := Φ.toLinearEquiv.toLinearMap
  let ψ : ((ι → Fin 2) → E) →ₗ[E] (Fin m → E) := Φ.toLinearEquiv.symm.toLinearMap
  let M : Matrix (ι → Fin 2) (Fin m) E := LinearMap.toMatrix' φ
  let N : Matrix (Fin m) (ι → Fin 2) E := LinearMap.toMatrix' ψ
  have hφ : Matrix.toLin' M = φ := Matrix.toLin'_toMatrix' φ
  have hψ : Matrix.toLin' N = ψ := Matrix.toLin'_toMatrix' ψ
  have hMN : M * N = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hφ, hψ, Matrix.toLin'_one]
    exact LinearMap.ext fun x => Φ.toLinearEquiv.apply_symm_apply x
  have hNM : N * M = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, hφ, hψ, Matrix.toLin'_one]
    exact LinearMap.ext fun x => Φ.toLinearEquiv.symm_apply_apply x
  have hint : ∀ g, M * A g = tmatE E e g * M := by
    intro g
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hφ]
    apply LinearMap.ext
    intro x
    have h1 := equiv_apply Φ g x
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [← hσ g x]
    exact h1.trans (by rw [tensorRep_eq_toLin, Matrix.toLin'_apply]; rfl)
  let M' : Matrix (ι → Fin 2) (Fin m) E := M.map τ
  let N' : Matrix (Fin m) (ι → Fin 2) E := N.map τ
  have hMN' : M' * N' = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one τ (map_zero τ) (map_one τ)]
  have hNM' : N' * M' = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one τ (map_zero τ) (map_one τ)]
  have hint' : ∀ g, M' * A g = tmatE E (fun i => e i + d) g * M' := by
    intro g
    have h1 := congrArg (fun X => X.map τ) (hint g)
    simp only [Matrix.map_mul] at h1
    rw [hA g, tmatE_frob] at h1
    exact h1
  refine ⟨Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (Matrix.toLin' M') (Matrix.toLin' N') ?_ ?_) ?_⟩
  · rw [← Matrix.toLin'_mul, hMN', Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, hNM', Matrix.toLin'_one]
  · intro g
    refine LinearMap.ext fun x => ?_
    show Matrix.toLin' M' (σ g x) = tensorRep F E (fun i => e i + d) g (Matrix.toLin' M' x)
    rw [hσ g x, tensorRep_eq_toLin, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hint' g]

end FrobTwist

section Shift

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

theorem shiftMod_injOn {n d i j : ℕ} (hi : i < n) (hj : j < n)
    (h : (i + d) % n = (j + d) % n) : i = j := by
  have : i ≡ j [MOD n] := Nat.ModEq.add_right_cancel' d h
  exact Nat.ModEq.eq_of_lt_of_lt this hi hj

theorem frobTensor_shift_eq' {n d : ℕ} (hn : 0 < n) (hF : Fintype.card F = 2 ^ n)
    {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n)
    (φ : (tensorRep F k (fun i : J => (i : ℕ) + d)).Equiv (frobTensor F k J)) :
    J.image (fun i => (i + d) % n) = J := by
  classical
  let J' := J.image (fun i => (i + d) % n)
  have hJ' : ∀ i ∈ J', i < n := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact Nat.mod_lt _ hn
  let e₁ : J → ℕ := fun i => ((i : ℕ) + d) % n
  have hrep : ∀ g : SL(2, F), tensorRep F k (fun i : J => (i : ℕ) + d) g = tensorRep F k e₁ g := by
    intro g
    simp only [tensorRep, MonoidHom.coe_mk, OneHom.coe_mk]
    congr 1
    ext x' x
    simp only [tmatE, e₁]
    exact Finset.prod_congr rfl fun i _ => by rw [twistMat_mod hF]
  let φ₁ : (tensorRep F k e₁).Equiv (frobTensor F k J) :=
    Representation.Equiv.mk φ.toLinearEquiv (fun g => by
      have := Representation.IntertwiningMap.isIntertwining' (φ.toIntertwiningMap) g
      rw [hrep g] at this
      exact this)
  let τ : J ≃ J' := Equiv.ofBijective
    (fun i => ⟨((i : ℕ) + d) % n, Finset.mem_image_of_mem _ i.2⟩)
    ⟨fun i j h => Subtype.ext (shiftMod_injOn (hJ i i.2) (hJ j j.2) (congrArg Subtype.val h)),
     fun ⟨j, hj⟩ => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨⟨i, hi⟩, rfl⟩⟩
  let φ₂ : (tensorRep F k e₁).Equiv (frobTensor F k J') :=
    reindexEquiv τ e₁ (fun j : J' => (j : ℕ)) (fun i => rfl)
  exact (frobTensor_nonisomorphic (J := J) (K := J') hF hJ hJ' (φ₁.symm.trans φ₂)).symm

end Shift

section Descent

theorem frobTensor_empty_apply {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
    (g : SL(2, F)) (v : ((↥(∅ : Finset ℕ)) → Fin 2) → k) : frobTensor F k ∅ g v = v := by
  have h1 : tmatE k (fun i : (↥(∅ : Finset ℕ)) => (i : ℕ)) g = 1 := by
    ext x' x
    have : x' = x := Subsingleton.elim x' x
    subst this
    simp [tmatE]
  rw [frobTensor, tensorRep_eq_toLin, h1, Matrix.toLin'_one]
  rfl

theorem descent_core {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F]
    [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) {d : ℕ} (hDcard : Nat.card (EndRing ρ) = 2 ^ d)
    (b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W)
    {E : Type*} [Field E] [CharP E 2] (ιF : F →+* E) (ιD : EndRing ρ →+* E) :
    ∃ J : Finset ℕ, J.Nonempty ∧ (∀ i ∈ J, i < n) ∧
      (letI := ιF.toAlgebra
       Nonempty ((matRepE b ιD).Equiv (frobTensor F E J))) ∧
      J.image (fun i => (i + d) % n) = J ∧
      Module.finrank (EndRing ρ) W = 2 ^ J.card := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have hιDinj : Function.Injective ιD := ιD.injective
  have hfrobD : ∀ a : EndRing ρ, (ιD a) ^ (2 ^ d) = ιD a := by
    intro a
    have : Fintype (EndRing ρ) := Fintype.ofFinite _
    rw [← map_pow]
    congr 1
    have h1 := FiniteField.pow_card a
    have hfc : Fintype.card (EndRing ρ) = 2 ^ d := by
      rw [Fintype.card_eq_nat_card]; exact hDcard
    rwa [hfc] at h1
  let _ : Algebra F E := ιF.toAlgebra
  have hirr := matRepE_isIrreducible b ιD
  obtain ⟨J, ⟨hJn, ⟨Φ⟩⟩, -⟩ := frobTensor_classification hF (matRepE b ιD) hirr
  have hJne : J.Nonempty := by
    by_contra hJ0
    rw [Finset.not_nonempty_iff_eq_empty] at hJ0
    subst hJ0
    obtain ⟨g, hg⟩ := hnt
    apply hg
    have hid : ∀ x, matRepE b ιD g x = x := by
      intro x
      have h1 := equiv_apply Φ g x
      rw [frobTensor_empty_apply] at h1
      exact Φ.toLinearEquiv.injective h1
    have hmat : (matRep b g).map ιD = 1 := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro x
      have := hid x
      rw [matRepE_apply] at this
      simpa [Matrix.toLin'_apply] using this
    have hmat' : matRep b g = 1 := by
      have : (matRep b g).map ιD = (1 : Matrix (Fin _) (Fin _) (EndRing ρ)).map ιD := by
        rw [hmat, Matrix.map_one ιD (map_zero ιD) (map_one ιD)]
      exact Matrix.map_injective hιDinj this
    have hrep : repD ρ g = 1 := by
      apply (LinearMap.toMatrix b b).injective
      rw [show LinearMap.toMatrix b b (repD ρ g) = matRep b g from rfl, hmat',
        LinearMap.toMatrix_one]
    apply LinearMap.ext
    intro w
    have h1 := congrArg (fun f : Module.End (EndRing ρ) W => f w) hrep
    have h2 : repD ρ g w = w := by simpa using h1
    exact h2
  have hdim : Module.finrank (EndRing ρ) W = 2 ^ J.card := by
    have h1 := Φ.toLinearEquiv.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at h1
    exact h1
  have hshift : J.image (fun i => (i + d) % n) = J := by
    have hA : ∀ g, ((matRep b g).map ιD).map (iterateFrobenius E 2 d) = (matRep b g).map ιD := by
      intro g
      ext i j
      simp only [Matrix.map_apply, iterateFrobenius_def]
      exact hfrobD _
    obtain ⟨Φ'⟩ := equiv_frob_twist d (fun i : J => (i : ℕ)) (fun g => (matRep b g).map ιD) hA
      (matRepE b ιD) (fun g x => matRepE_apply b ιD g x) Φ
    exact frobTensor_shift_eq' (by omega) hF hJn (Φ'.symm.trans Φ)
  exact ⟨J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩

theorem binary_SL2_irreducible_Frobenius_descent {n : ℕ} (hn : 1 ≤ n) {F : Type*} [Field F]
    [Fintype F] [CharP F 2] (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W)
    [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card (EndRing ρ) = 2 ^ d ∧
      ∀ b : Module.Basis (Fin (Module.finrank (EndRing ρ) W)) (EndRing ρ) W,
        ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (ιF : F →+* E)
          (ιD : EndRing ρ →+* E) (J : Finset ℕ),
          J.Nonempty ∧ (∀ i ∈ J, i < n) ∧
          (letI := ιF.toAlgebra
           Nonempty ((matRepE b ιD).Equiv (frobTensor F E J))) ∧
          J.image (fun i => (i + d) % n) = J ∧
          Module.finrank (EndRing ρ) W = 2 ^ J.card := by
  classical
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (ZMod 2) (EndRing ρ) := Module.Finite.of_finite
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank (ZMod 2) (EndRing ρ) = d := ⟨_, rfl⟩
  have hDcard : Nat.card (EndRing ρ) = 2 ^ d := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := EndRing ρ)
    rw [hd, Nat.card_zmod] at this
    exact this
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      have : Nat.card (EndRing ρ) = 1 := by rw [hDcard]; rfl
      have h2 := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (EndRing ρ))
      omega
    · exact h
  refine ⟨d, hd1, hDcard, fun b => ?_⟩
  have : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  have hFcard : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨e, E, hEF, hEfin, hEchar, ιF, ιD, -, -, -, -, hιFinj, hιDinj, -, hfrobD, -⟩ :=
    finite_fields_common_extension 2 hn hd1 hFcard hDcard
  obtain ⟨J, hJne, hJn, hΦ, hshift, hdim⟩ := descent_core hn hF ρ hnt hDcard b ιF ιD
  exact ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, hΦ, hshift, hdim⟩

end Descent

end CFSG.QuasithinUnique.Setup.SL2Modules
