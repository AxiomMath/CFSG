module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

structure KacData (τ : Tag) where
  θ : Fin τ.rank → ℤ
  c : Fin τ.rank → ℤ
  G : Matrix (Fin τ.rank) (Fin τ.rank) ℤ
  N : ℤ
  κ : ℤ
  isRoot_θ : IsRoot τ θ
  θ_nonneg : ∀ j, 0 ≤ θ j
  N_pos : 0 < N
  κ_pos : 0 < κ
  κ_smul_c : κ • c = τ.symmetrizedCartan *ᵥ θ
  θ_dot_c : θ ⬝ᵥ c = 2
  G_mul : G * τ.symmetrizedCartan = N • 1
  G_symm : Gᵀ = G

namespace KacData

variable {τ : Tag} (K : KacData τ)

@[expose] def h : ℤ := 1 + ∑ j, K.θ j

@[expose] def Λ (p : ℕ) (μ : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  K.h • μ - (p : ℤ) • (fun _ => (1 : ℤ))

@[expose] def Q (p : ℕ) (μ : Fin τ.rank → ℤ) : ℤ := K.Λ p μ ⬝ᵥ (K.G *ᵥ K.Λ p μ)

@[expose] def IsNormal (p : ℕ) (μ : Fin τ.rank → ℤ) : Prop := (∀ i, 0 ≤ μ i) ∧ K.θ ⬝ᵥ μ ≤ p

theorem h_pos : 0 < K.h := by
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => K.θ_nonneg j
  rw [h]
  omega

theorem symmetrizedCartan_transpose : τ.symmetrizedCartanᵀ = τ.symmetrizedCartan := by
  ext i j
  exact symmetrizedCartan_symm τ j i

theorem mul_G : τ.symmetrizedCartan * K.G = K.N • 1 := by
  have h := congrArg Matrix.transpose K.G_mul
  rwa [Matrix.transpose_mul, K.G_symm, symmetrizedCartan_transpose, Matrix.transpose_smul,
    Matrix.transpose_one] at h

theorem dot_G_comm (x y : Fin τ.rank → ℤ) : x ⬝ᵥ (K.G *ᵥ y) = y ⬝ᵥ (K.G *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, K.G_symm, dotProduct_comm]

theorem Q_nonneg (p : ℕ) (μ : Fin τ.rank → ℤ) : 0 ≤ K.Q p μ := by
  set u := K.G *ᵥ K.Λ p μ with hu
  have h1 : iform u u = K.N * K.Q p μ := by
    rw [← dotProduct_mulVec_eq_iform, hu, Matrix.mulVec_mulVec, mul_G, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_comm, Q]
  have h2 : 0 ≤ iform u u := by
    by_cases hu0 : u = 0
    · rw [hu0]
      simp [iform]
    · exact (iform_self_pos hu0).le
  rw [h1] at h2
  exact nonneg_of_mul_nonneg_right (by linarith) K.N_pos

@[expose] def dualReflect (i : Fin τ.rank) (μ : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  fun j => μ j - τ.cartan i j * μ i

omit K in
theorem reflect_dot_dualReflect (i : Fin τ.rank) (β μ : Fin τ.rank → ℤ) :
    reflect τ i β ⬝ᵥ dualReflect i μ = β ⬝ᵥ μ := by
  have hii : τ.cartan i i = 2 := τ.cartan_self i
  set ci : Fin τ.rank → ℤ := fun j => τ.cartan i j with hci
  have hr : reflect τ i β = β - (ci ⬝ᵥ β) • (Pi.single i 1 : Fin τ.rank → ℤ) := rfl
  have hd : dualReflect i μ = μ - μ i • ci := by
    funext j
    simp only [dualReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hci]
    ring
  have hcii : ci i = 2 := hii
  rw [hr, hd]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    single_dotProduct, one_mul]
  rw [hcii, dotProduct_comm β ci]
  ring

theorem B_dot_G (x y : Fin τ.rank → ℤ) :
    (τ.symmetrizedCartan *ᵥ x) ⬝ᵥ (K.G *ᵥ y) = K.N * (x ⬝ᵥ y) := by
  calc (τ.symmetrizedCartan *ᵥ x) ⬝ᵥ (K.G *ᵥ y)
      = (K.G *ᵥ y) ⬝ᵥ (τ.symmetrizedCartan *ᵥ x) := dotProduct_comm _ _
    _ = ((K.G *ᵥ y) ᵥ* τ.symmetrizedCartan) ⬝ᵥ x := Matrix.dotProduct_mulVec _ _ _
    _ = (τ.symmetrizedCartanᵀ *ᵥ (K.G *ᵥ y)) ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
    _ = ((τ.symmetrizedCartan * K.G) *ᵥ y) ⬝ᵥ x := by
        rw [symmetrizedCartan_transpose, Matrix.mulVec_mulVec]
    _ = K.N * (x ⬝ᵥ y) := by
        rw [mul_G, Matrix.smul_mulVec, Matrix.one_mulVec, smul_dotProduct, smul_eq_mul,
          dotProduct_comm]

theorem symmetrizer_mul_cartan_dot (i : Fin τ.rank) (y : Fin τ.rank → ℤ) :
    τ.symmetrizer i i * ((fun j => τ.cartan i j) ⬝ᵥ (K.G *ᵥ y)) = K.N * y i := by
  have hc : τ.symmetrizer i i • (fun j => τ.cartan i j) =
      τ.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply]
    rw [symmetrizedCartan_symm τ j i, symmetrizedCartan_apply]
  rw [← smul_eq_mul, ← smul_dotProduct, hc, K.B_dot_G, single_dotProduct, one_mul]

theorem symmetrizer_mul_Q_reflect (p : ℕ) (i : Fin τ.rank) (μ : Fin τ.rank → ℤ) :
    τ.symmetrizer i i * K.Q p (dualReflect i μ) =
      τ.symmetrizer i i * K.Q p μ + 2 * K.h * K.N * p * μ i := by
  set ci : Fin τ.rank → ℤ := fun j => τ.cartan i j with hci
  set t := K.h * μ i with ht
  have hΛ : K.Λ p (dualReflect i μ) = K.Λ p μ - t • ci := by
    funext j
    simp only [Λ, dualReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hci, ht]
    ring
  have hcii : ci i = 2 := τ.cartan_self i
  have h1 := K.symmetrizer_mul_cartan_dot i (K.Λ p μ)
  have h2 := K.symmetrizer_mul_cartan_dot i ci
  rw [← hci] at h1 h2
  rw [hcii] at h2
  have hΛi : K.Λ p μ i = K.h * μ i - p := by simp [Λ]
  have hexp : K.Q p (dualReflect i μ) = K.Q p μ - 2 * t * (ci ⬝ᵥ (K.G *ᵥ K.Λ p μ)) +
      t * t * (ci ⬝ᵥ (K.G *ᵥ ci)) := by
    have hsym := K.dot_G_comm (K.Λ p μ) ci
    simp only [Q, hΛ, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hsym]
    ring
  rw [hexp]
  linear_combination (-(2 * t)) * h1 + t * t * h2 - (2 * t * K.N) * hΛi

theorem corootPair_θ (v : Fin τ.rank → ℤ) : corootPair K.θ v = K.c ⬝ᵥ v := by
  have h := corootPair_mul K.isRoot_θ v
  have hθθ : iform K.θ K.θ = 2 * K.κ := by
    rw [← dotProduct_mulVec_eq_iform, ← K.κ_smul_c, dotProduct_smul, K.θ_dot_c, smul_eq_mul]
    ring
  have hθv : iform K.θ v = K.κ * (K.c ⬝ᵥ v) := by
    rw [iform_comm, ← dotProduct_mulVec_eq_iform, ← K.κ_smul_c, dotProduct_smul, smul_eq_mul,
      dotProduct_comm]
  rw [hθθ, hθv] at h
  have hκ := K.κ_pos
  have : (corootPair K.θ v - K.c ⬝ᵥ v) * (2 * K.κ) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · omega

theorem κ_mul_c_dot (y : Fin τ.rank → ℤ) : K.κ * (K.c ⬝ᵥ (K.G *ᵥ y)) = K.N * (K.θ ⬝ᵥ y) := by
  rw [← smul_eq_mul, ← smul_dotProduct, K.κ_smul_c, K.B_dot_G]

@[expose] def affineReflect (p : ℕ) (μ : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  μ - (K.θ ⬝ᵥ μ - p) • K.c

theorem rootReflection_dot_affineReflect (p : ℕ) (β μ : Fin τ.rank → ℤ) :
    (rootReflection K.θ • β) ⬝ᵥ K.affineReflect p μ = β ⬝ᵥ μ - p * (K.c ⬝ᵥ β) := by
  rw [rootReflection_smul K.isRoot_θ, K.corootPair_θ, affineReflect]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [K.θ_dot_c, dotProduct_comm K.c β]
  ring

theorem κ_mul_Q_affine (p : ℕ) (μ : Fin τ.rank → ℤ) :
    K.κ * K.Q p (K.affineReflect p μ) =
      K.κ * K.Q p μ - 2 * K.h * K.N * p * (K.θ ⬝ᵥ μ - p) := by
  set s := K.h * (K.θ ⬝ᵥ μ - p) with hs
  have hΛ : K.Λ p (K.affineReflect p μ) = K.Λ p μ - s • K.c := by
    funext j
    simp only [Λ, affineReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hs]
    ring
  have h1 := K.κ_mul_c_dot (K.Λ p μ)
  have h2 := K.κ_mul_c_dot K.c
  rw [K.θ_dot_c] at h2
  have hθΛ : K.θ ⬝ᵥ K.Λ p μ = K.h * (K.θ ⬝ᵥ μ) - p * (K.h - 1) := by
    simp only [Λ, dotProduct_sub, dotProduct_smul, smul_eq_mul, h]
    have : K.θ ⬝ᵥ (fun _ => (1 : ℤ)) = ∑ j, K.θ j := by simp [dotProduct]
    rw [this]
    ring
  have hsym := K.dot_G_comm (K.Λ p μ) K.c
  simp only [Q, hΛ, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hsym]
  rw [hθΛ] at h1
  linear_combination (-(2 * s)) * h1 + s * s * h2

theorem exists_normal (p : ℕ) (hp : 0 < p) (lam : Fin τ.rank → ℤ) :
    ∃ (w : WeylGroup τ) (μ : Fin τ.rank → ℤ), (∀ β : Fin τ.rank → ℤ,
      (p : ℤ) ∣ (w • β) ⬝ᵥ μ - β ⬝ᵥ lam) ∧ K.IsNormal p μ := by
  suffices h : ∀ n : ℕ, ∀ lam : Fin τ.rank → ℤ, K.Q p lam < n →
      ∃ (w : WeylGroup τ) (μ : Fin τ.rank → ℤ), (∀ β : Fin τ.rank → ℤ,
        (p : ℤ) ∣ (w • β) ⬝ᵥ μ - β ⬝ᵥ lam) ∧ K.IsNormal p μ from
    h ((K.Q p lam).toNat + 1) lam (by have := K.Q_nonneg p lam; omega)
  have hh := K.h_pos
  have hN := K.N_pos
  have hκ := K.κ_pos
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  intro n
  induction n with
  | zero => exact fun lam hlam => absurd hlam (not_lt.2 (by exact_mod_cast K.Q_nonneg p lam))
  | succ n ih =>
    intro lam hlam
    by_cases hneg : ∃ i, lam i < 0
    · obtain ⟨i, hi⟩ := hneg
      have hd := symmetrizer_pos τ i
      have hQ := K.symmetrizer_mul_Q_reflect p i lam
      have hlt : K.Q p (dualReflect i lam) < K.Q p lam := by
        by_contra hge
        push Not at hge
        have h1 : 0 < 2 * K.h * K.N * p * -lam i :=
          mul_pos (mul_pos (mul_pos (mul_pos two_pos hh) hN) hpz) (neg_pos.2 hi)
        nlinarith
      obtain ⟨w, μ, hw, hμ⟩ := ih (dualReflect i lam) (by omega)
      refine ⟨w * simple τ i, μ, fun β => ?_, hμ⟩
      have := hw (simple τ i • β)
      rw [simple_smul, reflect_dot_dualReflect] at this
      rwa [mul_smul, simple_smul]
    · push Not at hneg
      by_cases hθ : (p : ℤ) < K.θ ⬝ᵥ lam
      · have hQ := K.κ_mul_Q_affine p lam
        have hlt : K.Q p (K.affineReflect p lam) < K.Q p lam := by
          by_contra hge
          push Not at hge
          have h1 : 0 < 2 * K.h * K.N * p * (K.θ ⬝ᵥ lam - p) :=
            mul_pos (mul_pos (mul_pos (mul_pos two_pos hh) hN) hpz) (by linarith)
          nlinarith
        obtain ⟨w, μ, hw, hμ⟩ := ih (K.affineReflect p lam) (by omega)
        refine ⟨w * rootReflection K.θ, μ, fun β => ?_, hμ⟩
        have h1 := hw (rootReflection K.θ • β)
        rw [K.rootReflection_dot_affineReflect] at h1
        rw [mul_smul]
        have h2 : (p : ℤ) ∣ p * (K.c ⬝ᵥ β) := dvd_mul_right _ _
        have := dvd_add h1 (dvd_neg.2 h2)
        convert this using 1
        ring
      · exact ⟨1, lam, fun β => by simp, hneg, by linarith⟩

omit K in
theorem rootChar_eq_zpow {L : Type} [Field L] (ζ : Lˣ) (lam : Fin τ.rank → ℤ)
    (β : Fin τ.rank → ℤ) : rootChar (fun i => ζ ^ lam i) β = ζ ^ (β ⬝ᵥ lam) := by
  simp only [rootChar, ← _root_.zpow_mul, dotProduct]
  rw [← Finset.prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

theorem exists_weyl_normal {L : Type} [Field L] {p : ℕ} (hp : 0 < p) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot (ζ : L) p)
    (a : Fin τ.rank → Lˣ) (ha : ∀ i, a i ^ p = 1) :
    ∃ (w : WeylGroup τ) (μ : Fin τ.rank → ℤ), K.IsNormal p μ ∧
      ∀ β : Fin τ.rank → ℤ, rootChar a β = ζ ^ ((w • β) ⬝ᵥ μ) := by
  have ha1 : ∀ i, ((a i : L)) ^ p = 1 := fun i => by
    rw [← Units.val_pow_eq_pow_val, ha i, Units.val_one]
  have : NeZero p := ⟨hp.ne'⟩
  choose k _ hk using fun i => hζ.eq_pow_of_pow_eq_one (ha1 i)
  set lam : Fin τ.rank → ℤ := fun i => (k i : ℤ) with hlam
  have ha' : a = fun i => ζ ^ lam i := by
    funext i
    refine Units.ext ?_
    rw [← hk i]
    simp [hlam]
  obtain ⟨w, μ, hw, hμ⟩ := K.exists_normal p hp lam
  refine ⟨w, μ, hμ, fun β => ?_⟩
  rw [ha', rootChar_eq_zpow]
  obtain ⟨m, hm⟩ := hw β
  have hζp : ζ ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)
  have : (w • β) ⬝ᵥ μ = β ⬝ᵥ lam + p * m := by linarith
  rw [this, _root_.zpow_add, _root_.zpow_mul, hζp, one_zpow, mul_one]

end KacData

section Data


@[expose] noncomputable def kacF4 : KacData Tag.F4 where
  θ := ![2, 3, 4, 2]
  c := ![1, 0, 0, 0]
  G := !![2, 3, 4, 2; 3, 6, 8, 4; 4, 8, 12, 6; 2, 4, 6, 4]
  N := 2
  κ := 2
  isRoot_θ := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  θ_nonneg := show ∀ j : Fin 4, (0 : ℤ) ≤ ![2, 3, 4, 2] j by decide
  N_pos := by decide
  κ_pos := by decide
  κ_smul_c := by decide +kernel
  θ_dot_c := by decide +kernel
  G_mul := by decide +kernel
  G_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def kacE7 : KacData Tag.E7 where
  θ := ![2, 2, 3, 4, 3, 2, 1]
  c := ![1, 0, 0, 0, 0, 0, 0]
  G := !![4, 4, 6, 8, 6, 4, 2; 4, 7, 8, 12, 9, 6, 3; 6, 8, 12, 16, 12, 8, 4;
    8, 12, 16, 24, 18, 12, 6; 6, 9, 12, 18, 15, 10, 5; 4, 6, 8, 12, 10, 8, 4;
    2, 3, 4, 6, 5, 4, 3]
  N := 2
  κ := 1
  isRoot_θ := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  θ_nonneg := show ∀ j : Fin 7, (0 : ℤ) ≤ ![2, 2, 3, 4, 3, 2, 1] j by decide
  N_pos := by decide
  κ_pos := by decide
  κ_smul_c := by decide +kernel
  θ_dot_c := by decide +kernel
  G_mul := by decide +kernel
  G_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def kacE8 : KacData Tag.E8 where
  θ := ![2, 3, 4, 6, 5, 4, 3, 2]
  c := ![0, 0, 0, 0, 0, 0, 0, 1]
  G := !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]
  N := 1
  κ := 1
  isRoot_θ := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  θ_nonneg := show ∀ j : Fin 8, (0 : ℤ) ≤ ![2, 3, 4, 6, 5, 4, 3, 2] j by decide
  N_pos := by decide
  κ_pos := by decide
  κ_smul_c := by decide +kernel
  θ_dot_c := by decide +kernel
  G_mul := by decide +kernel
  G_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def kacE6 : KacData Tag.E6 where
  θ := ![1, 2, 2, 3, 2, 1]
  c := ![0, 1, 0, 0, 0, 0]
  G := !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]
  N := 3
  κ := 1
  isRoot_θ := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  θ_nonneg := show ∀ j : Fin 6, (0 : ℤ) ≤ ![1, 2, 2, 3, 2, 1] j by decide
  N_pos := by decide
  κ_pos := by decide
  κ_smul_c := by decide +kernel
  θ_dot_c := by decide +kernel
  G_mul := by decide +kernel
  G_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def kacD4 : KacData Tag.D4 where
  θ := ![1, 1, 2, 1]
  c := ![0, 0, 1, 0]
  G := !![2, 1, 2, 1; 1, 2, 2, 1; 2, 2, 4, 2; 1, 1, 2, 2]
  N := 2
  κ := 1
  isRoot_θ := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  θ_nonneg := show ∀ j : Fin 4, (0 : ℤ) ≤ ![1, 1, 2, 1] j by decide
  N_pos := by decide
  κ_pos := by decide
  κ_smul_c := by decide +kernel
  θ_dot_c := by decide +kernel
  G_mul := by decide +kernel
  G_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def kacG2 : KacData Tag.G2 where
  θ := ![2, 3]
  c := ![1, 0]
  G := !![2, 3; 3, 6]
  N := 3
  κ := 3
  isRoot_θ := isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  θ_nonneg := show ∀ j : Fin 2, (0 : ℤ) ≤ ![2, 3] j by decide
  N_pos := by decide
  κ_pos := by decide
  κ_smul_c := by decide +kernel
  θ_dot_c := by decide +kernel
  G_mul := by decide +kernel
  G_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

end Data

end CFSG.HardMathSupport.Timmesfeld.CrossChar
