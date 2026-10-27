module

public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareField

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace CLSFourGroupScalarSquare

open Matrix FourGroupOddBilinear FourGroupOddUnitary QuaternionMatrices UnitaryHigher Module
open scoped Kronecker

section General

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def centralizerSL (A : GL (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (Subgroup.centralizer {A}).comap SpecialLinearGroup.toGL

theorem mem_centralizerSL {A : GL (Fin n) K} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ centralizerSL A ↔
      (g : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * g := by
  rw [centralizerSL, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Units.ext_iff]
  rfl

theorem exists_four_of_linearMap (hn : 0 < n) (A : GL (Fin n) K)
    {x y : Module.End K (Fin n → K)}
    (hxA : x * Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) =
      Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) * x)
    (hyA : y * Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) =
      Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) * y)
    (hxd : LinearMap.det x = 1) (hyd : LinearMap.det y = 1)
    (hxx : ∃ a : K, x * x = a • 1) (hyy : ∃ a : K, y * y = a • 1)
    (hxy : ∃ a : K, x * y = a • (y * x))
    (hx : ∀ a : K, x ≠ a • 1) (hy : ∀ a : K, y ≠ a • 1) (hxyn : ∀ a : K, x * y ≠ a • 1) :
    ∃ W : Subgroup (LinearFlag.projectiveSL n K),
      W ≤ (centralizerSL A).map (LinearFlag.proj n K) ∧ CFSG.IsElementaryAbelian 2 W ∧
        Nat.card W = 4 := by
  have hmat : ∀ u v : Module.End K (Fin n → K),
      LinearMap.toMatrix' (u * v) = LinearMap.toMatrix' u * LinearMap.toMatrix' v :=
    fun u v => LinearMap.toMatrix'_mul u v
  have hmatsmul : ∀ (a : K) (u : Module.End K (Fin n → K)),
      LinearMap.toMatrix' (a • u) = a • LinearMap.toMatrix' u := fun a u => by
    rw [LinearMap.toMatrix'.map_smul]
  have hmatone : LinearMap.toMatrix' (1 : Module.End K (Fin n → K)) = 1 :=
    LinearMap.toMatrix'_id
  have hmatA : LinearMap.toMatrix' (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K)) = A :=
    LinearMap.toMatrix'_toLin' _
  let x' : SpecialLinearGroup (Fin n) K := ⟨LinearMap.toMatrix' x, by
    rw [LinearMap.det_toMatrix', hxd]⟩
  let y' : SpecialLinearGroup (Fin n) K := ⟨LinearMap.toMatrix' y, by
    rw [LinearMap.det_toMatrix', hyd]⟩
  have hx' : (x' : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix' x := rfl
  have hy' : (y' : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix' y := rfl
  have hcent : ∀ (u : Module.End K (Fin n → K)) (g : SpecialLinearGroup (Fin n) K),
      (g : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix' u →
      u * Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) =
        Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) * u → g ∈ centralizerSL A := by
    intro u g hg hu
    rw [mem_centralizerSL, hg, ← hmatA, ← hmat, ← hmat, hu]
  have hnotscalar : ∀ (u : Module.End K (Fin n → K)), (∀ a : K, u ≠ a • 1) →
      ∀ g : SpecialLinearGroup (Fin n) K, (g : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix' u →
        g ∉ LinearFlag.scalars n K := by
    rintro u hu g hg ⟨c, -, hc⟩
    refine hu c (LinearMap.toMatrix'.injective ?_)
    rw [← hg, hc, hmatsmul, hmatone, scalar_apply, smul_one_eq_diagonal]
  have hsq : ∀ (u : Module.End K (Fin n → K)) (g : SpecialLinearGroup (Fin n) K),
      (g : Matrix (Fin n) (Fin n) K) = LinearMap.toMatrix' u → (∃ a : K, u * u = a • 1) →
        LinearFlag.proj n K g * LinearFlag.proj n K g = 1 := by
    rintro u g hg ⟨a, ha⟩
    rw [← map_mul, LinearFlag.proj_eq_one_iff]
    refine mem_scalars_of_coe_eq_smul hn (a := a) ?_
    rw [SpecialLinearGroup.coe_mul, hg, ← hmat, ha, hmatsmul, hmatone]
  have hpx := hsq x x' hx' hxx
  have hpy := hsq y y' hy' hyy
  have hpxy : LinearFlag.proj n K x' * LinearFlag.proj n K y' =
      LinearFlag.proj n K y' * LinearFlag.proj n K x' := by
    obtain ⟨a, ha⟩ := hxy
    rw [← map_mul, ← map_mul]
    refine proj_eq_of_coe_eq_smul hn (a := a) ?_
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hx', hy', ← hmat, ← hmat, ha,
      hmatsmul]
  have hpx1 : LinearFlag.proj n K x' ≠ 1 := fun h =>
    hnotscalar x hx x' hx' (LinearFlag.proj_eq_one_iff.1 h)
  have hpy1 : LinearFlag.proj n K y' ≠ 1 := fun h =>
    hnotscalar y hy y' hy' (LinearFlag.proj_eq_one_iff.1 h)
  have hpne : LinearFlag.proj n K x' ≠ LinearFlag.proj n K y' := fun h => by
    have h1 : LinearFlag.proj n K (x' * y') = 1 := by rw [map_mul, ← h, hpx]
    exact hnotscalar (x * y) hxyn (x' * y') (by rw [SpecialLinearGroup.coe_mul, hx', hy', hmat])
      (LinearFlag.proj_eq_one_iff.1 h1)
  obtain ⟨W, -, hWle, hW, hWcard⟩ := FourGroup.exists_kleinFour hpx hpy hpxy hpx1 hpy1 hpne
  exact ⟨W, hWle _ (Subgroup.mem_map_of_mem _ (hcent x x' hx' hxA))
    (Subgroup.mem_map_of_mem _ (hcent y y' hy' hyA)), hW, hWcard⟩

section Basis

variable {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem toLin_mul_toLin (b : Basis ι K V) (M N : Matrix ι ι K) :
    Matrix.toLin b b M * Matrix.toLin b b N = Matrix.toLin b b (M * N) := by
  rw [Matrix.toLin_mul b b b]
  rfl

theorem toLin_smul_one (b : Basis ι K V) (a : K) :
    Matrix.toLin b b (a • 1 : Matrix ι ι K) = a • (1 : Module.End K V) := by
  rw [map_smul, Matrix.toLin_one]
  rfl

theorem toLin_commute (b : Basis ι K V) {f : Module.End K V} {M : Matrix ι ι K}
    (hM : M * LinearMap.toMatrix b b f = LinearMap.toMatrix b b f * M) :
    Matrix.toLin b b M * f = f * Matrix.toLin b b M := by
  conv_lhs => rw [← Matrix.toLin_toMatrix b b f]
  conv_rhs => rw [← Matrix.toLin_toMatrix b b f]
  rw [toLin_mul_toLin, toLin_mul_toLin, hM]

end Basis

theorem exists_four_of_matrices (hn : 0 < n) (A : GL (Fin n) K) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (c : Basis ι K (Fin n → K)) {X Y : Matrix ι ι K}
    (hXD : X * LinearMap.toMatrix c c (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K)) =
      LinearMap.toMatrix c c (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K)) * X)
    (hYD : Y * LinearMap.toMatrix c c (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K)) =
      LinearMap.toMatrix c c (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K)) * Y)
    (hXd : X.det = 1) (hYd : Y.det = 1) (hXX : ∃ a : K, X * X = a • 1)
    (hYY : ∃ a : K, Y * Y = a • 1) (hXY : ∃ a : K, X * Y = a • (Y * X))
    (hX : ∀ a : K, X ≠ a • 1) (hY : ∀ a : K, Y ≠ a • 1) (hXYn : ∀ a : K, X * Y ≠ a • 1) :
    ∃ W : Subgroup (LinearFlag.projectiveSL n K),
      W ≤ (centralizerSL A).map (LinearFlag.proj n K) ∧ CFSG.IsElementaryAbelian 2 W ∧
        Nat.card W = 4 := by
  have hsc : ∀ {M : Matrix ι ι K}, (∀ a : K, M ≠ a • 1) → ∀ a : K,
      Matrix.toLin c c M ≠ a • (1 : Module.End K (Fin n → K)) := fun hM a h =>
    hM a (toLin_eq_smul_id c (by rw [h]; rfl))
  refine exists_four_of_linearMap hn A (toLin_commute c hXD) (toLin_commute c hYD)
    (by rw [LinearMap.det_toLin, hXd]) (by rw [LinearMap.det_toLin, hYd]) ?_ ?_ ?_ (hsc hX)
    (hsc hY) (by rw [toLin_mul_toLin]; exact hsc hXYn)
  · obtain ⟨a, ha⟩ := hXX
    exact ⟨a, by rw [toLin_mul_toLin, ha, toLin_smul_one]⟩
  · obtain ⟨a, ha⟩ := hYY
    exact ⟨a, by rw [toLin_mul_toLin, ha, toLin_smul_one]⟩
  · obtain ⟨a, ha⟩ := hXY
    exact ⟨a, by rw [toLin_mul_toLin, toLin_mul_toLin, ha, map_smul]⟩

theorem signDiag_mul_signDiag {ι : Type*} [Fintype ι] [DecidableEq ι] (S T : Finset ι) :
    signDiag (K := K) S * signDiag T = signDiag (symmDiff S T) := by
  rw [signDiag, signDiag, signDiag, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, Finset.mem_symmDiff]

theorem signDiag_mul_comm_of_diag {ι : Type*} [Fintype ι] [DecidableEq ι] {D : Matrix ι ι K}
    (hD : ∀ i j, D i j ≠ 0 → i = j) (S : Finset ι) : signDiag S * D = D * signDiag S :=
  signDiag_mul_comm fun i j h => by rw [hD i j h]

section Square

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_basis_diagonal (h2 : (2 : K) ≠ 0) {f : Module.End K V} {l : K} (hl : l ≠ 0)
    (hf : f * f = (l ^ 2) • 1) :
    ∃ b : Basis (Fin (finrank K V)) K V, ∀ i j, LinearMap.toMatrix b b f i j ≠ 0 → i = j := by
  classical
  set T : Module.End K V := l⁻¹ • f
  have hT : T * T = 1 := by
    rw [smul_mul_smul_comm, hf, smul_smul, show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  have hc := isCompl_eigen h2 hT
  have hfT : ∀ v, f v = l • T v := fun v => by
    simp only [T, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hl, one_smul]
  have hfp : ∀ v ∈ LinearMap.ker (T - 1), f v = l • v := fun v hv => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [hfT, hv]
  have hfm : ∀ v ∈ LinearMap.ker (T + 1), f v = (-l) • v := fun v hv => by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg] at hv
    rw [hfT, hv, smul_neg, neg_smul]
  let b₁ := Basis.ofVectorSpace K (LinearMap.ker (T - 1))
  let b₂ := Basis.ofVectorSpace K (LinearMap.ker (T + 1))
  let b := sumBasis hc b₁ b₂
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, fun i j hij => ?_⟩
  have hij' : LinearMap.toMatrix b b f (e.symm i) (e.symm j) ≠ 0 := by
    simpa [LinearMap.toMatrix_apply] using hij
  rw [toMatrix_sumBasis hc b₁ b₂ hfp hfm] at hij'
  by_contra hne
  exact hij' (diagonal_apply_ne _ (e.symm.injective.ne hne))

end Square

section PairBasis

variable {V : Type*} [AddCommGroup V] [Module K V] {f : Module.End K V} {d : K}

theorem toMatrix_pairBasis {m : ℕ} (c : Basis (Fin 2 × Fin m) K V)
    (hc : ∀ k, c (1, k) = f (c (0, k))) (hff : f * f = d • 1) :
    LinearMap.toMatrix c c f =
      (!![0, d; 1, 0] : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin m) (Fin m) K) := by
  have h0 : ∀ k, f (c (0, k)) = c (1, k) := fun k => (hc k).symm
  have h1 : ∀ k, f (c (1, k)) = d • c (0, k) := fun k => by
    rw [hc, ← Module.End.mul_apply, hff]
    rfl
  ext ⟨s, k⟩ ⟨s', k'⟩
  rw [LinearMap.toMatrix_apply, kronecker_apply]
  fin_cases s' <;> fin_cases s
  all_goals simp [h0, h1, Finsupp.single_apply, one_apply, Prod.ext_iff, eq_comm]

end PairBasis

section Kronecker

theorem one_kronecker_mul (M N : Matrix (Fin 2) (Fin 2) K) :
    ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ M) * ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ N) =
      (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (M * N) := by
  rw [← mul_kronecker_mul, Matrix.one_mul]

theorem one_kronecker_neg (M : Matrix (Fin 2) (Fin 2) K) :
    (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (-M) = (-1 : K) • ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ M) := by
  rw [← kronecker_smul, neg_one_smul]

theorem eq_smul_of_one_kronecker {M : Matrix (Fin 2) (Fin 2) K} {r : K}
    (h : (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ M = r • 1) : M = r • 1 := by
  ext i j
  have := congrFun (congrFun h (0, i)) (0, j)
  simpa [kronecker_apply, one_apply, Prod.ext_iff] using this

end Kronecker

end General

section Nonsquare

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {f : Module.End K V}
  {d : K}

theorem exists_pair_basis [Finite K] [FiniteDimensional K V] [Nontrivial V]
    (hf : ∀ c : K, f ≠ c • 1) (hff : f * f = d • 1) (hd : ∀ l : K, l ^ 2 ≠ d) :
    ∃ m : ℕ, ∃ c : Basis (Fin 2 × Fin m) K V, ∀ k, c (1, k) = f (c (0, k)) := by
  let _ : Field (scalarSquareField f) := (isField_scalarSquareField hff hd).toField
  have : Finite V := Module.finite_of_finite K
  have : Module.Finite (scalarSquareField f) V := Module.Finite.of_finite
  have hmem : f ∈ scalarSquareField f := Algebra.subset_adjoin (Set.mem_singleton f)
  let v : Fin 2 → scalarSquareField f := ![1, ⟨f, hmem⟩]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (fun z : scalarSquareField f => (z : Module.End K V)) hg
    simp only [Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h1
    have h3 : g 0 • (1 : Module.End K V) + g 1 • f = (0 : K) • 1 + (0 : K) • f := by
      simpa using h1
    obtain ⟨e0, e1⟩ := smul_add_smul_inj hf h3
    fin_cases i
    · exact e0
    · exact e1
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rintro x -
    obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hff).mp x.2
    have : x = a • v 0 + b • v 1 := Subtype.ext (by simpa [v] using hab)
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bK : Basis (Fin 2) K (scalarSquareField f) := Basis.mk hli hsp
  let bE := Module.finBasis (scalarSquareField f) V
  refine ⟨_, bK.smulTower bE, fun k => ?_⟩
  rw [Basis.smulTower_apply, Basis.smulTower_apply]
  simp only [bK, Basis.mk_apply, v, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, one_smul]
  rfl

end Nonsquare

theorem odd_scalar_square_linear_centralizer_projective_four_group {K : Type} [Field K]
    {n : ℕ} [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n) (A : GL (Fin n) K) (d : Kˣ)
    (hA : (A : Matrix (Fin n) (Fin n) K) * A = (d : K) • 1) :
    ∃ W : Subgroup (LinearFlag.projectiveSL n K),
      W ≤ (centralizerSL A).map (LinearFlag.proj n K) ∧ CFSG.IsElementaryAbelian 2 W ∧
        Nat.card W = 4 := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn0 : 0 < n := by omega
  set f : Module.End K (Fin n → K) := Matrix.toLin' (A : Matrix (Fin n) (Fin n) K) with hfdef
  have hff : f * f = (d : K) • 1 := by
    have e : Matrix.toLin' ((A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) =
        f * f :=
      Matrix.toLin'_mul _ _
    rw [← e, hA, map_smul, Matrix.toLin'_one]
    rfl
  have hfin : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  by_cases hsq : ∃ l : K, l ^ 2 = d
  ·
    obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact d.ne_zero (by rw [← hl]; ring)
    obtain ⟨b, hb⟩ := exists_basis_diagonal h2 hl0 (by rw [hff, hl])
    let i₀ : Fin (finrank K (Fin n → K)) := ⟨0, by omega⟩
    let i₁ : Fin (finrank K (Fin n → K)) := ⟨1, by omega⟩
    let i₂ : Fin (finrank K (Fin n → K)) := ⟨2, by omega⟩
    have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
    have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
    refine exists_four_of_matrices hn0 A b (X := signDiag {i₀, i₁}) (Y := signDiag {i₀, i₂})
      (signDiag_mul_comm_of_diag hb _) (signDiag_mul_comm_of_diag hb _)
      (by rw [det_signDiag, Finset.card_pair h01]; norm_num)
      (by rw [det_signDiag, Finset.card_pair h02]; norm_num)
      ⟨1, by rw [signDiag_mul_self, one_smul]⟩ ⟨1, by rw [signDiag_mul_self, one_smul]⟩
      ⟨1, by rw [signDiag_comm, one_smul]⟩
      (signDiag_ne_smul h2 (S := {i₀, i₁}) (i := i₀) (j := i₂) (by simp)
        (by simp [h02.symm, h12.symm]))
      (signDiag_ne_smul h2 (S := {i₀, i₂}) (i := i₀) (j := i₁) (by simp) (by simp [h01.symm, h12]))
      ?_
    rw [signDiag_mul_signDiag]
    refine signDiag_ne_smul h2 (i := i₁) (j := i₀) ?_ ?_
    · simp [Finset.mem_symmDiff, h01.symm, h12]
    · simp [Finset.mem_symmDiff]
  ·
    push Not at hsq
    have : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
    have : Nontrivial (Fin n → K) := Function.nontrivial
    have hfns : ∀ c : K, f ≠ c • 1 := by
      intro c hc
      obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → K)
      have h1 : (c ^ 2 - d) • v = 0 := by
        have := congrArg (fun g : Module.End K (Fin n → K) => g v) hff
        simp only [hc, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply,
          smul_smul] at this
        rw [sub_smul, pow_two, this, sub_self]
      exact hsq c (sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hv))
    obtain ⟨m, c, hc⟩ := exists_pair_basis hfns hff hsq
    have hD := toMatrix_pairBasis c hc hff
    have hm : n = 2 * m := by
      rw [← hfin, Module.finrank_eq_card_basis c, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin]
    have hDsupp : ∀ p q : Fin 2 × Fin m, LinearMap.toMatrix c c f p q ≠ 0 → p.2 = q.2 := by
      rintro ⟨s, k⟩ ⟨s', k'⟩ h
      rw [hD, kronecker_apply] at h
      by_contra hk
      exact h (by simp [one_apply, hk])
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    ·
      have hm2 : m = 2 := by omega
      subst hm2
      obtain ⟨⟨a, b, hab⟩, -⟩ := odd_field_two_dimensional_quaternion_matrices hK
      have hkcomm : ∀ M : Matrix (Fin 2) (Fin 2) K,
          ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ M) * LinearMap.toMatrix c c f =
            LinearMap.toMatrix c c f * ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ M) := fun M => by
        rw [hD, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
          Matrix.one_mul, Matrix.mul_one]
      have hkdet : ∀ M : Matrix (Fin 2) (Fin 2) K, M.det = 1 →
          ((1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ M).det = 1 := fun M hM => by
        rw [det_kronecker, det_one, hM, one_pow, one_mul]
      have hI : ∀ r : K, quatI K ≠ r • 1 := fun r h => by
        have := congrFun (congrFun h 0) 1
        simp [quatI] at this
      have hJ : ∀ r : K, quatJ a b ≠ r • 1 := fun r h => by
        have h01 := congrFun (congrFun h 0) 1
        have h00 := congrFun (congrFun h 0) 0
        have h11 := congrFun (congrFun h 1) 1
        simp [quatJ] at h01 h00 h11
        have ha : a = 0 := by
          have h2a : (2 : K) * a = 0 := by linear_combination h00 - h11
          exact (mul_eq_zero.1 h2a).resolve_left h2
        rw [ha, h01] at hab
        norm_num at hab
      have hIJ : ∀ r : K, quatI K * quatJ a b ≠ r • 1 := fun r h => by
        rw [quatI_mul_quatJ] at h
        have h01 := congrFun (congrFun h 0) 1
        have h00 := congrFun (congrFun h 0) 0
        have h11 := congrFun (congrFun h 1) 1
        simp at h01 h00 h11
        have hb : b = 0 := by
          have h2b : (2 : K) * b = 0 := by linear_combination h00 - h11
          exact (mul_eq_zero.1 h2b).resolve_left h2
        rw [hb, h01] at hab
        norm_num at hab
      refine exists_four_of_matrices hn0 A c (X := (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ quatI K)
        (Y := (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ quatJ a b) (hkcomm _) (hkcomm _)
        (hkdet _ det_quatI) (hkdet _ (det_quatJ hab))
        ⟨-1, by rw [one_kronecker_mul, quatI_mul_self, one_kronecker_neg, one_kronecker_one]⟩
        ⟨-1, by rw [one_kronecker_mul, quatJ_mul_self hab, one_kronecker_neg, one_kronecker_one]⟩
        ⟨-1, by rw [one_kronecker_mul, one_kronecker_mul, quatI_mul_quatJ_eq_neg,
          one_kronecker_neg]⟩
        (fun r h => hI r (eq_smul_of_one_kronecker h))
        (fun r h => hJ r (eq_smul_of_one_kronecker h))
        (fun r h => hIJ r (eq_smul_of_one_kronecker (by rw [← one_kronecker_mul]; exact h)))
    ·
      let k₀ : Fin m := ⟨0, by omega⟩
      let k₁ : Fin m := ⟨1, by omega⟩
      let k₂ : Fin m := ⟨2, by omega⟩
      have h01 : k₀ ≠ k₁ := by simp [k₀, k₁, Fin.ext_iff]
      have h02 : k₀ ≠ k₂ := by simp [k₀, k₂, Fin.ext_iff]
      have h12 : k₁ ≠ k₂ := by simp [k₁, k₂, Fin.ext_iff]
      have hblock : ∀ (k : Fin m) (p : Fin 2 × Fin m),
          p ∈ ({(0, k), (1, k)} : Finset (Fin 2 × Fin m)) ↔ p.2 = k := by
        rintro k ⟨s, k'⟩
        fin_cases s <;> simp [Prod.ext_iff, eq_comm]
      have hcomm : ∀ k : Fin m,
          signDiag ({(0, k), (1, k)} : Finset (Fin 2 × Fin m)) * LinearMap.toMatrix c c f =
            LinearMap.toMatrix c c f * signDiag ({(0, k), (1, k)} : Finset (Fin 2 × Fin m)) :=
        fun k => signDiag_mul_comm fun p q h => by rw [hblock, hblock, hDsupp p q h]
      have hdet : ∀ k : Fin m,
          (signDiag (K := K) ({(0, k), (1, k)} : Finset (Fin 2 × Fin m))).det = 1 := fun k => by
        rw [det_signDiag, Finset.card_pair (by simp [Prod.ext_iff])]
        norm_num
      refine exists_four_of_matrices hn0 A c
        (X := signDiag ({(0, k₀), (1, k₀)} : Finset (Fin 2 × Fin m)))
        (Y := signDiag ({(0, k₁), (1, k₁)} : Finset (Fin 2 × Fin m))) (hcomm k₀) (hcomm k₁)
        (hdet k₀) (hdet k₁)
        ⟨1, by rw [signDiag_mul_self, one_smul]⟩ ⟨1, by rw [signDiag_mul_self, one_smul]⟩
        ⟨1, by rw [signDiag_comm, one_smul]⟩
        (signDiag_ne_smul h2 (i := (0, k₀)) (j := (0, k₁)) (by simp)
          (by simp [Prod.ext_iff, h01.symm]))
        (signDiag_ne_smul h2 (i := (0, k₁)) (j := (0, k₀)) (by simp)
          (by simp [Prod.ext_iff, h01]))
        ?_
      rw [signDiag_mul_signDiag]
      refine signDiag_ne_smul h2 (i := (0, k₀)) (j := (0, k₂)) ?_ ?_
      · simp [Finset.mem_symmDiff, Prod.ext_iff, h01]
      · simp [Finset.mem_symmDiff, Prod.ext_iff, h02.symm, h12.symm]

end CLSFourGroupScalarSquare

end CFSG.LocalAnalysis.ComponentInitial
