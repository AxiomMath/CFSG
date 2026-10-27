module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXLangSel2
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141g
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
open scoped MatrixGroups commutatorElement

section Matrices

variable {L : Type} [Field L] [CharP L 2]

private theorem eq_one_of_pow_two_pow {x : L} {n : ℕ} (h : x ^ 2 ^ n = 1) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (x - 1) ^ 2 ^ n = 0 := by rw [sub_pow_char_pow, one_pow, h, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).1 h4)

private theorem exists_omega [IsAlgClosed L] : ∃ ω : L, ω ^ 2 + ω + 1 = 0 := by
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree = 2 := by
    compute_degree!
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L)
    (by rw [hdeg]; norm_num)
  exact ⟨ω, by simpa using hω⟩

section Mat

variable (ω : L) (hω : ω ^ 2 + ω + 1 = 0)

include hω

private theorem mat_TT :
    (!![0, ω ^ 2, 0; ω, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) L) *
      !![0, ω ^ 2, 0; ω, 0, 0; 0, 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem mat_TT_unitary :
    ((!![0, ω ^ 2, 0; ω, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) L).map (· ^ 2))ᵀ *
      !![0, ω ^ 2, 0; ω, 0, 0; 0, 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem mat_hh :
    (!![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω] : Matrix (Fin 3) (Fin 3) L) *
      !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω] = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem mat_hh_unitary :
    ((!![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω] : Matrix (Fin 3) (Fin 3) L).map (· ^ 2))ᵀ *
      !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem mat_comm :
    (!![0, ω ^ 2, 0; ω, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) L) * !![0, 1, 0; 1, 0, 0; 0, 0, 1] *
      !![0, ω ^ 2, 0; ω, 0, 0; 0, 0, 1] * !![0, 1, 0; 1, 0, 0; 0, 0, 1] =
        !![ω, 0, 0; 0, ω ^ 2, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem mat_diag_eq_one (X : SL(3, L))
    (hX : (X : Matrix (Fin 3) (Fin 3) L) * !![ω, 0, 0; 0, ω ^ 2, 0; 0, 0, 1] =
      !![ω, 0, 0; 0, ω ^ 2, 0; 0, 0, 1] * (X : Matrix (Fin 3) (Fin 3) L))
    {n : ℕ} (hXn : X ^ 2 ^ n = 1) : X = 1 := by
  have hne1 : ω ≠ 1 := by intro h; subst h; grind
  have hne2 : ω ^ 2 ≠ 1 := by intro h; grind
  have hne3 : ω ≠ ω ^ 2 := by intro h; grind
  have hD : (!![ω, 0, 0; 0, ω ^ 2, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![ω, ω ^ 2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hD] at hX
  have hinj : Function.Injective (![ω, ω ^ 2, 1] : Fin 3 → L) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> grind
  have hoff : ∀ i j : Fin 3, i ≠ j → (X : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun hX i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : ((![ω, ω ^ 2, 1] : Fin 3 → L) j - (![ω, ω ^ 2, 1] : Fin 3 → L) i) *
        (X : Matrix (Fin 3) (Fin 3) L) i j = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (hinj (sub_eq_zero.1 h3).symm) hij
    · exact h3
  have hdiag : (X : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal (fun i => (X : Matrix (Fin 3) (Fin 3) L) i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hpow : Matrix.diagonal (fun i => ((X : Matrix (Fin 3) (Fin 3) L) i i) ^ 2 ^ n) =
      (1 : Matrix (Fin 3) (Fin 3) L) := by
    have h := congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) hXn
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
    rw [hdiag, Matrix.diagonal_pow] at h
    exact h
  have hone : ∀ i, (X : Matrix (Fin 3) (Fin 3) L) i i = 1 := by
    intro i
    have h := congrFun (congrFun hpow i) i
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h
    exact eq_one_of_pow_two_pow h
  apply Subtype.ext
  rw [hdiag, Matrix.SpecialLinearGroup.coe_one]
  have : (fun i => (X : Matrix (Fin 3) (Fin 3) L) i i) = fun _ => 1 := funext hone
  rw [this]
  exact Matrix.diagonal_one

end Mat

private theorem exists_su3_elements [IsAlgClosed L] :
    ∃ T A h P D : SL(3, L),
      ((T : Matrix (Fin 3) (Fin 3) L).map (· ^ 2))ᵀ * (T : Matrix (Fin 3) (Fin 3) L) = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) L).map (· ^ 2))ᵀ * (A : Matrix (Fin 3) (Fin 3) L) = 1 ∧
      ((h : Matrix (Fin 3) (Fin 3) L).map (· ^ 2))ᵀ * (h : Matrix (Fin 3) (Fin 3) L) = 1 ∧
      T * T = 1 ∧ A * A = 1 ∧ h * h = P ∧ P * P = 1 ∧ P ∉ Subgroup.center SL(3, L) ∧
      ⁅T, A⁆ = D ∧ ∀ X : SL(3, L), X * D = D * X → ∀ n : ℕ, X ^ 2 ^ n = 1 → X = 1 := by
  obtain ⟨ω, hω⟩ := exists_omega (L := L)
  let T : SL(3, L) := ⟨!![0, ω ^ 2, 0; ω, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]; grind⟩
  let A : SL(3, L) := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]; grind⟩
  let h : SL(3, L) := ⟨!![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω], by
    simp [Matrix.det_fin_three]; grind⟩
  let P : SL(3, L) := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [Matrix.det_fin_three]; grind⟩
  let D : SL(3, L) := ⟨!![ω, 0, 0; 0, ω ^ 2, 0; 0, 0, 1], by
    simp [Matrix.det_fin_three]; grind⟩
  have hTT : T * T = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact mat_TT ω hω)
  have hAA : A * A = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_three])
  have hhh : h * h = P := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact mat_hh ω hω)
  have hPP : P * P = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_three])
  refine ⟨T, A, h, P, D, mat_TT_unitary ω hω, ?_, mat_hh_unitary ω hω, hTT, hAA, hhh, hPP,
    ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  · intro hc
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
    have h12 := congrFun (congrFun hr 1) 2
    have e1 : (Matrix.scalar (Fin 3) r : Matrix (Fin 3) (Fin 3) L) 1 2 = 0 := by
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    have e2 : (P : Matrix (Fin 3) (Fin 3) L) 1 2 = 1 := by simp [P]
    rw [e1, e2] at h12
    exact zero_ne_one h12
  · have hTi : T⁻¹ = T := inv_eq_of_mul_eq_one_right hTT
    have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_right hAA
    rw [commutatorElement_def, hTi, hAi]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    exact mat_comm ω hω
  · intro X hX n hXn
    refine mat_diag_eq_one ω hω X ?_ hXn
    have := congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) hX
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this

end Matrices

section GroupTheory

private theorem commutator_pow_of_central {G : Type*} [Group G] {x d : G}
    (hc : ⁅x, d⁆ ∈ Subgroup.center G) (k : ℕ) : ⁅x ^ k, d⁆ = ⁅x, d⁆ ^ k := by
  set c : G := ⁅x, d⁆ with hcdef
  have hxd : x * d * x⁻¹ = c * d := by
    rw [hcdef, commutatorElement_def]
    group
  have hconj : ∀ k : ℕ, x ^ k * d * (x ^ k)⁻¹ = c ^ k * d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hck : x * c ^ k = c ^ k * x :=
        Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hc k) x
      calc x ^ (k + 1) * d * (x ^ (k + 1))⁻¹ = x * (x ^ k * d * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * (c ^ k * d) * x⁻¹ := by rw [ih]
        _ = (x * c ^ k) * (d * x⁻¹) := by group
        _ = c ^ k * (x * d * x⁻¹) := by rw [hck]; group
        _ = c ^ (k + 1) * d := by rw [hxd]; group
  rw [commutatorElement_def, hconj k]
  group

end GroupTheory

private theorem stdUnitary_eq_self_of_unitary {L : Type} [Field L] {ν : ℕ} (σ : L →+* L)
    (X : SL(ν, L))
    (h : ((X : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * (X : Matrix (Fin ν) (Fin ν) L) = 1) :
    stdUnitary σ X = X := by
  apply Subtype.ext
  rw [coe_stdUnitary]
  have h2 : (X : Matrix (Fin ν) (Fin ν) L)ᵀ * (X : Matrix (Fin ν) (Fin ν) L).map σ = 1 := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  rw [Matrix.inv_eq_left_inv h2, Matrix.transpose_transpose]


private theorem su3_data {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    (hq2 : S.D.q = 2) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {ψ : SL(3, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K)}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    ∃ (θ : SL(3, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K))
      (C : Subgroup SL(3, AlgebraicClosure K)),
      Nat.card C = 216 ∧
      (∀ X : SL(3, AlgebraicClosure K),
        ((X : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)).map (· ^ 2))ᵀ *
          (X : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) = 1 → X ∈ C) ∧
      (∀ X ∈ C, θ X ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ∧
        S.D.step (θ X) = θ X) ∧
      (∀ X : SL(3, AlgebraicClosure K), θ X = 1 →
        X ∈ Subgroup.center SL(3, AlgebraicClosure K)) ∧
      ∀ (y : ModGL τ (AlgebraicClosure K)) (n : ℕ),
        y ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) →
        S.D.step y = y → y ^ 2 ^ n = 1 → ∃ X ∈ C, θ X = y ∧ X ^ 2 ^ n = 1 := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hν : 3 ≤ 3 := le_rfl
  obtain ⟨r, e, σQ, z, hr, hchar, he, hq, hσc, hconj, hnormz⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141g.exists_unitary_untwist S hT i hν hψ hΨ
      π hπ
  have hr2 : r = 2 := CharP.eq (AlgebraicClosure K) hchar hL2
  subst hr2
  haveI : Fact (Nat.Prime 2) := ⟨hr⟩
  have he1 : e = 1 := by
    have h2 : (2 : ℕ) ^ e = 2 ^ 1 := by rw [← hq, hq2]; norm_num
    exact Nat.pow_right_injective le_rfl h2
  rw [hs1] at hσc hconj
  have hσ2 : ∀ c, σQ c = c ^ 2 ^ 1 := fun c => by rw [hσc c, he1]
  have hψS : ∀ X, ψ X ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
    fun X => by
      rw [hΨ, ← hψ.range]
      exact ⟨X, rfl⟩
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ) with hCdef
  have hCmem : ∀ X : SL(3, AlgebraicClosure K), X ∈ C ↔ stdUnitary σQ.toRingHom X = X :=
    fun X => by
      rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  obtain ⟨-, -, hcard⟩ := stdUnitary_fixSubgroup (ν := 3) (ℓ := 2) (f := 1) hr le_rfl σQ hσ2 hν
  have hCcard : Nat.card C = 216 := hcard (by norm_num)
  set θ : SL(3, AlgebraicClosure K) →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj z).toMonoidHom.comp ψ with hθdef
  have hθ : ∀ X, θ X = z * ψ X * z⁻¹ := fun X => rfl
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin 3) ≠ ⟨1, by omega⟩ := by simp
    obtain ⟨ε, hε⟩ := hψ.transv ⟨0, by omega⟩ ⟨1, by omega⟩ h01
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : AlgebraicClosure K) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ (AlgebraicClosure K) (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ (AlgebraicClosure K) _ h1)
  have hkerc : ∀ X : SL(3, AlgebraicClosure K), ψ X = 1 → X ∈ Subgroup.center SL(3, _) :=
    fun X hX => mem_center_SL_of_commute hν ψ hker fun Y => by rw [hX, one_mul, mul_one]
  refine ⟨θ, C, hCcard, fun X hX => ?_, fun X hX => ⟨?_, ?_⟩, fun X hX => ?_, ?_⟩
  · refine (hCmem X).2 (stdUnitary_eq_self_of_unitary _ X ?_)
    have : (X : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)).map σQ.toRingHom =
        (X : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)).map (· ^ 2) := by
      ext j k
      simp [hσ2]
    rw [this]
    exact hX
  · rw [hθ]
    exact (hnormz i _).1 (hψS X)
  · show S.D.step (θ X) = θ X
    have h1 := hconj X
    rw [(hCmem X).1 hX] at h1
    rw [hθ]
    exact h1
  · refine hkerc X ?_
    have h1 : z * ψ X * z⁻¹ = 1 := by rw [← hθ]; exact hX
    have h2 : ψ X = z⁻¹ * (z * ψ X * z⁻¹) * z := by group
    rw [h2, h1]
    group
  · intro y n hy hyF hn
    have hy' : z⁻¹ * y * z ∈ rootSpan τ (AlgebraicClosure K)
        (componentRoots (rootCharHom a) i) := (hnormz i _).2 (by
      have e : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
      rw [e]
      exact hy)
    rw [hΨ, ← hψ.range] at hy'
    obtain ⟨X, hX⟩ := hy'
    have hyX : y = θ X := by rw [hθ, hX]; group
    have hcX : X ^ 2 ^ n ∈ Subgroup.center SL(3, AlgebraicClosure K) := by
      refine hkerc _ ?_
      have h1 : θ (X ^ 2 ^ n) = 1 := by rw [map_pow, ← hyX, hn]
      rw [hθ] at h1
      have h2 : ψ (X ^ 2 ^ n) = z⁻¹ * (z * ψ (X ^ 2 ^ n) * z⁻¹) * z := by group
      rw [h2, h1]
      group
    obtain ⟨N, hN, hcN⟩ := exists_coprime_pow_of_mem_center_SL Nat.prime_two hK2 (by omega) hcX
    have hcopy : Nat.Coprime N (orderOf y) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn) (Nat.Coprime.pow_right n hN)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcopy
    set X₁ := (X ^ N) ^ m with hX₁
    have hyX₁ : y = θ X₁ := by
      rw [hX₁, map_pow, map_pow, ← hyX, hm]
    have hX₁n : X₁ ^ 2 ^ n = 1 := by
      rw [hX₁, ← pow_mul, ← pow_mul, show N * (m * 2 ^ n) = 2 ^ n * N * m by ring, pow_mul,
        pow_mul, hcN, one_pow]
    set c₁ := stdUnitary σQ.toRingHom X₁ * X₁⁻¹ with hc₁
    have hc₁c : c₁ ∈ Subgroup.center SL(3, AlgebraicClosure K) := by
      refine hkerc _ ?_
      have h1 : iterHom S.D.step 1 (θ X₁) = θ X₁ := by rw [← hyX₁]; exact hyF
      rw [hθ, hconj] at h1
      have h2 : ψ (stdUnitary σQ.toRingHom X₁) = ψ X₁ := by
        have := congrArg (fun g => z⁻¹ * g * z) h1
        simpa [mul_assoc] using this
      rw [hc₁, map_mul, map_inv, h2, mul_inv_cancel]
    have hc₁n : c₁ ^ 2 ^ n = 1 := by
      have hcomm : Commute c₁ X₁ := (Subgroup.mem_center_iff.1 hc₁c X₁).symm
      have e1 : stdUnitary σQ.toRingHom X₁ = c₁ * X₁ := by rw [hc₁, inv_mul_cancel_right]
      have h1 : (stdUnitary σQ.toRingHom X₁) ^ 2 ^ n = 1 := by rw [← map_pow, hX₁n, map_one]
      rw [e1, hcomm.mul_pow, hX₁n, mul_one] at h1
      exact h1
    have hc₁1 : c₁ = 1 := eq_one_of_mem_center_SL_charPow (by omega) hc₁c hc₁n
    have hX₁C : X₁ ∈ C := by
      rw [hCmem]
      exact mul_inv_eq_one.1 hc₁1
    exact ⟨X₁, hX₁C, hyX₁.symm, hX₁n⟩

private theorem smallSU3_core {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2)
    {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hq2 : S.D.q = 2)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hT : rootDiagUnit τ a ∈ S.D.torus) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hap : ∀ i, a i ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2)
    (hk : twistKind S.ρ (rootCharHom a) i = .suN)
    (hn6 : (componentRoots (rootCharHom a) i).ncard = 6) :
    (∀ z ∈ twoClosure S i, (∀ x ∈ ⁅twoClosure S i, twoClosure S i⁆, Commute z x) →
      (∃ n : ℕ, z ^ 2 ^ n = 1) → z = 1) ∧
      Nat.card (twoClosure S i) ∣ 216 ∧
      (p = 7 → 8 ∣ Nat.card (twoClosure S i) → ∃ x ∈ twoClosure S i, orderOf x = 4) := by
  classical
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ν, ψ, σ, hν, hψ, hΨ, π, hπ⟩ := exists_unitary_frame hK2 S hp hp2 hT hap i hk
  have hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1 := fun x y hxy => by
    rw [CFSG.SeitzReduction.EPilot.iform_self_eq_two hτ (hψ.isRoot x y hxy)]
    norm_num
  have hcard := CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ one_ne_zero hnorm
  rw [← hΨ, hn6] at hcard
  have hν3 : ν = 3 := by
    have hle : ν ≤ 3 := by
      by_contra h
      push Not at h
      have : 4 * 3 ≤ ν * (ν - 1) := Nat.mul_le_mul h (by omega)
      omega
    omega
  subst hν3
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
    rw [hq2] at hQ
    exact Nat.pow_right_injective le_rfl (hQ.trans (pow_one 2).symm)
  obtain ⟨θ, C, hCcard, hCmem, hC1, hC3, hC2⟩ := su3_data hK2 S hq2 hT i hψ hΨ π hπ hs1
  have hρΨ : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    have := (outer_componentOrbitLength_spec S hT i).2.1
    rwa [hs1, Function.iterate_one] at this
  have hρmem : ∀ k : ℕ, ∀ δ ∈ componentRoots (rootCharHom a) i,
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ ∈ componentRoots (rootCharHom a) i := by
    intro k
    induction k with
    | zero => exact fun δ hδ => hδ
    | succ k ih =>
      intro δ hδ
      rw [Function.iterate_succ_apply']
      rw [← hρΨ]
      exact Set.mem_image_of_mem _ (ih δ hδ)
  have hRR : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      exact hρmem k δ hδ
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  have hspAdj : rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ≤
      adjointGroup τ (AlgebraicClosure K) := by
    rw [hΨ, ← hψ.range]
    exact hψ.range_le_adjointGroup
  have hVgen : ∀ g, g ∈ orbitGroup S i ↔
      g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ∧
        g ∈ S.D.model := fun g => by
    unfold orbitGroup
    rw [hRR]
    exact Subgroup.mem_inf
  have hVle : twoClosure S i ≤ C.map θ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hg, n, hgn⟩
    obtain ⟨hg1, hg2⟩ := (hVgen g).1 hg
    obtain ⟨X, hXC, hXg, -⟩ := hC2 g n hg1 hg2.2 hgn
    exact ⟨X, hXC, hXg⟩
  have hgen : ∀ X ∈ C, ∀ n : ℕ, X ^ 2 ^ n = 1 → θ X ∈ twoClosure S i := by
    intro X hX n hXn
    refine Subgroup.subset_closure ⟨(hVgen _).2 ⟨(hC1 X hX).1, ?_⟩, n, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨hspAdj (hC1 X hX).1, (hC1 X hX).2⟩
    · rw [← map_pow, hXn, map_one]
  have hb2 : Nat.card (twoClosure S i) ∣ 216 := by
    have h1 : Nat.card (twoClosure S i) ∣ Nat.card (C.map θ) := Subgroup.card_dvd_of_le hVle
    have h2 : Nat.card (C.map θ) ∣ Nat.card C := Subgroup.card_map_dvd C θ
    rw [← hCcard]
    exact h1.trans h2
  obtain ⟨T, A, h, P, D, hTu, hAu, hhu, hTT, hAA, hhh, hPP, hPc, hTA, hdiag⟩ :=
    exists_su3_elements (L := AlgebraicClosure K)
  have hTC : T ∈ C := hCmem T hTu
  have hAC : A ∈ C := hCmem A hAu
  have hhC : h ∈ C := hCmem h hhu
  have hTV : θ T ∈ twoClosure S i := hgen T hTC 1 (by rw [pow_one, pow_two]; exact hTT)
  have hAV : θ A ∈ twoClosure S i := hgen A hAC 1 (by rw [pow_one, pow_two]; exact hAA)
  have hhV : θ h ∈ twoClosure S i :=
    hgen h hhC 2 (by
      rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, pow_two h, hhh, pow_two, hPP])
  have hord : orderOf (θ h) = 4 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsq : θ h ^ 2 = θ P := by rw [← map_pow, pow_two, hhh]
    have hne : θ h ^ 2 ^ 1 ≠ 1 := by
      rw [pow_one, hsq]
      intro h1
      exact hPc (hC3 P h1)
    have h4 : θ h ^ 2 ^ (1 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hsq, pow_two, ← map_mul, hPP,
        map_one]
    have := orderOf_eq_prime_pow hne h4
    simpa using this
  refine ⟨?_, hb2, fun _ _ => ⟨θ h, hhV, hord⟩⟩
  intro z hz hzc ⟨n, hn⟩
  obtain ⟨X₀, hX₀C, hX₀⟩ := hVle hz
  have hz1 := hC1 X₀ hX₀C
  rw [hX₀] at hz1
  obtain ⟨X, hXC, hXz, hXn⟩ := hC2 z n hz1.1 hz1.2 hn
  have hDmem : θ ⁅T, A⁆ ∈ ⁅twoClosure S i, twoClosure S i⁆ := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hTV hAV
  have hcen : ⁅X, ⁅T, A⁆⁆ ∈ Subgroup.center SL(3, AlgebraicClosure K) := by
    refine hC3 _ ?_
    rw [map_commutatorElement, hXz, commutatorElement_eq_one_iff_mul_comm]
    exact (hzc _ hDmem).eq
  have hcn : ⁅X, ⁅T, A⁆⁆ ^ 2 ^ n = 1 := by
    rw [← commutator_pow_of_central hcen, hXn]
    simp
  have hc1 : ⁅X, ⁅T, A⁆⁆ = 1 :=
    eq_one_of_mem_center_SL_charPow (ℓ := 2) (by omega) hcen hcn
  rw [commutatorElement_eq_one_iff_mul_comm, hTA] at hc1
  have hX1 : X = 1 := hdiag X hc1 n hXn
  rw [← hXz, hX1, map_one]

theorem smallFactsSU3 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : SmallFactsSU3 p :=
  fun _ _ _ _ hK2 _ S _ hq2 hτ hT hap i ⟨hQ, hk, hn6⟩ =>
    smallSU3_core hK2 S hq2 hτ hT hp hp2 hap i hQ hk hn6

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
