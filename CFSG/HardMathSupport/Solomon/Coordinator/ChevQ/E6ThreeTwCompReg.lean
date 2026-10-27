module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompInner
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompRegular
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLineSum
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwE6FrameLayer
public import CFSG.RankThree.PartOne.KE6.Phi6Excl

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (diagGL3 conjDiag3 toGL_conjDiag3 conjDiag3_transvection)

open CFSG.RankThree.PartOne.TCX.E (e6rhoA2₁ e6rhoA2₁_transvection)

open CFSG.RankThree.E6 (chainRoot chain13)

open CFSG.RankThree.PartTwo.Sec4 (exists_eigenbasis colMat mul_colMat_eq isUnit_colMat
  linearIndependent_cyclic one_add_tau_add_sq)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open Matrix.SpecialLinearGroup (toGL)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Matrices

variable {K : Type} [Field K]

theorem twThree_ne_zero {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : (3 : K) ≠ 0 := by
  intro h3
  have hs := one_add_tau_add_sq hω3 hω1
  have h2 : (ω - 1) ^ 2 = 0 := by linear_combination hs - ω * h3
  exact hω1 (sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2))

theorem twExists_cube_root_unity {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) (hℓ3 : ℓ ≠ 3) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp' : ℓ % 3 = 1 ∨ ℓ % 3 = 2 := by
    have h3 : ¬ 3 ∣ ℓ := fun h3 =>
      hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).mp h3).symm
    omega
  have hp2 : ℓ ^ 2 % 3 = 1 := by
    rcases hp' with h1 | h1 <;> (rw [Nat.pow_mod, h1]; try decide)
  have hmod : ℓ ^ (2 * f) % 3 = 1 := by
    rw [pow_mul, Nat.pow_mod, hp2, one_pow]
    try decide
  have hcard : 3 ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hcard
  refine ⟨u, ?_, fun h1 => ?_⟩
  · have h3 := pow_orderOf_eq_one u
    rw [hu] at h3
    have h4 := congrArg Units.val h3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h4
  · have hu1 : u = 1 := Units.val_eq_one.mp h1
    rw [hu1, orderOf_one] at hu
    omega

theorem twDiagGL3_mul (a b : Fin 3 → Kˣ) : diagGL3 a * diagGL3 b = diagGL3 (a * b) := by
  apply Units.ext
  change Matrix.diagonal (fun i => (a i : K)) * Matrix.diagonal (fun i => (b i : K)) =
    Matrix.diagonal (fun i => ((a * b) i : K))
  rw [Matrix.diagonal_mul_diagonal]
  rfl

theorem twDiagGL3_inv (a : Fin 3 → Kˣ) : diagGL3 a⁻¹ = (diagGL3 a)⁻¹ :=
  Units.ext rfl

theorem twDiagGL3_const_comm (u : Kˣ) (Z : GL (Fin 3) K) :
    diagGL3 (fun _ => u) * Z = Z * diagGL3 (fun _ => u) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change Matrix.diagonal (fun _ => (u : K)) * _ = _ * Matrix.diagonal (fun _ => (u : K))
  rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

theorem twExists_mul_eq_diagGL3 {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {M : GL (Fin 3) K}
    {μ : K} (hM : (M : Matrix (Fin 3) (Fin 3) K) ^ 3 = (μ ^ 3) • 1) :
    ∃ (G : GL (Fin 3) K) (c : Fin 3 → Kˣ), M * G = G * diagGL3 c := by
  have h3 := twThree_ne_zero hω3 hω1
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact ne_zero_of_pow_three_eq_smul hM (zero_pow (by norm_num))
  set y : Matrix (Fin 3) (Fin 3) K := μ⁻¹ • (M : Matrix (Fin 3) (Fin 3) K) with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, smul_pow, hM, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hμ0), one_smul]
  have hM' : (M : Matrix (Fin 3) (Fin 3) K) = μ • y := by
    rw [hy, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  obtain ⟨b, hb, hk⟩ := exists_eigenbasis hω3 hω1 h3 hy3
  choose k hk using hk
  refine ⟨(isUnit_colMat hb).unit, fun r => Units.mk0 (μ * ω ^ (k r : ℕ))
    (mul_ne_zero hμ0 (pow_ne_zero _ hω0)), Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec]
  refine mul_colMat_eq fun r => ?_
  rw [hM', Matrix.smul_mulVec, hk r, smul_smul, Units.val_mk0]

theorem twExists_eigen_eq_of_not_hasCyclicVec3 {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {A : GL (Fin 3) K} {α : K} (hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1)
    (hA : ¬ HasCyclicVec3 (A : Matrix (Fin 3) (Fin 3) K)) :
    ∃ (g : GL (Fin 3) K) (c : Fin 3 → Kˣ) (j k : Fin 3), j ≠ k ∧ c j = c k ∧
      A * g = g * diagGL3 c := by
  by_cases hcube : ∃ μ : K, μ ^ 3 = α
  swap
  · refine absurd (hasCyclicVec3_iff.2 ⟨Pi.single (0 : Fin 3) (1 : K),
      linearIndependent_cyclic (fun μ h => hcube ⟨μ, h⟩) hA3 ?_⟩) hA
    intro h0
    have := congrFun h0 0
    simp at this
  obtain ⟨μ, rfl⟩ := hcube
  obtain ⟨g, c, hgc⟩ := twExists_mul_eq_diagGL3 hω3 hω1 hA3
  obtain ⟨j, k, hjk, hc⟩ : ∃ j k : Fin 3, j ≠ k ∧ c j = c k := by
    by_contra hne
    push Not at hne
    have hne' : ∀ j k : Fin 3, j ≠ k → (c j : K) ≠ c k := fun j k hjk h =>
      hne j k hjk (Units.ext h)
    have hMg : (A : Matrix (Fin 3) (Fin 3) K) * g = g * Matrix.diagonal fun r => (c r : K) := by
      have h := congrArg Units.val hgc
      rw [Units.val_mul, Units.val_mul] at h
      exact h
    exact hA (hasCyclicVec3_iff.2 ⟨_, linearIndependent_cyclic_of_mul_eq g.isUnit hMg
      (linearIndependent_cyclic_diagonal (d := fun r => (c r : K)) (hne' 0 1 (by decide))
        (hne' 0 2 (by decide)) (hne' 1 2 (by decide)))⟩)
  exact ⟨g, c, j, k, hjk, hc, hgc⟩

theorem twExists_SL_conj_diagGL3 {Ω : Type} [Field Ω] [IsAlgClosed Ω] {M G : GL (Fin 3) Ω}
    {c : Fin 3 → Ωˣ} (h : M * G = G * diagGL3 c) :
    ∃ P : SL(3, Ω), toGL P * M * (toGL P)⁻¹ = diagGL3 c := by
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq ((Matrix.GeneralLinearGroup.det G : Ωˣ) : Ω)
    (by norm_num : 0 < 3)
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact (Matrix.GeneralLinearGroup.det G).ne_zero hl.symm
  have hsc : ∀ Z, diagGL3 (fun _ => Units.mk0 l hl0) * Z = Z * diagGL3 (fun _ => Units.mk0 l hl0) :=
    fun Z => twDiagGL3_const_comm _ Z
  have hdet : ((diagGL3 (fun _ => Units.mk0 l hl0) * G⁻¹ : GL (Fin 3) Ω) :
      Matrix (Fin 3) (Fin 3) Ω).det = 1 := by
    have h1 : ((diagGL3 (fun _ => Units.mk0 l hl0) : GL (Fin 3) Ω) :
        Matrix (Fin 3) (Fin 3) Ω).det = l ^ 3 := by
      change (Matrix.diagonal fun _ => ((Units.mk0 l hl0 : Ωˣ) : Ω)).det = l ^ 3
      rw [Matrix.det_diagonal, Fin.prod_const, Units.val_mk0]
    have h2 : ((G⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω).det *
        (G : Matrix (Fin 3) (Fin 3) Ω).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [Units.val_mul, Matrix.det_mul, h1, hl, Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
    exact h2
  refine ⟨⟨_, hdet⟩, ?_⟩
  have hP : toGL ⟨_, hdet⟩ = diagGL3 (fun _ => Units.mk0 l hl0) * G⁻¹ := Units.ext rfl
  have hD : G⁻¹ * M * G = diagGL3 c := by
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hP]
  calc diagGL3 (fun _ => Units.mk0 l hl0) * G⁻¹ * M * (diagGL3 (fun _ => Units.mk0 l hl0) * G⁻¹)⁻¹
      = diagGL3 (fun _ => Units.mk0 l hl0) * (G⁻¹ * M * G) *
          (diagGL3 (fun _ => Units.mk0 l hl0))⁻¹ := by group
    _ = diagGL3 c := by rw [hD, hsc, mul_inv_cancel_right]

variable {Ω : Type} [Field Ω] [Algebra K Ω]

theorem twGl3Emb_diagGL3 (c : Fin 3 → Kˣ) :
    gl3Emb K Ω (diagGL3 c) = diagGL3 (fun r => Units.map (algebraMap K Ω).toMonoidHom (c r)) := by
  apply Units.ext
  rw [coe_gl3Emb]
  change (Matrix.diagonal fun r => (c r : K)).map (algebraMap K Ω) =
    Matrix.diagonal fun r => ((Units.map (algebraMap K Ω).toMonoidHom (c r) : Ωˣ) : Ω)
  rw [Matrix.diagonal_map (map_zero _)]
  rfl

theorem twGl3Emb_pow_three {γ : GL (Fin 3) K} {α : K}
    (h : (γ : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) :
    ((gl3Emb K Ω γ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = (algebraMap K Ω α) • 1 := by
  rw [coe_gl3Emb, ← RingHom.mapMatrix_apply, ← map_pow, h, RingHom.mapMatrix_apply]
  ext r s
  by_cases hrs : r = s <;> simp [hrs]

theorem TwDiagRealizes.diagGL3_mul {Hc : SL(3, Ω)} {d : Fin 3 → Ωˣ} {B : GL (Fin 3) K}
    (hB : TwDiagRealizes Hc d B) (w : GL (Fin 3) K) :
    ∃ u : Ωˣ, diagGL3 d * (toGL Hc * gl3Emb K Ω w * (toGL Hc)⁻¹) =
      diagGL3 (fun _ => u) * (toGL Hc * gl3Emb K Ω (B * w) * (toGL Hc)⁻¹) := by
  obtain ⟨c, hc, hN⟩ := hB
  refine ⟨Units.mk0 c hc, ?_⟩
  have hfd : twFrameDiag Hc d = diagGL3 (fun _ => Units.mk0 c hc) * gl3Emb K Ω B := by
    apply Units.ext
    rw [hN, Units.val_mul, coe_gl3Emb, Matrix.smul_eq_diagonal_mul]
    rfl
  have hdiag : diagGL3 d = toGL Hc * twFrameDiag Hc d * (toGL Hc)⁻¹ := by
    unfold twFrameDiag
    group
  have hs := twDiagGL3_const_comm (Units.mk0 c hc) (toGL Hc)
  rw [hdiag, hfd, map_mul]
  calc toGL Hc * (diagGL3 (fun _ => Units.mk0 c hc) * gl3Emb K Ω B) * (toGL Hc)⁻¹ *
        (toGL Hc * gl3Emb K Ω w * (toGL Hc)⁻¹)
      = toGL Hc * diagGL3 (fun _ => Units.mk0 c hc) * (gl3Emb K Ω B * gl3Emb K Ω w) *
          (toGL Hc)⁻¹ := by group
    _ = diagGL3 (fun _ => Units.mk0 c hc) * toGL Hc * (gl3Emb K Ω B * gl3Emb K Ω w) *
          (toGL Hc)⁻¹ := by rw [hs]
    _ = _ := by group

theorem twScalar_conj_mul_eq {N G₀ : GL (Fin 3) Ω} {c : Fin 3 → Ωˣ}
    (h : N * G₀ = G₀ * diagGL3 c) (u : Ωˣ) (H : GL (Fin 3) Ω) :
    diagGL3 (fun _ => u) * (H * N * H⁻¹) * (H * G₀) = H * G₀ * diagGL3 (fun r => u * c r) := by
  have e : diagGL3 (fun r => u * c r) = diagGL3 (fun _ => u) * diagGL3 c := by
    rw [twDiagGL3_mul]
    rfl
  have hs := twDiagGL3_const_comm u (H * G₀)
  calc diagGL3 (fun _ => u) * (H * N * H⁻¹) * (H * G₀)
      = diagGL3 (fun _ => u) * (H * (N * G₀)) := by group
    _ = diagGL3 (fun _ => u) * (H * G₀) * diagGL3 c := by rw [h]; group
    _ = H * G₀ * diagGL3 (fun r => u * c r) := by rw [hs, e]; group

end Matrices

section Psi


theorem twFinrank_psi {K : Type} [Field K] (g₀ : ModGL Tag.E6 (AlgebraicClosure K))
    (g : ModGL TwistTag.E6.tag K) :
    Module.finrank (AlgebraicClosure K) (LinearMap.ker
      (((twLinePsi K g₀ g : ModGL Tag.E6 (AlgebraicClosure K)) :
        Module.End (AlgebraicClosure K) (RootModule Tag.E6 (AlgebraicClosure K))) - 1)) =
      Module.finrank K (LinearMap.ker ((g : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) := by
  have e : twLinePsi K g₀ g =
      g₀⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) g * g₀⁻¹⁻¹ := by
    rw [twLinePsi_apply, inv_inv]
  have h := finrank_ker_baseChangeEnd (L := AlgebraicClosure K)
    ((g : Module.End K (RootModule TwistTag.E6.tag K)) - 1)
  rw [baseChangeEnd_sub_aux, baseChangeEnd_one_aux, ← coe_baseChangeGL] at h
  rw [e, finrank_ker_conj_sub_one]
  exact h

end Psi

section Count


variable {Ω : Type} [Field Ω]

theorem twRootChar_eq_one_of_conj {β : Fin Tag.E6.rank → Ωˣ} {j k : Fin 3} (hjk : j ≠ k)
    (h : rootDiagUnit Tag.E6 β * e6rhoA2₁ Ω (Matrix.SpecialLinearGroup.transvection hjk 1) *
        (rootDiagUnit Tag.E6 β)⁻¹ = e6rhoA2₁ Ω (Matrix.SpecialLinearGroup.transvection hjk 1)) :
    rootChar β (chainRoot chain13 j k) = 1 := by
  obtain ⟨ε, hε⟩ := e6rhoA2₁_transvection (L := Ω) hjk
  have hr : IsRoot Tag.E6 (chainRoot chain13 j k) := (e6Std_frame Ω).isRoot j k hjk
  rw [hε 1, rootDiagUnit_conj_pinnedX β hr] at h
  have h1 := pinnedX_injective (τ := Tag.E6) (R := Ω) _ h
  apply Units.ext
  rw [Units.val_one]
  have hε0 : (ε : Ω) * 1 ≠ 0 := by
    rw [mul_one]
    exact ε.ne_zero
  exact mul_right_cancel₀ hε0 (by rw [h1, one_mul])

theorem twSeven_le_finrank_supported {S : Set (Label Tag.E6)} {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hγS : (Sum.inr ⟨γ, hγ⟩ : Label Tag.E6) ∈ S)
    (hS : ∀ j, (Sum.inl j : Label Tag.E6) ∈ S) :
    7 ≤ Module.finrank Ω ↥(Finsupp.supported Ω Ω S) := by
  classical
  haveI : Fintype S := Fintype.ofFinite _
  rw [(Finsupp.supportedEquivFinsupp (M := Ω) (R := Ω) S).finrank_eq,
    Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  have h7 := Nat.card_le_card_of_injective
    (fun o : Option (Fin Tag.E6.rank) => (o.elim ⟨_, hγS⟩ fun j => ⟨_, hS j⟩ : S)) (by
      rintro (_ | j) (_ | j') h
      · rfl
      · exact absurd (congrArg Subtype.val h) Sum.inr_ne_inl
      · exact absurd (congrArg Subtype.val h) Sum.inl_ne_inr
      · exact congrArg some (Sum.inl_injective (congrArg Subtype.val h)))
  rw [Finite.card_option, Nat.card_fin] at h7
  have h6 : Tag.E6.rank = 6 := rfl
  omega

theorem twSeven_le_finrank_inf {α β : Fin Tag.E6.rank → Ωˣ} {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hα : rootChar α γ = 1) (hβ : rootChar β γ = 1) :
    7 ≤ Module.finrank Ω ↥(LinearMap.ker ((rootDiag α : Module.End Ω (RootModule Tag.E6 Ω)) - 1) ⊓
      LinearMap.ker ((rootDiag β : Module.End Ω (RootModule Tag.E6 Ω)) - 1)) := by
  rw [ker_rootDiag_sub_one, ker_rootDiag_sub_one, ← Finsupp.supported_inter]
  exact twSeven_le_finrank_supported hγ ⟨hα, hβ⟩ fun _ => ⟨rootChar_zero α, rootChar_zero β⟩

theorem twLineSum_false (h3 : (3 : Ω) ≠ 0) {α β : Fin Tag.E6.rank → Ωˣ}
    (hα3 : rootDiagUnit Tag.E6 α ^ 3 = 1) (hβ3 : rootDiagUnit Tag.E6 β ^ 3 = 1)
    (h0 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 α : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24)
    (h1 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 β : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24)
    (h2 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 α * rootDiagUnit Tag.E6 β :
      ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24)
    (h4 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 α ^ 2 * rootDiagUnit Tag.E6 β :
      ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (hαγ : rootChar α γ = 1)
    (hβγ : rootChar β γ = 1) : False := by
  have hc : Commute ((rootDiagUnit Tag.E6 α : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) (rootDiagUnit Tag.E6 β : ModGL Tag.E6 Ω) := by
    change rootDiag α * rootDiag β = rootDiag β * rootDiag α
    rw [rootDiag_mul_rootDiag, rootDiag_mul_rootDiag, mul_comm]
  have ha : ((rootDiagUnit Tag.E6 α : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hα3, Units.val_one]
  have hb : ((rootDiagUnit Tag.E6 β : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hβ3, Units.val_one]
  have hsum := finrank_lineSum h3 ha hb hc
  rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, h0, h1, h2, h4] at hsum
  have h78 : Module.finrank Ω (RootModule Tag.E6 Ω) = 78 := by
    rw [Module.finrank_finsupp_self, Fintype.card_sum, Fintype.card_fin, card_isRoot]
    rfl
  have h7 : 7 ≤ Module.finrank Ω ↥(LinearMap.ker (((rootDiagUnit Tag.E6 α : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) - 1) ⊓ LinearMap.ker (((rootDiagUnit Tag.E6 β :
        ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) - 1)) :=
    twSeven_le_finrank_inf hγ hαγ hβγ
  omega

theorem twFrameN_conj_fix (i : Fin 3) {g : ModGL Tag.E6 Ω} {W : SL(3, Ω)}
    (h : g * twFrame Ω i W * g⁻¹ = twFrame Ω i W) :
    twFrameN Ω i * g * (twFrameN Ω i)⁻¹ * e6rhoA2₁ Ω W * (twFrameN Ω i * g * (twFrameN Ω i)⁻¹)⁻¹ =
      e6rhoA2₁ Ω W := by
  rw [twFrame_apply] at h
  calc twFrameN Ω i * g * (twFrameN Ω i)⁻¹ * e6rhoA2₁ Ω W *
        (twFrameN Ω i * g * (twFrameN Ω i)⁻¹)⁻¹
      = twFrameN Ω i * (g * ((twFrameN Ω i)⁻¹ * e6rhoA2₁ Ω W * twFrameN Ω i) * g⁻¹) *
          (twFrameN Ω i)⁻¹ := by group
    _ = e6rhoA2₁ Ω W := by rw [h]; group

end Count

section Main


variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
  {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)}

local notation "Ω" => AlgebraicClosure K

theorem TwCompFrames.hasCyclicVec3 (hl : TwE6ThreeA2Line K σ h₀ L T n)
    (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A) {τ : ModGL TwistTag.E6.tag K}
    (hτ : τ ∈ twTorusHat K σ g₀) (x : Fin 3 → unitarySU ℓ f K 3)
    (h3 : (τ * twLayerProd ρ x) ^ 3 = 1)
    (hd0 : Module.finrank K (LinearMap.ker (((τ * twLayerProd ρ x : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24)
    (hd1 : Module.finrank K (LinearMap.ker (((h₀ * (τ * twLayerProd ρ x) :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24)
    (hd2 : Module.finrank K (LinearMap.ker (((h₀ ^ 2 * (τ * twLayerProd ρ x) :
      ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24)
    (i : Fin 3) :
    HasCyclicVec3 ((((A i τ : GL (Fin 3) K) * (x i : GL (Fin 3) K) : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) := by
  classical
  by_contra hcyc
  obtain ⟨ωK, hωK3, hωK1⟩ := twExists_cube_root_unity hU F.ne_three
  have hωΩ3 : (algebraMap K Ω ωK) ^ 3 = 1 := by
    rw [← map_pow, hωK3, map_one]
  have hωΩ1 : algebraMap K Ω ωK ≠ 1 := fun h =>
    hωK1 ((algebraMap K Ω).injective (h.trans (map_one _).symm))
  have hcube : ∀ j, ∃ a : K, ((((A j τ : GL (Fin 3) K) * (x j : GL (Fin 3) K) :
      GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) ^ 3 = a • 1 :=
    twLayerProd_pow_three F.injective (twFrames_commute hl F.range) (A := fun j => A j τ)
      (fun j w => F.act j τ hτ w) x h3
  choose α hα using hcube
  obtain ⟨gK, cK, j₀, k₀, hjk, hcjk, hgK⟩ :=
    twExists_eigen_eq_of_not_hasCyclicVec3 hωK3 hωK1 (hα i) hcyc
  have hΩ : ∀ j, ∃ (G : GL (Fin 3) Ω) (c : Fin 3 → Ωˣ),
      gl3Emb K Ω ((A j τ : GL (Fin 3) K) * (x j : GL (Fin 3) K)) * G = G * diagGL3 c ∧
        (j = i → c j₀ = c k₀) := by
    intro j
    by_cases hji : j = i
    · subst hji
      refine ⟨gl3Emb K Ω gK, fun r => Units.map (algebraMap K Ω).toMonoidHom (cK r), ?_,
        fun _ => congrArg (Units.map (algebraMap K Ω).toMonoidHom) hcjk⟩
      rw [← map_mul, hgK, map_mul, twGl3Emb_diagGL3]
    · obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (α j))
        (by norm_num : 0 < 3)
      obtain ⟨G, c, hGc⟩ := twExists_mul_eq_diagGL3 hωΩ3 hωΩ1
        (M := gl3Emb K Ω ((A j τ : GL (Fin 3) K) * (x j : GL (Fin 3) K))) (μ := μ)
        (by rw [hμ]; exact twGl3Emb_pow_three (hα j))
      exact ⟨G, c, hGc, fun h => absurd h hji⟩
  choose G c hGc hci using hΩ
  choose d hd hreal using fun j => F.realizes j τ hτ
  choose u hu using fun j => (hreal j).diagGL3_mul ((x j : GL (Fin 3) K))
  have hPex : ∀ j, ∃ P : SL(3, Ω), toGL P * (diagGL3 (d j) *
      toGL (twUnitaryFrame hU (Hc j) (x j))) * (toGL P)⁻¹ = diagGL3 (fun r => u j * c j r) := by
    intro j
    refine twExists_SL_conj_diagGL3 (G := toGL (Hc j) * G j) ?_
    rw [toGL_twUnitaryFrame, hu j]
    exact twScalar_conj_mul_eq (hGc j) (u j) (toGL (Hc j))
  choose P hP using hPex
  have hτB : ∀ Z : Fin 3 → SL(3, Ω), twLinePsi K g₀ τ * twBlockProd Ω Z *
      (twLinePsi K g₀ τ)⁻¹ = twBlockProd Ω (fun j => conjDiag3 (d j) (Z j)) := by
    intro Z
    simp only [twBlockProd_apply]
    rw [← hd 0, ← hd 1, ← hd 2]
    group
  have hψv : twLinePsi K g₀ (τ * twLayerProd ρ x) = twLinePsi K g₀ τ *
      twBlockProd Ω (fun j => twUnitaryFrame hU (Hc j) (x j)) := by
    rw [map_mul, F.psi_layerProd]
  obtain ⟨N, hN⟩ : ∃ N : Fin 3 → SL(3, Ω),
      N = fun j => P j * conjDiag3 (d j) (twUnitaryFrame hU (Hc j) (x j) * (P j)⁻¹) := ⟨_, rfl⟩
  have ht : twBlockProd Ω P * twLinePsi K g₀ (τ * twLayerProd ρ x) * (twBlockProd Ω P)⁻¹ =
      twBlockProd Ω N * twLinePsi K g₀ τ := by
    have e1 : twBlockProd Ω N = twBlockProd Ω P * (twLinePsi K g₀ τ *
        twBlockProd Ω (fun j => twUnitaryFrame hU (Hc j) (x j) * (P j)⁻¹) *
          (twLinePsi K g₀ τ)⁻¹) := by
      rw [hτB, hN, ← map_mul]
      rfl
    have e2 : twBlockProd Ω (fun j => twUnitaryFrame hU (Hc j) (x j) * (P j)⁻¹) =
        twBlockProd Ω (fun j => twUnitaryFrame hU (Hc j) (x j)) * (twBlockProd Ω P)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e1, e2, hψv]
    group
  have hNj : ∀ j, toGL (N j) = diagGL3 (fun r => u j * c j r) * (diagGL3 (d j))⁻¹ := by
    intro j
    rw [← hP j, hN]
    simp only [map_mul, map_inv, toGL_conjDiag3]
    group
  have hNdiag : ∀ j r s, r ≠ s → ((N j : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) r s = 0 := by
    intro j r s hrs
    rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hNj j, ← twDiagGL3_inv, twDiagGL3_mul]
    exact Matrix.diagonal_apply_ne _ hrs
  have htH : twBlockProd Ω N * twLinePsi K g₀ τ ∈ torusGroup Tag.E6 Ω := by
    rw [twBlockProd_apply]
    exact mul_mem (mul_mem (mul_mem (twFrame_diag_mem_torusGroup 0 (hNdiag 0))
      (twFrame_diag_mem_torusGroup 1 (hNdiag 1))) (twFrame_diag_mem_torusGroup 2 (hNdiag 2)))
      (mem_twTorusHat.1 hτ).2
  have hact : ∀ W : SL(3, Ω), twBlockProd Ω N * twLinePsi K g₀ τ * twFrame Ω i W *
      (twBlockProd Ω N * twLinePsi K g₀ τ)⁻¹ =
        twFrame Ω i (conjDiag3 (fun r => u i * c i r) W) := by
    intro W
    have e1 : twBlockProd Ω N * twLinePsi K g₀ τ * twFrame Ω i W *
        (twBlockProd Ω N * twLinePsi K g₀ τ)⁻¹ = twBlockProd Ω N *
          (twLinePsi K g₀ τ * twFrame Ω i W * (twLinePsi K g₀ τ)⁻¹) * (twBlockProd Ω N)⁻¹ := by
      group
    rw [e1, hd i W]
    refine (commProd3_conj_apply (twFrame Ω) twFrame_commute N i _).trans
      (congrArg (twFrame Ω i) ?_)
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv, hNj i, toGL_conjDiag3, toGL_conjDiag3]
    group
  have hfix : twBlockProd Ω N * twLinePsi K g₀ τ *
      twFrame Ω i (Matrix.SpecialLinearGroup.transvection hjk 1) *
      (twBlockProd Ω N * twLinePsi K g₀ τ)⁻¹ =
        twFrame Ω i (Matrix.SpecialLinearGroup.transvection hjk 1) := by
    rw [hact, conjDiag3_transvection]
    congr 2
    show ((u i * c i j₀ : Ωˣ) : Ω) * 1 * (((u i * c i k₀)⁻¹ : Ωˣ) : Ω) = 1
    rw [hci i rfl, mul_one, Units.mul_inv]
  obtain ⟨ω, hω3, -, hψh₀⟩ := F.pic.h₀_image
  have hay : Commute (rootDiagUnit Tag.E6 (twLineChar ω)) (twBlockProd Ω P) := by
    rw [twBlockProd_apply]
    exact Commute.mul_right (Commute.mul_right
      (twLine_diag_commute hω3 0 (twFrame_mem_rootSpan 0 (P 0)))
      (twLine_diag_commute hω3 1 (twFrame_mem_rootSpan 1 (P 1))))
      (twLine_diag_commute hω3 2 (twFrame_mem_rootSpan 2 (P 2)))
  have hafix : rootDiagUnit Tag.E6 (twLineChar ω) *
      twFrame Ω i (Matrix.SpecialLinearGroup.transvection hjk 1) *
      (rootDiagUnit Tag.E6 (twLineChar ω))⁻¹ =
        twFrame Ω i (Matrix.SpecialLinearGroup.transvection hjk 1) := by
    rw [twLine_diag_commute hω3 i (twFrame_mem_rootSpan i _), mul_inv_cancel_right]
  have hn₀ : ∀ g, g ∈ torusGroup Tag.E6 Ω ↔
      twFrameN Ω i * g * (twFrameN Ω i)⁻¹ ∈ torusGroup Tag.E6 Ω :=
    Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer (R := Ω) (twE6FrameWeyl i))
  obtain ⟨z, hz⟩ : ∃ z : ModGL Tag.E6 Ω, z = twFrameN Ω i * twBlockProd Ω P := ⟨_, rfl⟩
  have ha'eq : z * twLinePsi K g₀ h₀ * z⁻¹ =
      twFrameN Ω i * rootDiagUnit Tag.E6 (twLineChar ω) * (twFrameN Ω i)⁻¹ := by
    rw [hz, hψh₀]
    calc twFrameN Ω i * twBlockProd Ω P * rootDiagUnit Tag.E6 (twLineChar ω) *
          (twFrameN Ω i * twBlockProd Ω P)⁻¹
        = twFrameN Ω i * (twBlockProd Ω P * rootDiagUnit Tag.E6 (twLineChar ω)) *
            (twBlockProd Ω P)⁻¹ * (twFrameN Ω i)⁻¹ := by group
      _ = twFrameN Ω i * (rootDiagUnit Tag.E6 (twLineChar ω) * twBlockProd Ω P) *
            (twBlockProd Ω P)⁻¹ * (twFrameN Ω i)⁻¹ := by rw [hay.eq]
      _ = twFrameN Ω i * rootDiagUnit Tag.E6 (twLineChar ω) * (twFrameN Ω i)⁻¹ := by group
  have ht'eq : z * twLinePsi K g₀ (τ * twLayerProd ρ x) * z⁻¹ =
      twFrameN Ω i * (twBlockProd Ω N * twLinePsi K g₀ τ) * (twFrameN Ω i)⁻¹ := by
    rw [hz, ← ht]
    group
  have haH : rootDiagUnit Tag.E6 (twLineChar ω) ∈ torusGroup Tag.E6 Ω := by
    rw [← hψh₀]
    exact ((F.pic.mem_T h₀).1 hl.h₀_mem_T).2
  have ha'H : z * twLinePsi K g₀ h₀ * z⁻¹ ∈ torusGroup Tag.E6 Ω := by
    rw [ha'eq]
    exact (hn₀ _).1 haH
  have ht'H : z * twLinePsi K g₀ (τ * twLayerProd ρ x) * z⁻¹ ∈ torusGroup Tag.E6 Ω := by
    rw [ht'eq]
    exact (hn₀ _).1 htH
  obtain ⟨α', hα'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ha'H
  obtain ⟨β', hβ'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht'H
  have hrα : rootChar α' (chainRoot chain13 j₀ k₀) = 1 := by
    apply twRootChar_eq_one_of_conj hjk
    rw [← hα', ha'eq]
    exact twFrameN_conj_fix i hafix
  have hrβ : rootChar β' (chainRoot chain13 j₀ k₀) = 1 := by
    apply twRootChar_eq_one_of_conj hjk
    rw [← hβ', ht'eq]
    exact twFrameN_conj_fix i hfix
  have hα'3 : rootDiagUnit Tag.E6 α' ^ 3 = 1 := by
    rw [← hα', conj_pow, ← map_pow, hl.h₀_pow, map_one, mul_one, mul_inv_cancel]
  have hβ'3 : rootDiagUnit Tag.E6 β' ^ 3 = 1 := by
    rw [← hβ', conj_pow, ← map_pow, h3, map_one, mul_one, mul_inv_cancel]
  have hdim : ∀ g : ModGL TwistTag.E6.tag K, Module.finrank Ω (LinearMap.ker
      (((z * twLinePsi K g₀ g * z⁻¹ : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) -
        1)) =
      Module.finrank K (LinearMap.ker ((g : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) :=
    fun g => (finrank_ker_conj_sub_one z _).trans (twFinrank_psi g₀ g)
  have hD0 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 α' : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24 := by
    rw [← hα', hdim]
    exact hl.finrank_fixed
  have hD1 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 β' : ModGL Tag.E6 Ω) :
      Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24 := by
    rw [← hβ', hdim]
    exact hd0
  have hD2 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 α' * rootDiagUnit Tag.E6 β' :
      ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) - 1)) = 24 := by
    have e : z * twLinePsi K g₀ h₀ * z⁻¹ * (z * twLinePsi K g₀ (τ * twLayerProd ρ x) * z⁻¹) =
        z * twLinePsi K g₀ (h₀ * (τ * twLayerProd ρ x)) * z⁻¹ := by
      rw [map_mul (twLinePsi K g₀) h₀]
      group
    rw [← hα', ← hβ', e, hdim]
    exact hd1
  have hD3 : Module.finrank Ω (LinearMap.ker (((rootDiagUnit Tag.E6 α' ^ 2 *
      rootDiagUnit Tag.E6 β' : ModGL Tag.E6 Ω) : Module.End Ω (RootModule Tag.E6 Ω)) - 1)) =
        24 := by
    have e : (z * twLinePsi K g₀ h₀ * z⁻¹) ^ 2 *
        (z * twLinePsi K g₀ (τ * twLayerProd ρ x) * z⁻¹) =
          z * twLinePsi K g₀ (h₀ ^ 2 * (τ * twLayerProd ρ x)) * z⁻¹ := by
      rw [conj_pow, map_mul (twLinePsi K g₀) (h₀ ^ 2), map_pow]
      group
    rw [← hα', ← hβ', e, hdim]
    exact hd2
  exact twLineSum_false (twThree_ne_zero hωΩ3 hωΩ1) hα'3 hβ'3 hD0 hD1 hD2 hD3
    ((e6Std_frame Ω).isRoot j₀ k₀ hjk) hrα hrβ

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
