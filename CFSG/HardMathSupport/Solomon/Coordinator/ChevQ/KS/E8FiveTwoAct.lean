module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE8Ten
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeCentralizer
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Timmesfeld.Steinberg
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Data

theorem cz_wbB_data : ∀ i : Fin 5,
    (∑ k, (czVec k : ℤ) * (wordMat Tag.E8 e8WordB *ᵥ e8a4Weight i) k) % 5 = 1 := by
  decide +kernel

@[expose] def xExpA : Fin 5 → ℤ := ![0, 2, 4, 1, 3]

@[expose] def xExpB : Fin 5 → ℤ := ![4, 3, 2, 1, 0]

theorem cx_wbA_data : ∀ i : Fin 5,
    (∑ k, (cxVec k : ℤ) * (wordMat Tag.E8 e8WordA *ᵥ e8a4Weight i) k) % 5 = xExpA i % 5 := by
  decide +kernel

theorem cx_wbB_data : ∀ i : Fin 5,
    (∑ k, (cxVec k : ℤ) * (wordMat Tag.E8 e8WordB *ᵥ e8a4Weight i) k) % 5 = xExpB i % 5 := by
  decide +kernel

end Data

section Acts

variable {L : Type} [Field L]

theorem conjDiagn_eq_conjSLn (d : Fin 5 → Lˣ) (A : SL(5, L)) :
    conjDiagn d A = conjSLn (diagGLn d) A := rfl

theorem actsBy_rootDiagUnit (v : WeylGroup Tag.E8) (b : Fin Tag.E8.rank → Lˣ) :
    ActsBy (rhoSigmaE8A4 L v) (rootDiagUnit Tag.E8 b)
      (diagGLn (fun i => rootChar b (wbE8A4 v i))) := fun A => by
  rw [rhoSigmaE8A4_torus, conjDiagn_eq_conjSLn]

variable {ζ : L}

theorem actsBy_z_A (hζ : IsPrimitiveRoot ζ 5) :
    ActsBy (rhoSigmaE8A4 L e8VA) (griessZ hζ) 1 := fun A => by
  rw [conjSLn_one', griessZ_comm_rhoA hζ A]
  group

theorem actsBy_z_B (hζ : IsPrimitiveRoot ζ 5) :
    ActsBy (rhoSigmaE8A4 L e8VB) (griessZ hζ) 1 := fun A => by
  have h : griessZ hζ * rhoSigmaE8A4 L e8VB A = rhoSigmaE8A4 L e8VB A * griessZ hζ :=
    rootDiagUnit_comm_rho hζ e8VB czVec 1 (fun i => by
      rw [show wbE8A4 e8VB i = wordMat Tag.E8 e8WordB *ᵥ e8a4Weight i from e8VB_smul _]
      exact cz_wbB_data i) A
  rw [conjSLn_one', h]
  group

theorem conjSLn_toGL' (S X : SL(5, L)) :
    conjSLn (Matrix.SpecialLinearGroup.toGL S) X = S * X * S⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSLn, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← map_inv,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem actsBy_x_A (hζ : IsPrimitiveRoot ζ 5) :
    ActsBy (rhoSigmaE8A4 L e8VA) (griessX hζ) (diagGLn (fun i => griessU hζ ^ xExpA i)) := by
  have h := actsBy_rootDiagUnit (L := L) e8VA (fun k => griessU hζ ^ cxVec k)
  have hd : (fun i => rootChar (fun k => griessU hζ ^ cxVec k) (wbE8A4 e8VA i)) =
      fun i => griessU hζ ^ xExpA i := by
    funext i
    rw [rootChar_powVec]
    exact zpow_eq_zpow_of_modEq (griessU_prim hζ) (by
      rw [show wbE8A4 e8VA i = wordMat Tag.E8 e8WordA *ᵥ e8a4Weight i from e8VA_smul _]
      exact cx_wbA_data i)
  rw [hd] at h
  exact h

theorem actsBy_x_B (hζ : IsPrimitiveRoot ζ 5) :
    ActsBy (rhoSigmaE8A4 L e8VB) (griessX hζ) (diagGLn (fun i => griessU hζ ^ xExpB i)) := by
  have h := actsBy_rootDiagUnit (L := L) e8VB (fun k => griessU hζ ^ cxVec k)
  have hd : (fun i => rootChar (fun k => griessU hζ ^ cxVec k) (wbE8A4 e8VB i)) =
      fun i => griessU hζ ^ xExpB i := by
    funext i
    rw [rootChar_powVec]
    exact zpow_eq_zpow_of_modEq (griessU_prim hζ) (by
      rw [show wbE8A4 e8VB i = wordMat Tag.E8 e8WordB *ᵥ e8a4Weight i from e8VB_smul _]
      exact cx_wbB_data i)
  rw [hd] at h
  exact h

variable {ρ : SL(5, L) →* ModGL Tag.E8 L} {ε ε₀ ε₁ : ModGL Tag.E8 L}
  {M M₀ M₁ : GL (Fin 5) L}

theorem ActsBy.inv' (h : ActsBy ρ ε M) : ActsBy ρ ε⁻¹ M⁻¹ := fun A => by
  have h1 := h (conjSLn M⁻¹ A)
  rw [← conjSLn_mul', mul_inv_cancel, conjSLn_one'] at h1
  calc ε⁻¹ * ρ A * ε⁻¹⁻¹ = ε⁻¹ * (ε * ρ (conjSLn M⁻¹ A) * ε⁻¹) * ε := by rw [h1]; group
    _ = ρ (conjSLn M⁻¹ A) := by group

theorem ActsBy.conj' {c : ModGL Tag.E8 L} {N : GL (Fin 5) L} (hc : ActsBy ρ c N)
    (h : ActsBy ρ ε M) : ActsBy ρ (c * ε * c⁻¹) (N * M * N⁻¹) :=
  (hc.mul h).mul hc.inv'

@[expose] def HeisShape (ρ : SL(5, L) →* ModGL Tag.E8 L) (εz ε₀ ε₁ : ModGL Tag.E8 L) : Prop :=
  ActsBy ρ εz 1 ∧ ∃ (M₀ M₁ : GL (Fin 5) L) (ζ c₀ c₁ : L), IsPrimitiveRoot ζ 5 ∧
    ActsBy ρ ε₀ M₀ ∧ ActsBy ρ ε₁ M₁ ∧
    (M₀ : Matrix (Fin 5) (Fin 5) L) * M₁ = ζ • ((M₁ : Matrix (Fin 5) (Fin 5) L) * M₀) ∧
    ((M₀ ^ 5 : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) = c₀ • 1 ∧
    ((M₁ ^ 5 : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) = c₁ • 1

theorem conj_mul_eq_smul (N M₀ M₁ : GL (Fin 5) L) {ζ : L}
    (h : (M₀ : Matrix (Fin 5) (Fin 5) L) * M₁ = ζ • ((M₁ : Matrix (Fin 5) (Fin 5) L) * M₀)) :
    ((N * M₀ * N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) * ((N * M₁ * N⁻¹ : GL (Fin 5) L) :
      Matrix (Fin 5) (Fin 5) L) = ζ • (((N * M₁ * N⁻¹ : GL (Fin 5) L) :
        Matrix (Fin 5) (Fin 5) L) * ((N * M₀ * N⁻¹ : GL (Fin 5) L) :
        Matrix (Fin 5) (Fin 5) L)) := by
  calc ((N * M₀ * N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) *
        ((N * M₁ * N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L)
      = ((N * (M₀ * M₁) * N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) := by
        rw [← Units.val_mul]
        congr 1
        group
    _ = (N : Matrix (Fin 5) (Fin 5) L) * ((M₀ : Matrix (Fin 5) (Fin 5) L) * M₁) *
          ((N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) := by
        simp only [Units.val_mul]
    _ = ζ • ((N : Matrix (Fin 5) (Fin 5) L) * ((M₁ : Matrix (Fin 5) (Fin 5) L) * M₀) *
          ((N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L)) := by
        rw [h, Matrix.mul_smul, Matrix.smul_mul]
    _ = ζ • (((N * M₁ * N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) *
          ((N * M₀ * N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L)) := by
        congr 1
        have := congrArg Units.val
          (show N * (M₁ * M₀) * N⁻¹ = (N * M₁ * N⁻¹) * (N * M₀ * N⁻¹) by group)
        simpa only [Units.val_mul] using this

theorem conj_pow_scalar (N M : GL (Fin 5) L) {c : L} {n : ℕ}
    (h : ((M ^ n : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) = c • 1) :
    (((N * M * N⁻¹) ^ n : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) = c • 1 := by
  rw [conj_pow]
  simp only [Units.val_mul]
  rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [show (N : Matrix (Fin 5) (Fin 5) L) * ((N⁻¹ : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) = 1
    from congrArg Units.val (mul_inv_cancel N)]

theorem HeisShape.conj_of_actsBy {εz : ModGL Tag.E8 L} {c : ModGL Tag.E8 L} {N : GL (Fin 5) L}
    (hc : ActsBy ρ c N) (h : HeisShape ρ εz ε₀ ε₁) :
    HeisShape ρ (c * εz * c⁻¹) (c * ε₀ * c⁻¹) (c * ε₁ * c⁻¹) := by
  obtain ⟨hz, M₀, M₁, ζ, c₀, c₁, hζ, h₀, h₁, hcomm, hc₀, hc₁⟩ := h
  refine ⟨?_, N * M₀ * N⁻¹, N * M₁ * N⁻¹, ζ, c₀, c₁, hζ, hc.conj' h₀, hc.conj' h₁,
    conj_mul_eq_smul N M₀ M₁ hcomm, conj_pow_scalar N M₀ hc₀, conj_pow_scalar N M₁ hc₁⟩
  have := hc.conj' hz
  simpa using this

@[expose] def actsSubgroup (ρ : SL(5, L) →* ModGL Tag.E8 L) : Subgroup (ModGL Tag.E8 L) where
  carrier := {g | ∃ M, ActsBy ρ g M}
  one_mem' := ⟨1, actsBy_one⟩
  mul_mem' := fun ⟨_, hM⟩ ⟨_, hN⟩ => ⟨_, hM.mul hN⟩
  inv_mem' := fun ⟨_, hM⟩ => ⟨_, hM.inv'⟩

theorem sup_le_actsSubgroup (v w : WeylGroup Tag.E8)
    (hcomm : ∀ A B, Commute (rhoSigmaE8A4 L v A) (rhoSigmaE8A4 L w B)) :
    torusGroup Tag.E8 L ⊔ ((rhoSigmaE8A4 L v).range ⊔ (rhoSigmaE8A4 L w).range) ≤
      actsSubgroup (rhoSigmaE8A4 L v) := by
  refine sup_le ?_ (sup_le ?_ ?_)
  · intro t ht
    obtain ⟨b, rfl⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup ht
    exact ⟨_, actsBy_rootDiagUnit v b⟩
  · rintro _ ⟨Y, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.toGL Y, fun A => ?_⟩
    rw [conjSLn_toGL', map_mul, map_mul, map_inv]
  · rintro _ ⟨B, rfl⟩
    refine ⟨1, fun A => ?_⟩
    rw [conjSLn_one']
    have h := (hcomm A B).symm.eq
    calc rhoSigmaE8A4 L w B * rhoSigmaE8A4 L v A * (rhoSigmaE8A4 L w B)⁻¹
        = (rhoSigmaE8A4 L v A * rhoSigmaE8A4 L w B) * (rhoSigmaE8A4 L w B)⁻¹ := by rw [h]
      _ = rhoSigmaE8A4 L v A := by group

theorem rhoA_commute_rhoB (A B : SL(5, L)) :
    Commute (rhoSigmaE8A4 L e8VA A) (rhoSigmaE8A4 L e8VB B) := by
  have hrA : (rhoSigmaE8A4 L e8VA).range = rootSpan Tag.E8 L {r | r ∈ e8ListA} :=
    (rhoSigmaE8A4_range e8VA).trans (congrArg _ QuasiE8Ten.sigmaSet_A)
  have hrB : (rhoSigmaE8A4 L e8VB).range = rootSpan Tag.E8 L {r | r ∈ e8ListB} :=
    (rhoSigmaE8A4_range e8VB).trans (congrArg _ QuasiE8Ten.sigmaSet_B)
  have hcomm : ∀ u ∈ rootSpan Tag.E8 L {r | r ∈ e8ListA},
      ∀ v ∈ rootSpan Tag.E8 L {r | r ∈ e8ListB}, u * v = v * u := by
    refine rootSpan_commute_of_orth (Or.inr (Or.inr (Or.inr rfl))) ?_ ?_ ?_
    · intro r hr
      obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_left _ hr)
      exact isRoot_e8RootVec m
    · intro r hr
      obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_right _ hr)
      exact isRoot_e8RootVec m
    · intro α hα β hβ
      exact e8_orth α hα β hβ
  refine hcomm _ ?_ _ ?_
  · rw [← hrA]; exact ⟨A, rfl⟩
  · rw [← hrB]; exact ⟨B, rfl⟩

theorem czVec_eq_zero {k : Fin Tag.E8.rank} (hk : k ≠ 4) : czVec k = 0 := by
  revert k; decide +kernel

theorem exists_actsBy_of_centralizer
    (hζ : IsPrimitiveRoot ζ 5) {g : ModGL Tag.E8 L} (hg : g ∈ adjointGroup Tag.E8 L)
    (hcomm : g * griessZ hζ = griessZ hζ * g) :
    (∃ M, ActsBy (rhoSigmaE8A4 L e8VA) g M) ∧ (∃ M, ActsBy (rhoSigmaE8A4 L e8VB) g M) := by
  set a : Fin Tag.E8.rank → Lˣ := fun k => griessU hζ ^ czVec k with ha
  have h5 : ∀ i, a i ^ 5 = 1 := fun i => congrFun (pow_five_vec hζ czVec) i
  have hgc : g ∈ toralCentralizer Tag.E8 L a := by
    rw [mem_toralCentralizer]
    refine ⟨hg, ?_⟩
    show griessZ hζ * g * (griessZ hζ)⁻¹ = g
    rw [← hcomm]
    group
  rw [toralCentralizer_eq_toralRootGroup_E8_five L a h5] at hgc
  have hker : rootCharKernel a ⊆ {r | r ∈ e8ListA} ∪ {r | r ∈ e8ListB} := by
    rintro α ⟨hα, hχ⟩
    have hsum : ∑ k, (czVec k : ℤ) * α k = α 4 := by
      rw [Finset.sum_eq_single (4 : Fin Tag.E8.rank)]
      · simp [czVec]
      · intro k _ hk
        simp [czVec_eq_zero hk]
      · simp
    have hdvd : (5 : ℤ) ∣ α 4 := by
      have h1 : griessU hζ ^ (α 4) = 1 := by
        rw [← hsum, ← rootChar_powVec]
        exact hχ
      have h2 := (orderOf_dvd_iff_zpow_eq_one (G := Lˣ) (x := griessU hζ) (i := α 4)).2 h1
      rwa [← (griessU_prim hζ).eq_orderOf] at h2
    rw [← e8_coset_eq]
    exact ⟨hα, hdvd⟩
  have hle : toralRootGroup Tag.E8 L a ≤ torusGroup Tag.E8 L ⊔
      ((rhoSigmaE8A4 L e8VA).range ⊔ (rhoSigmaE8A4 L e8VB).range) := by
    refine sup_le_sup_left ?_ _
    rw [(rhoSigmaE8A4_range e8VA).trans (congrArg _ QuasiE8Ten.sigmaSet_A),
      (rhoSigmaE8A4_range e8VB).trans (congrArg _ QuasiE8Ten.sigmaSet_B),
      ← CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.rootSpan_union_eq]
    exact rootSpan_mono hker
  refine ⟨sup_le_actsSubgroup e8VA e8VB rhoA_commute_rhoB (hle hgc), ?_⟩
  refine sup_le_actsSubgroup e8VB e8VA (fun B A => (rhoA_commute_rhoB A B).symm) ?_
  rw [sup_comm (rhoSigmaE8A4 L e8VB).range]
  exact hle hgc

end Acts

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
