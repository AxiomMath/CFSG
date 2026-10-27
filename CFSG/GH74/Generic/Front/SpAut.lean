module

public import CFSG.GH74.Generic.Front.DataSp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoTypePreservation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups

section Aut

variable {F : Type} [Field F]

theorem isPerfect_statedSp2_of_odd [Finite F] (hF : Odd (Nat.card F)) :
    Group.IsPerfect (StatedSp 2 F) := by
  apply CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 F
  by_cases h4 : 4 ≤ Nat.card F
  · left
    have := Fintype.ofFinite F
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨t, ht⟩
  · right
    left
    have hcard2 : 2 ≤ Nat.card F := Finite.one_lt_card
    refine ⟨?_, le_rfl⟩
    obtain ⟨m, hm⟩ := hF
    omega

theorem spScalars_eq_center : spScalars 2 F = Subgroup.center ↥(StatedSp 2 F) :=
  (CFSG.LieType.Universal.Symplectic.center_eq 2 F).symm

theorem mulAut_mem_spScalars (α : MulAut ↥(StatedSp 2 F)) {z : ↥(StatedSp 2 F)}
    (hz : z ∈ spScalars 2 F) : α z ∈ spScalars 2 F := by
  rw [spScalars_eq_center] at hz ⊢
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have h1 := congrArg α (hz (α.symm g))
  simpa [map_mul] using h1

@[expose] noncomputable def descentAut (α : MulAut ↥(StatedSp 2 F)) : MulAut (StatedProj (StatedSp 2 F)) :=
  quotientAutHom (MonoidHom.id (MulAut ↥(StatedSp 2 F))) (spScalars 2 F)
    (fun _ _ hg => mulAut_mem_spScalars _ hg) α

theorem descentAut_proj (α : MulAut ↥(StatedSp 2 F)) (g : ↥(StatedSp 2 F)) :
    descentAut α (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F g) = CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F (α g) := rfl

theorem exists_conjAut_fieldAut [Finite F] (hF : Odd (Nat.card F))
    (β : MulAut (StatedProj (StatedSp 2 F))) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), β = conjAut 2 F A * fieldAut 2 F σ := by
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hF
  have hodd : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  obtain ⟨-, htop, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.odd_symplectic_two_type_preservation
      (K := F) hodd
  have hβ : β ∈ CFSG.ComponentClassification.CatalogueBSymplecticTwo.typeKernel F := by
    rw [htop]
    trivial
  exact (CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := F)).2.1 β hβ

theorem aut_statedSp2 [Finite F] (hF : Odd (Nat.card F)) (α : MulAut ↥(StatedSp 2 F)) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), α = conjSp 2 F A * fieldSp 2 F σ := by
  obtain ⟨A, σ, hAσ⟩ := exists_conjAut_fieldAut hF (descentAut α)
  refine ⟨A, σ, ?_⟩
  set τ : MulAut ↥(StatedSp 2 F) := conjSp 2 F A * fieldSp 2 F σ with hτ
  have hmod : ∀ g : ↥(StatedSp 2 F), (α g)⁻¹ * τ g ∈ spScalars 2 F := by
    intro g
    have h1 : CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F (α g) = CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F (τ g) := by
      rw [← descentAut_proj, hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
      rfl
    exact QuotientGroup.eq.1 h1
  have hcent : ∀ g, (α g)⁻¹ * τ g ∈ Subgroup.center ↥(StatedSp 2 F) := by
    intro g
    rw [← spScalars_eq_center]
    exact hmod g
  have hperf := isPerfect_statedSp2_of_odd hF
  let χ : ↥(StatedSp 2 F) →* Subgroup.center ↥(StatedSp 2 F) :=
    { toFun := fun g => ⟨(α g)⁻¹ * τ g, hcent g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (hcent g)
        have hc' : (α h)⁻¹ * ((α g)⁻¹ * τ g) = ((α g)⁻¹ * τ g) * (α h)⁻¹ := hc ((α h)⁻¹)
        change (α (g * h))⁻¹ * τ (g * h) = (α g)⁻¹ * τ g * ((α h)⁻¹ * τ h)
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc (α h)⁻¹ * (α g)⁻¹ * (τ g * τ h) = ((α h)⁻¹ * ((α g)⁻¹ * τ g)) * τ h := by
              simp only [mul_assoc]
          _ = ((α g)⁻¹ * τ g) * (α h)⁻¹ * τ h := by rw [hc']
          _ = (α g)⁻¹ * τ g * ((α h)⁻¹ * τ h) := by simp only [mul_assoc] }
  have hker : _root_.commutator ↥(StatedSp 2 F) ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : _root_.commutator ↥(StatedSp 2 F) = ⊤ := Group.IsPerfect.commutator_eq_top
  refine MulEquiv.ext fun g => ?_
  have hg : g ∈ χ.ker := hker (htop ▸ Subgroup.mem_top g)
  have h1 : (α g)⁻¹ * τ g = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
  exact inv_mul_eq_one.1 h1

theorem coe_tau (A : gsp 2 F) (σ : F ≃+* F) (k : ↥(StatedSp 2 F)) :
    ((((conjSp 2 F A * fieldSp 2 F σ) k : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ *
        (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  rw [MulAut.mul_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

theorem trace_spDiagHom (X : SL(2, F)) :
    Matrix.trace ((((spDiagHom (X, 1) : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) =
      (X : Matrix (Fin 2) (Fin 2) F) 0 0 + (X : Matrix (Fin 2) (Fin 2) F) 1 1 + 2 := by
  rw [spDiagHom_val]
  simp [sp2Diag_apply, planeDiag, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

@[expose] def companionSL (x : F) : SL(2, F) :=
  ⟨!![x, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def upperSp (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) :
    ↥(StatedSp 2 F) :=
  ⟨(CFSG.ClassicalGroups.Symplectic.upperUnipotent hS : TauCeti.GLSymplectic (Fin 2) F), by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (CFSG.ClassicalGroups.Symplectic.upperUnipotent hS).2⟩

@[expose] noncomputable def lowerSp (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) :
    ↥(StatedSp 2 F) :=
  ⟨(CFSG.ClassicalGroups.Symplectic.lowerUnipotent hS : TauCeti.GLSymplectic (Fin 2) F), by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (CFSG.ClassicalGroups.Symplectic.lowerUnipotent hS).2⟩

theorem coe_upperSp (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) :
    (((upperSp S hS : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 1 S 0 1 := by
  exact CFSG.ClassicalGroups.Symplectic.coe_upperUnipotent hS

theorem coe_lowerSp (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) :
    (((lowerSp S hS : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 1 0 S 1 := by
  exact CFSG.ClassicalGroups.Symplectic.coe_lowerUnipotent hS

theorem sq_one_matrix [Finite F] (M Ai : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (σ : F ≃+* F)
    (hMAi : M * Ai = 1) (hAiM : Ai * M = 1)
    (h : ∀ k : ↥(StatedSp 2 F),
      M * (M.map σ * ((((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ).map σ) *
        Ai.map σ) * Ai = ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :
    σ * σ = 1 ∧ ∃ c : F, M * M.map σ = c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  classical
  have hMσ : M.map σ * Ai.map σ = 1 := by
    rw [← map_mul_ringEquiv, hMAi]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hσM : Ai.map σ * M.map σ = 1 := by
    rw [← map_mul_ringEquiv, hAiM]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hBBi : (M * M.map σ) * (Ai.map σ * Ai) = 1 := by
    calc (M * M.map σ) * (Ai.map σ * Ai) = M * (M.map σ * Ai.map σ) * Ai := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMσ, Matrix.mul_one, hMAi]
  have hBiB : (Ai.map σ * Ai) * (M * M.map σ) = 1 := by
    calc (Ai.map σ * Ai) * (M * M.map σ) = Ai.map σ * (Ai * M) * M.map σ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAiM, Matrix.mul_one, hσM]
  have hττ : ∀ k : ↥(StatedSp 2 F),
      (M * M.map σ) *
          ((((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ).map σ) *
        (Ai.map σ * Ai) =
        ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k
    refine Eq.trans ?_ (h k)
    simp only [Matrix.mul_assoc]
  have htr : ∀ N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      Matrix.trace ((M * M.map σ) * N * (Ai.map σ * Ai)) = Matrix.trace N := by
    intro N
    rw [Matrix.trace_mul_comm ((M * M.map σ) * N) (Ai.map σ * Ai), ← Matrix.mul_assoc, hBiB,
      Matrix.one_mul]
  have hmap : ∀ N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      Matrix.trace (N.map σ) = σ (Matrix.trace N) := by
    intro N
    simp [Matrix.trace]
  have hσσ : ∀ x : F, σ (σ x) = x := by
    intro x
    have h1 := hττ (spDiagHom (companionSL x, 1))
    have h2' := congrArg Matrix.trace h1
    rw [htr, hmap, hmap, trace_spDiagHom] at h2'
    simp [companionSL] at h2'
    have e2 : σ (σ (2 : F)) = 2 := by rw [map_ofNat, map_ofNat]
    linear_combination h2' - e2
  have hσ2 : σ * σ = 1 := RingEquiv.ext hσσ
  refine ⟨hσ2, ?_⟩
  have hmapmap : ∀ N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, (N.map σ).map σ = N := by
    intro N
    ext i j
    simp [hσσ]
  have hcomm : ∀ k : ↥(StatedSp 2 F),
      (M * M.map σ) * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (M * M.map σ) := by
    intro k
    have h' := hττ k
    rw [hmapmap] at h'
    calc (M * M.map σ) * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
        = (M * M.map σ) * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
            ((Ai.map σ * Ai) * (M * M.map σ)) := by rw [hBiB, Matrix.mul_one]
      _ = ((M * M.map σ) * ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
            (Ai.map σ * Ai)) * (M * M.map σ) := by simp only [Matrix.mul_assoc]
      _ = ((k : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
            (M * M.map σ) := by rw [h']
  obtain ⟨d, hd⟩ := CFSG.ClassicalGroups.Symplectic.eq_scalar_of_commute_unipotents (M * M.map σ)
    (fun S hS => by
      have := hcomm (upperSp S hS)
      rwa [coe_upperSp] at this)
    (fun S hS => by
      have := hcomm (lowerSp S hS)
      rwa [coe_lowerSp] at this)
  refine ⟨d, ?_⟩
  rw [hd, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem sq_one_consequences [Finite F] (A : gsp 2 F) (σ : F ≃+* F)
    (h2 : ∀ k : ↥(StatedSp 2 F),
      (conjSp 2 F A * fieldSp 2 F σ) ((conjSp 2 F A * fieldSp 2 F σ) k) = k) :
    σ * σ = 1 ∧ ∃ c : F,
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ =
          c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  refine sq_one_matrix ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) σ (by simp) (by simp) ?_
  intro k
  have h := congrArg (fun u : ↥(StatedSp 2 F) =>
    ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (h2 k)
  simp only [coe_tau] at h
  rw [map_mul_ringEquiv, map_mul_ringEquiv] at h
  exact h

end Aut

end CFSG.GH74.Generic
