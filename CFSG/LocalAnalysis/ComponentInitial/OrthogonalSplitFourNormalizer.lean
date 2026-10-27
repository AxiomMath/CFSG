module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit
import CFSG.Quasithin.Background.P3OrthoOm4
import CFSG.RankThree.PartOne.S11d.OrthSplitModel

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem exists_mul_mul_ne_transpose {M N : Matrix (Fin 2) (Fin 2) K}
    (hMN : M * N = 1) (hNM : N * M = 1) :
    ∃ X : Matrix (Fin 2) (Fin 2) K, M * X * N ≠ Xᵀ := by
  by_contra hcon
  have hcon : ∀ X : Matrix (Fin 2) (Fin 2) K, M * X * N = Xᵀ :=
    fun X => not_not.mp (not_exists.mp hcon X)
  have key : ∀ X Y : Matrix (Fin 2) (Fin 2) K, Xᵀ * Yᵀ = Yᵀ * Xᵀ := by
    intro X Y
    calc Xᵀ * Yᵀ = (M * X * N) * (M * Y * N) := by rw [hcon X, hcon Y]
      _ = M * X * (N * M) * Y * N := by noncomm_ring
      _ = M * (X * Y) * N := by rw [hNM]; noncomm_ring
      _ = (X * Y)ᵀ := hcon (X * Y)
      _ = Yᵀ * Xᵀ := Matrix.transpose_mul X Y
  have h := congrArg (fun Z : Matrix (Fin 2) (Fin 2) K => Z 0 0)
    (key (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K))
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h

theorem rho_ne_tau (z : equalDeterminants K) : rho z ≠ tau := by
  intro h
  have hX : ∀ X : Matrix (Fin 2) (Fin 2) K,
      z.val.1.val * X * (z.val.2⁻¹).val = Xᵀ := by
    intro X
    have h' := congrArg (fun g : DeterminantIsometries K => g.val X) h
    rwa [rho_apply, tau_apply] at h'
  have hMN : z.val.1.val * (z.val.2⁻¹).val = 1 := by
    have h' := hX 1
    rwa [Matrix.mul_one, Matrix.transpose_one] at h'
  have hNM : (z.val.2⁻¹).val * z.val.1.val = 1 := by
    have hu : z.val.1 * z.val.2⁻¹ = 1 := Units.ext hMN
    have h2 : z.val.2⁻¹ = z.val.1⁻¹ := eq_inv_of_mul_eq_one_right hu
    rw [h2]
    exact Units.inv_mul z.val.1
  obtain ⟨X, hXne⟩ := exists_mul_mul_ne_transpose hMN hNM
  exact hXne (hX X)

theorem tau_notMem_specialImage : (tau : DeterminantIsometries K) ∉ specialImage K := by
  rintro ⟨z, hz⟩
  exact rho_ne_tau (specialPairs z) (by simpa [specialRho] using hz)

variable [Finite K] [CharP K 2]

theorem index_specialImage : (specialImage K).index = 2 := by
  refine Subgroup.index_eq_two_iff.mpr ⟨tau, fun b => ?_⟩
  have hkey : ∀ b : DeterminantIsometries K,
      b * tau ∈ specialImage K → b ∉ specialImage K := by
    intro b hbt hb
    exact tau_notMem_specialImage (K := K) (by
      have h := (specialImage K).mul_mem ((specialImage K).inv_mem hb) hbt
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h)
  rcases CFSG.Quasithin.G11.P3Ortho.Om4.mem_specialImage_or_mul_tau b with hb | hb
  · exact Or.inr ⟨hb, fun hbt => hkey b hbt hb⟩
  · exact Or.inl ⟨hb, fun hbj => hkey b hb hbj⟩

theorem conj_mem_determinantRightFactor {g x : DeterminantIsometries K}
    (hg : g ∉ specialImage K) (hx : x ∈ determinantLeftFactor K) :
    g * x * g⁻¹ ∈ determinantRightFactor K := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨z₁, z₂, hz⟩ := CFSG.RankThree.PartOne.exists_swap hg
  obtain ⟨A', B', hA', -, hconj⟩ := hz A 1
  have hA'1 : A' = 1 := by
    have h1 : Matrix.SpecialLinearGroup.toGL (1 : Matrix.SpecialLinearGroup (Fin 2) K) = 1 :=
      map_one _
    have h2 : inverseTranspose (1 : Matrix.GeneralLinearGroup (Fin 2) K) = 1 := by
      apply Units.ext
      simp [inverseTranspose]
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hA', h1, h2, mul_one, mul_inv_cancel]
  subst hA'1
  refine ⟨B', ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.inr_apply, MonoidHom.comp_apply,
    MonoidHom.inl_apply]
  exact hconj.symm

theorem conj_mem_determinantLeftFactor {g x : DeterminantIsometries K}
    (hg : g ∉ specialImage K) (hx : x ∈ determinantRightFactor K) :
    g * x * g⁻¹ ∈ determinantLeftFactor K := by
  obtain ⟨B, rfl⟩ := hx
  obtain ⟨z₁, z₂, hz⟩ := CFSG.RankThree.PartOne.exists_swap hg
  obtain ⟨A', B', -, hB', hconj⟩ := hz 1 B
  have hB'1 : B' = 1 := by
    have h1 : Matrix.SpecialLinearGroup.toGL (1 : Matrix.SpecialLinearGroup (Fin 2) K) = 1 :=
      map_one _
    have h2 : inverseTranspose (1 : Matrix.GeneralLinearGroup (Fin 2) K) = 1 := by
      apply Units.ext
      simp [inverseTranspose]
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hB', h1, h2, mul_one, mul_inv_cancel]
  subst hB'1
  refine ⟨A', ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.comp_apply,
    MonoidHom.inr_apply]
  exact hconj.symm

private theorem specialRho_inl_mem (A : SL(2, K)) :
    specialRho (A, 1) ∈ determinantLeftFactor K :=
  ⟨A, by rw [MonoidHom.comp_apply, MonoidHom.inl_apply]⟩

private theorem specialRho_inr_mem (B : SL(2, K)) :
    specialRho (1, B) ∈ determinantRightFactor K :=
  ⟨B, by rw [MonoidHom.comp_apply, MonoidHom.inr_apply]⟩

private theorem unipotentSL_ne_one : (unipotentSL K : SL(2, K)) ≠ 1 := by
  intro h
  have h' := congrArg (fun A : SL(2, K) => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simpa [unipotentSL] using h'

private theorem not_determinantLeftFactor_le_right :
    ¬ determinantLeftFactor K ≤ determinantRightFactor K := by
  intro hle
  obtain ⟨B, hB⟩ := hle (specialRho_inl_mem (unipotentSL K))
  have hB' : specialRho ((unipotentSL K, 1) : SL(2, K) × SL(2, K)) =
      specialRho ((1, B) : SL(2, K) × SL(2, K)) := by
    simpa [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] using hB.symm
  have hpair := congrArg Prod.fst (CFSG.RankThree.PartOne.specialRho_injective hB')
  exact unipotentSL_ne_one hpair

private theorem not_determinantRightFactor_le_left :
    ¬ determinantRightFactor K ≤ determinantLeftFactor K := by
  intro hle
  obtain ⟨B, hB⟩ := hle (specialRho_inr_mem (unipotentSL K))
  have hB' : specialRho ((1, unipotentSL K) : SL(2, K) × SL(2, K)) =
      specialRho ((B, 1) : SL(2, K) × SL(2, K)) := by
    simpa [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] using hB.symm
  have hpair := congrArg Prod.snd (CFSG.RankThree.PartOne.specialRho_injective hB')
  exact unipotentSL_ne_one hpair

theorem normalizer_determinantLeftFactor_le :
    normalizer (determinantLeftFactor K : Set (DeterminantIsometries K)) ≤ specialImage K := by
  intro g hg
  by_contra hgJ
  have hLR : determinantLeftFactor K ≤ determinantRightFactor K := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ determinantLeftFactor K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using h1
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ determinantRightFactor K :=
      conj_mem_determinantRightFactor hgJ hx'
    have h3 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h3] at h2
  exact not_determinantLeftFactor_le_right hLR

theorem normalizer_determinantRightFactor_le :
    normalizer (determinantRightFactor K : Set (DeterminantIsometries K)) ≤ specialImage K := by
  intro g hg
  by_contra hgJ
  have hRL : determinantRightFactor K ≤ determinantLeftFactor K := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ determinantRightFactor K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using h1
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ determinantLeftFactor K :=
      conj_mem_determinantLeftFactor hgJ hx'
    have h3 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [h3] at h2
  exact not_determinantRightFactor_le_left hRL

end CFSG.LocalAnalysis.ComponentInitial
