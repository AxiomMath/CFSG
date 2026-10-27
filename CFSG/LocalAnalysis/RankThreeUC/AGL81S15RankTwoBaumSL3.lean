module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumPower
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Matrix Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.AGLEmbedding.ParabAutIrr
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)

private theorem slFieldAut_apply_map {K : Type} [Field K] (τ : K ≃+* K)
    (u : Matrix.SpecialLinearGroup (Fin 3) K) :
    slFieldAut (Fin 3) K τ u = SpecialLinearGroup.map τ.toRingHom u := rfl

private theorem exists_pow_mul_inv_mem_of_slConjugation_slFieldAut_unitriangular {K : Type}
    [Field K] [Finite K] [CharP K 2] (P : Matrix.GeneralLinearGroup (Fin 3) K) (σ : K ≃+* K)
    (hα : (unitriangular 3 K).map
      (slConjugation 3 K P * slFieldAut (Fin 3) K σ).toMonoidHom = unitriangular 3 K) :
    ∃ k : ℕ, ∀ b ∈ normalizer ((unitriangular 3 K :
        Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) :
        Set (Matrix.SpecialLinearGroup (Fin 3) K)),
      (slConjugation 3 K P * slFieldAut (Fin 3) K σ) b * (b ^ k)⁻¹ ∈ unitriangular 3 K := by
  have hmap : ∀ (τ : K ≃+* K) (u : SpecialLinearGroup (Fin 3) K),
      (u ∈ unitriangular 3 K → SpecialLinearGroup.map τ.toRingHom u ∈ unitriangular 3 K) ∧
      (u ∈ upperTriangular 3 K → SpecialLinearGroup.map τ.toRingHom u ∈ upperTriangular 3 K) := by
    intro τ u
    refine ⟨fun hu => ⟨fun i j hij => ?_, fun i => ?_⟩, fun hu i j hij => ?_⟩
    · simp [hu.1 i j hij]
    · simp [hu.2 i]
    · simp [hu i j hij]
  have hσU : (unitriangular 3 K).map (slFieldAut (Fin 3) K σ).toMonoidHom =
      unitriangular 3 K := by
    apply le_antisymm
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := hx
      change SpecialLinearGroup.map σ.toRingHom u ∈ unitriangular 3 K
      exact (hmap σ u).1 hu
    · intro u hu
      refine ⟨(slFieldAut (Fin 3) K σ)⁻¹ u, ?_, ?_⟩
      · rw [show (slFieldAut (Fin 3) K σ)⁻¹ = slFieldAut (Fin 3) K σ⁻¹ from
          (map_inv (slFieldAut (Fin 3) K) σ).symm]
        change SpecialLinearGroup.map (σ⁻¹).toRingHom u ∈ unitriangular 3 K
        exact (hmap σ⁻¹ u).1 hu
      · show slFieldAut (Fin 3) K σ ((slFieldAut (Fin 3) K σ)⁻¹ u) = u
        simp
  have hαc : (unitriangular 3 K).map (slConjugation 3 K P).toMonoidHom =
      unitriangular 3 K := by
    have hαcomp : (slConjugation 3 K P * slFieldAut (Fin 3) K σ).toMonoidHom =
        (slConjugation 3 K P).toMonoidHom.comp (slFieldAut (Fin 3) K σ).toMonoidHom :=
      MonoidHom.ext fun _ => rfl
    have h := hα
    rw [hαcomp, ← Subgroup.map_map, hσU] at h
    exact h
  have hcomp : (conjAut 3 K P).toMonoidHom.comp (proj 3 K) =
      (proj 3 K).comp (slConjugation 3 K P).toMonoidHom := by
    ext g
    exact conjAut_proj P g
  have hprojmap : (projUnitriangular 3 K).map (conjAut 3 K P).toMonoidHom =
      projUnitriangular 3 K := by
    unfold projUnitriangular
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hαc]
  have hcP : ∀ w : projectiveSL 3 K,
      w ∈ projUnitriangular 3 K ↔ conjAut 3 K P w ∈ projUnitriangular 3 K := by
    intro w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · rw [← hprojmap]
      exact ⟨w, hw, rfl⟩
    · rw [← hprojmap] at hw
      obtain ⟨x, hx, hxw⟩ := hw
      rw [(conjAut 3 K P).injective hxw] at hx
      exact hx
  have hA : (P : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
    isUpperTriangular_of_normalizes (K := K) (n := 3) (by norm_num) hcP
  obtain ⟨j, hj⟩ := exists_pow_two_of_ringEquiv σ
  refine ⟨2 ^ j, fun b hb => ?_⟩
  rw [normalizer_unitriangular (n := 3) (K := K)] at hb
  have hσb : slFieldAut (Fin 3) K σ b ∈ upperTriangular 3 K := by
    change SpecialLinearGroup.map σ.toRingHom b ∈ upperTriangular 3 K
    exact (hmap σ b).2 hb
  set y := slConjugation 3 K P (slFieldAut (Fin 3) K σ b) with hy
  have hyU : y ∈ upperTriangular 3 K := slConjugation_mem_upperTriangular hA hσb
  set Z : upperTriangular 3 K := (⟨b, hb⟩ : upperTriangular 3 K) ^ 2 ^ j with hZ
  have hdiag : diagHom 3 K ⟨y, hyU⟩ = diagHom 3 K Z := by
    ext i
    rw [diagHom_apply, hZ, map_pow, Pi.pow_apply, diagHom_apply]
    change ((y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = _
    rw [hy, slConjugation_diag hA hσb i, slFieldAut_apply_map σ b]
    simp [hj]
  have hx' : ((⟨y, hyU⟩ * Z⁻¹ : upperTriangular 3 K) :
      SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K := by
    rw [mem_unitriangular_iff_diagHom, map_mul, hdiag, ← map_mul, mul_inv_cancel, map_one]
  have hxe : ((⟨y, hyU⟩ * Z⁻¹ : upperTriangular 3 K) :
      SpecialLinearGroup (Fin 3) K) = y * (b ^ 2 ^ j)⁻¹ := by
    simp [hZ]
  have hx : y * (b ^ 2 ^ j)⁻¹ ∈ unitriangular 3 K := hxe ▸ hx'
  have hαb : (slConjugation 3 K P * slFieldAut (Fin 3) K σ) b = y := rfl
  rw [hαb]
  exact hx

theorem exists_pow_mul_inv_mem_of_slConjugation_slFieldAut {K : Type} [Field K] [Finite K]
    [CharP K 2] {U : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hU : IsSylowTwoOf U ⊤)
    (P : Matrix.GeneralLinearGroup (Fin 3) K) (σ : K ≃+* K)
    (hα : U.map (slConjugation 3 K P * slFieldAut (Fin 3) K σ).toMonoidHom = U) :
    ∃ k : ℕ, ∀ b ∈ normalizer (U : Set (Matrix.SpecialLinearGroup (Fin 3) K)),
      (slConjugation 3 K P * slFieldAut (Fin 3) K σ) b * (b ^ k)⁻¹ ∈ U := by
  let C : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) → Prop := fun α =>
    ∃ (P : Matrix.GeneralLinearGroup (Fin 3) K) (σ : K ≃+* K),
      α = slConjugation 3 K P * slFieldAut (Fin 3) K σ
  have hCα : C (slConjugation 3 K P * slFieldAut (Fin 3) K σ) := ⟨P, σ, rfl⟩
  obtain ⟨SU, hSU⟩ := exists_sylow_unitriangular (K := K) (p := 2) (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (unitriangular 3 K) ⊤ := by
    rw [← hSU]
    exact isSylowTwoOf_sylow SU
  refine exists_pow_action_of_isSylowTwoOf C ?hC hU₀ ?h₀ hU hCα hα
  ·
    rintro α ⟨P, σ, rfl⟩ g
    have hconj : ∀ x : Matrix.SpecialLinearGroup (Fin 3) K,
        MulAut.conj x = slConjugation 3 K (SpecialLinearGroup.toGL x) := by
      intro x
      refine MulEquiv.ext fun y => ?_
      apply SpecialLinearGroup.toGL_injective
      simp only [MulAut.conj_apply, toGL_slConjugation, map_mul, map_inv]
    have hfm : slFieldAut (Fin 3) K σ * MulAut.conj g =
        MulAut.conj (slFieldAut (Fin 3) K σ g) * slFieldAut (Fin 3) K σ := by
      calc slFieldAut (Fin 3) K σ * MulAut.conj g
          = (slFieldAut (Fin 3) K σ * MulAut.conj g * (slFieldAut (Fin 3) K σ)⁻¹) *
              slFieldAut (Fin 3) K σ := by
            simp only [mul_assoc, inv_mul_cancel, mul_one]
        _ = MulAut.conj (slFieldAut (Fin 3) K σ g) * slFieldAut (Fin 3) K σ := by
            rw [mul_conj_mul_inv]
    refine ⟨SpecialLinearGroup.toGL g⁻¹ * P *
      SpecialLinearGroup.toGL (slFieldAut (Fin 3) K σ g), σ, ?_⟩
    calc MulAut.conj g⁻¹ * (slConjugation 3 K P * slFieldAut (Fin 3) K σ) *
          MulAut.conj g
        = MulAut.conj g⁻¹ * (slConjugation 3 K P *
            (slFieldAut (Fin 3) K σ * MulAut.conj g)) := by
          simp only [mul_assoc]
      _ = MulAut.conj g⁻¹ * (slConjugation 3 K P *
            (MulAut.conj (slFieldAut (Fin 3) K σ g) * slFieldAut (Fin 3) K σ)) := by
          rw [hfm]
      _ = MulAut.conj g⁻¹ * (slConjugation 3 K P *
            slConjugation 3 K (SpecialLinearGroup.toGL (slFieldAut (Fin 3) K σ g))) *
            slFieldAut (Fin 3) K σ := by
          rw [hconj (slFieldAut (Fin 3) K σ g)]
          simp only [mul_assoc]
      _ = MulAut.conj g⁻¹ * slConjugation 3 K (P *
            SpecialLinearGroup.toGL (slFieldAut (Fin 3) K σ g)) *
            slFieldAut (Fin 3) K σ := by
          rw [← map_mul (slConjugation 3 K)]
      _ = slConjugation 3 K (SpecialLinearGroup.toGL g⁻¹) *
            slConjugation 3 K (P * SpecialLinearGroup.toGL (slFieldAut (Fin 3) K σ g)) *
            slFieldAut (Fin 3) K σ := by
          rw [hconj g⁻¹]
      _ = slConjugation 3 K (SpecialLinearGroup.toGL g⁻¹ *
            (P * SpecialLinearGroup.toGL (slFieldAut (Fin 3) K σ g))) *
            slFieldAut (Fin 3) K σ := by
          rw [← map_mul (slConjugation 3 K)]
      _ = slConjugation 3 K (SpecialLinearGroup.toGL g⁻¹ * P *
            SpecialLinearGroup.toGL (slFieldAut (Fin 3) K σ g)) *
            slFieldAut (Fin 3) K σ := by
          rw [mul_assoc]
  ·
    rintro α ⟨P, σ, rfl⟩ hαU₀
    exact exists_pow_mul_inv_mem_of_slConjugation_slFieldAut_unitriangular P σ hαU₀

end CFSG.LocalAnalysis.RankThreeUC.S15

end
