module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismData

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup
open scoped Pointwise

section Model

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

variable {E : Type} [Field E] [Finite E] [CharP E 2]

theorem unitary_model_torus_eq_inf (J : HermitianForm 3 E) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card E = (2 ^ f) ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ S S₁ : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ ∧ S₁ ≠ S ∧
      Subgroup.normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ⊓
        Subgroup.normalizer (S₁ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
          unitaryCoverTorus J hJ ∧
      fusionStronglyEmbedded
        (Subgroup.normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∧
      Nat.card (Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) =
        Nat.card (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) + 1 := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hcard hfixed hJ
  obtain ⟨hNR, hcardS⟩ := normalizer_and_card_sylow J f hf hcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ) S
  have hHN : unitaryCoverTorus J hJ ≤
      Subgroup.normalizer (((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) : Set _) := by
    rw [hS]
    exact unitaryCoverTorus_le_normalizer J hJ
  rw [← hS] at hNR hcardS
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  have hHN₁ : unitaryCoverTorus J hJ ≤ Subgroup.normalizer
      ((((hermitianWeylPSU J hJ • S : Sylow 2 _)) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    rintro _ ⟨k, rfl⟩
    rw [Omega.mem_normalizer_conj_smul_iff]
    have h := weyl_conj_torus J hJ (Units.map J.conj.toMonoidHom k)⁻¹
    have hk : (Units.map J.conj.toMonoidHom (Units.map J.conj.toMonoidHom k)⁻¹)⁻¹ = k := by
      ext
      simp [J.conj_involutive (k : E)]
    rw [hk] at h
    have h2 : (hermitianWeylPSU J hJ)⁻¹ * hermitianTorusPSU J hJ k * hermitianWeylPSU J hJ =
        hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
      rw [← h]
      group
    rw [h2]
    exact hHN ⟨_, rfl⟩
  refine ⟨S, hermitianWeylPSU J hJ • S, hS, hS₁, ?_, hSE, hcardS⟩
  apply le_antisymm
  · intro g hg
    exact Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ hg.1 hg.2
  · intro g hg
    exact ⟨hHN hg, hHN₁ hg⟩

end Model

section Transfer

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI
open CFSG.ComponentClassification.AschbacherToolkit.Bender

theorem cartan_eq_inf_normalizer_smul {G : Type*} [Group G] (S : Sylow 2 G) {t : G}
    (ht : t * t = 1) :
    cartan (S : Subgroup G) t =
      Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer ((t • S : Sylow 2 G) : Set G) := by
  unfold cartan
  rw [conjugate_borel]
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj : conjugate (S : Subgroup G) t = ((t • S : Sylow 2 G) : Subgroup G) := by
    ext x
    rw [mem_conjugate_iff_mul_inv, mem_sylow_smul_iff, htt]
  rw [hconj]
  rfl

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem BenderType.exists_standard_iso_unitary {n e : ℕ} (h : BenderType K n 3 e)
    (Q : Sylow 2 K) {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (_ : Nat.card E = (2 ^ n) ^ 2)
      (_ : Nat.card {x : E // J.conj x = x} = 2 ^ n)
      (φ : K ≃* ProjectiveSpecialUnitaryMatrixGroup J),
      (Q : Subgroup K).map φ.toMonoidHom = unitaryCoverRoot J hJ ∧
      (cartan (Q : Subgroup K) t).map φ.toMonoidHom = unitaryCoverTorus J hJ := by
  obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨S, S₁, hS, hS₁, hcartan, hSE, hcardS⟩ :=
    unitary_model_torus_eq_inf J n hn hcard hfixed hJ
  obtain ⟨ε₁, hε₁⟩ :=
    CFSG.ProperTwoGeneratedCore.RootCenter.exists_mulEquiv_map_eq (e₁.trans e') S Q
  set φ₁ : K ≃* ProjectiveSpecialUnitaryMatrixGroup J := ε₁.symm with hφ₁
  have hQS : (Q : Subgroup K).map φ₁.toMonoidHom =
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← hε₁, Subgroup.map_map]
    ext x
    simp [hφ₁]
  have ht₁ : φ₁ t * φ₁ t = 1 := by rw [← map_mul, ht, map_one]
  have ht₁S : φ₁ t ∉ Subgroup.normalizer
      ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    intro hmem
    apply htQ
    have h1 : φ₁ t ∈ borel ((Q : Subgroup K).map φ₁.toMonoidHom) := by
      rw [hQS]
      exact hmem
    rw [borel_map] at h1
    obtain ⟨y, hy, hyt⟩ := h1
    have := φ₁.injective hyt
    rwa [← this]
  have hcart : (cartan (Q : Subgroup K) t).map φ₁.toMonoidHom =
      cartan (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (φ₁ t) := by
    rw [← hQS]
    exact (cartan_map φ₁ _ t).symm
  have h₀ : φ₁ t • S ≠ S := fun h => ht₁S (Sylow.smul_eq_iff_mem_normalizer.mp h)
  obtain ⟨r, hr, hrS⟩ := Omega.exists_smul_eq hSE hcardS h₀ hS₁
  have hrSS : r • S = S := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hr)
  have hφ : ((φ₁.trans (MulAut.conj r)).toMonoidHom) =
      (MulAut.conj r).toMonoidHom.comp φ₁.toMonoidHom := rfl
  refine ⟨E, hE, hF, J, hJ, hcard, hfixed, φ₁.trans (MulAut.conj r), ?_, ?_⟩
  · rw [hφ, ← Subgroup.map_map, hQS, ← hS]
    exact CFSG.ProperTwoGeneratedCore.RootCenter.map_conj_of_mem hr
  · rw [hφ, ← Subgroup.map_map, hcart, cartan_eq_inf_normalizer_smul S ht₁, ← hcartan]
    have e1 : ∀ y, y ∈ Subgroup.normalizer
        ((r • (φ₁ t • S) : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
        r⁻¹ * y * r ∈ Subgroup.normalizer
        ((φ₁ t • S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      fun y => Omega.mem_normalizer_conj_smul_iff
    have e2 : ∀ y, y ∈ Subgroup.normalizer
        (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
          r⁻¹ * y * r ∈ Subgroup.normalizer
            (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := fun y => by
      have := Omega.mem_normalizer_conj_smul_iff (x := r) (g := y) (S := S)
      rwa [hrSS] at this
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_inf, Subgroup.mem_inf,
      ← hrS, e1 x, ← e2 x]

end Transfer

end CFSG.GH74.Uniqueness.Bender
