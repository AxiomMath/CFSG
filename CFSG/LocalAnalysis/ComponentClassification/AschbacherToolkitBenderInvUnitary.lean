module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitaryCoord
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace UnitaryAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem invDichotomyAt_root (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ) :
    InvDichotomyAt (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  classical
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hconjU : ∀ (k : Kˣ) (z : hermitianUnipotentCoord J),
      hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹ =
        U (hermitianTorusAction J k z) := unitaryCoverTorus_conj_root J hJ
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  have hHN : unitaryCoverTorus J hJ ≤
      Subgroup.normalizer (((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) : Set _) := by
    rw [hS]
    exact unitaryCoverTorus_le_normalizer J hJ
  rw [← hS] at hNR hcard
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
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
      simp [J.conj_involutive (k : K)]
    rw [hk] at h
    have h2 : (hermitianWeylPSU J hJ)⁻¹ * hermitianTorusPSU J hJ k * hermitianWeylPSU J hJ =
        hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
      rw [← h]
      group
    rw [h2]
    exact hHN ⟨_, rfl⟩
  apply invDichotomyAt_of_twisted hSE hcard hS₁
  intro α' hα'α' hα'S hα'S₁ r hr hα'r
  have hα'H : ∀ k : Kˣ, ∃ k' : Kˣ, α' (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k' := by
    intro k
    have h1 := Omega.mem_normalizer_smul (α := α') (hHN ⟨k, rfl⟩)
    have h2 := Omega.mem_normalizer_smul (α := α') (hHN₁ ⟨k, rfl⟩)
    rw [hα'S] at h1
    rw [hα'S₁] at h2
    obtain ⟨k', hk'⟩ := Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2
    exact ⟨k', hk'.symm⟩
  have hRS : ∀ z, U z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := fun z => by
    rw [hS]
    exact ⟨z, rfl⟩
  have hex : ∀ z : hermitianUnipotentCoord J, ∃ z', α' (U z) = U z' := by
    intro z
    have h := InvInner.apply_mem_of_smul_eq hα'S (hRS z)
    rw [hS] at h
    obtain ⟨z', hz'⟩ := h
    exact ⟨z', hz'.symm⟩
  choose ψf hψf using hex
  let ψ : hermitianUnipotentCoord J →* hermitianUnipotentCoord J :=
    { toFun := ψf
      map_one' := by
        apply hU
        rw [← hψf, map_one, map_one]
      map_mul' := fun z z' => by
        apply hU
        rw [← hψf, map_mul, map_mul, map_mul, hψf, hψf] }
  have hψU : ∀ z, U (ψ z) = α' (U z) := fun z => (hψf z).symm
  have hψψ : ∀ z, ψ (ψ z) = z := fun z => hU (by rw [hψU, hψU, hα'α'])
  have hψinj : Function.Injective ψ := fun z z' h => by rw [← hψψ z, h, hψψ]
  have hψtor : ∀ k : Kˣ, ∃ k' : Kˣ,
      ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z) := by
    intro k
    obtain ⟨k', hk'⟩ := hα'H k
    refine ⟨k', fun z => hU ?_⟩
    calc U (ψ (hermitianTorusAction J k z)) = α' (U (hermitianTorusAction J k z)) := hψU _
      _ = α' (hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹) := by
          rw [hconjU]
      _ = α' (hermitianTorusPSU J hJ k) * α' (U z) * (α' (hermitianTorusPSU J hJ k))⁻¹ := by
          rw [map_mul, map_mul, mulAut_apply_inv]
      _ = hermitianTorusPSU J hJ k' * U (ψ z) * (hermitianTorusPSU J hJ k')⁻¹ := by
          rw [hk', hψU]
      _ = U (hermitianTorusAction J k' (ψ z)) := hconjU k' (ψ z)
  have hψcen := UnitaryCoordAut.center_fixed J (2 ^ f) hKcard hfixed hq4 hJ ψ hψψ hψtor
  obtain ⟨lam, hNlam, hform⟩ := UnitaryCoordAut.coordAut_form J (2 ^ f) hKcard hfixed hq4 hJ ψ
    hψinj hψcen hψtor
  obtain ⟨c, rfl⟩ : ∃ c, U c = r := by
    have h := hr
    rw [hS] at h
    exact h
  rcases hform with hid | hconj
  ·
    left
    obtain ⟨z₁, hz₁⟩ :=
      unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ (Multiplicative.ofAdd 1)
    have hz₁1 : z₁.1.1 = 1 := congrArg Multiplicative.toAdd hz₁
    have hlam2 : lam * lam = 1 := by
      have h := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) (hψψ z₁)
      change (ψ (ψ z₁)).1.1 = z₁.1.1 at h
      rw [(hid (ψ z₁)).1, (hid z₁).1, hz₁1] at h
      linear_combination h
    have hlam1 : lam = 1 :=
      CharTwo.sq_injective (show lam ^ 2 = 1 ^ 2 by rw [sq, hlam2, one_pow])
    intro s hs
    rw [hS] at hs
    obtain ⟨z, rfl⟩ := hs
    rw [← hψU]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change (ψ z).1.1 = z.1.1
      rw [(hid z).1, hlam1, one_mul]
    · exact (hid z).2
  ·
    right
    have hψc : ψ c = c⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      apply hU
      rw [map_mul, hψU, hα'r, inv_mul_cancel, map_one]
    have hc1 : lam * J.conj c.1.1 = -c.1.1 := by
      have h := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) hψc
      change (ψ c).1.1 = -c.1.1 at h
      rw [(hconj c).1] at h
      exact h
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (lam * c.1.2)
    obtain ⟨z, hz⟩ :=
      unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ (Multiplicative.ofAdd s)
    have hz1 : z.1.1 = s := congrArg Multiplicative.toAdd hz
    refine ⟨U z, hRS z, ?_⟩
    rw [← hψU, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change c.1.1 = z.1.1 + -(ψ z).1.1
      rw [(hconj z).1, hz1]
      apply CharTwo.sq_injective
      change c.1.1 ^ 2 = (s + -(lam * J.conj s)) ^ 2
      have hs' : J.conj lam * J.conj c.1.2 = J.conj s * J.conj s := by
        rw [← map_mul, hs, map_mul]
      have hcc := c.2
      linear_combination hs + lam ^ 2 * hs' - lam * hcc - lam * J.conj c.1.2 * hNlam +
        c.1.1 * hc1 + lam * s * J.conj s * (CharTwo.two_eq_zero (R := K))
    · change c.1.2 = z.1.2 + J.conj (ψ z).1.2 - z.1.1 * J.conj (-(ψ z).1.1)
      rw [(hconj z).1, (hconj z).2, hz1, map_neg, map_add, map_mul, map_mul, J.conj_involutive]
      have hz2 := z.2
      rw [hz1] at hz2
      linear_combination -hz2 + J.conj lam * hs - c.1.2 * hNlam

end UnitaryAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups UnitaryAut in
theorem invDichotomyAt_of_mulEquiv_psu3 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) (T : Sylow 2 X) : InvDichotomyAt (T : Subgroup X) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  let e₃ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e₂.symm
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  exact invDichotomyAt_of_mulEquiv e₃
    (invDichotomyAt_of_one_sylow S (invDichotomyAt_root J f hf hKcard hfixed hJ S hS)) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
