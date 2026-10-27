module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitaryCoord
public import CFSG.Models.BenderSuzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

@[expose] def UnitaryTwisted (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∃ lam : K, lam ≠ 0 ∧ ∀ z : hermitianUnipotentCoord J, ∃ z' : hermitianUnipotentCoord J,
    γ (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ z' ∧
      z'.1.1 = lam * J.conj z.1.1

theorem unitary_form (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hγγ : γ * γ = 1) (hγS : γ • S = S)
    (hγS₁ : γ • (hermitianWeylPSU J hJ • S) = hermitianWeylPSU J hJ • S) :
    γ = 1 ∨ UnitaryTwisted J hJ γ := by
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
  have hγH : ∀ k : Kˣ, ∃ k' : Kˣ, γ (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k' := by
    intro k
    have h1 := Omega.mem_normalizer_smul (α := γ) (hHN ⟨k, rfl⟩)
    have h2 := Omega.mem_normalizer_smul (α := γ) (hHN₁ ⟨k, rfl⟩)
    rw [hγS] at h1
    rw [hγS₁] at h2
    obtain ⟨k', hk'⟩ := Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2
    exact ⟨k', hk'.symm⟩
  have hRS : ∀ z, U z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := fun z => by
    rw [hS]
    exact ⟨z, rfl⟩
  have hex : ∀ z : hermitianUnipotentCoord J, ∃ z', γ (U z) = U z' := by
    intro z
    have h := InvInner.apply_mem_of_smul_eq hγS (hRS z)
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
  have hψU : ∀ z, U (ψ z) = γ (U z) := fun z => (hψf z).symm
  have hψψ : ∀ z, ψ (ψ z) = z := fun z => hU (by
    rw [hψU, hψU]
    change (γ * γ) (U z) = U z
    rw [hγγ, MulAut.one_apply])
  have hψinj : Function.Injective ψ := fun z z' h => by rw [← hψψ z, h, hψψ]
  have hψtor : ∀ k : Kˣ, ∃ k' : Kˣ,
      ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z) := by
    intro k
    obtain ⟨k', hk'⟩ := hγH k
    refine ⟨k', fun z => hU ?_⟩
    calc U (ψ (hermitianTorusAction J k z)) = γ (U (hermitianTorusAction J k z)) := hψU _
      _ = γ (hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹) := by
          rw [hconjU]
      _ = γ (hermitianTorusPSU J hJ k) * γ (U z) * (γ (hermitianTorusPSU J hJ k))⁻¹ := by
          rw [map_mul, map_mul, mulAut_apply_inv]
      _ = hermitianTorusPSU J hJ k' * U (ψ z) * (hermitianTorusPSU J hJ k')⁻¹ := by
          rw [hk', hψU]
      _ = U (hermitianTorusAction J k' (ψ z)) := hconjU k' (ψ z)
  have hψcen := UnitaryCoordAut.center_fixed J (2 ^ f) hKcard hfixed hq4 hJ ψ hψψ hψtor
  obtain ⟨lam, hNlam, hform⟩ := UnitaryCoordAut.coordAut_form J (2 ^ f) hKcard hfixed hq4 hJ ψ
    hψinj hψcen hψtor
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
    refine Omega.eq_one_of_centralizes hSE hcard hS₁ γ hγS hγS₁ fun s hs => ?_
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
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hNlam
      exact zero_ne_one hNlam
    exact ⟨lam, hlam0, fun z => ⟨ψ z, (hψU z).symm, (hconj z).1⟩⟩

theorem unitary_not_twisted_mul (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {γ₁ γ₂ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} (h₁ : UnitaryTwisted J hJ γ₁)
    (h₂ : UnitaryTwisted J hJ γ₂) : ¬ UnitaryTwisted J hJ (γ₁ * γ₂) := by
  rintro ⟨l', hl'0, h'⟩
  obtain ⟨l₁, -, hγ₁⟩ := h₁
  obtain ⟨l₂, -, hγ₂⟩ := h₂
  have hU := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hcomp : ∀ a : K, l₁ * J.conj l₂ * a = l' * J.conj a := by
    intro a
    obtain ⟨z, hz⟩ :=
      unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ (Multiplicative.ofAdd a)
    have hza : z.1.1 = a := congrArg Multiplicative.toAdd hz
    obtain ⟨z₂, hz₂, hz₂1⟩ := hγ₂ z
    obtain ⟨z₁₂, hz₁₂, hz₁₂1⟩ := hγ₁ z₂
    obtain ⟨z', hz', hz'1⟩ := h' z
    have hzz : z' = z₁₂ := hU (by rw [← hz', ← hz₁₂, ← hz₂, MulAut.mul_apply])
    rw [← hza, ← hz'1, hzz, hz₁₂1, hz₂1, map_mul, J.conj_involutive]
    ring
  have hl : l' = l₁ * J.conj l₂ := by
    have h := hcomp 1
    rw [mul_one, map_one, mul_one] at h
    exact h.symm
  obtain ⟨a, ha⟩ : ∃ a : K, J.conj a ≠ a := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card {x : K // J.conj x = x} = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hfixed, hKcard] at h1
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    nlinarith
  apply ha
  have h := hcomp a
  rw [← hl] at h
  exact (mul_left_cancel₀ hl'0 h).symm

theorem e4Inner_projectiveSpecialUnitary (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    E4Inner (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  obtain ⟨-, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  rw [← hS] at hcard
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  intro α β hα hβ hαβ
  exact exists_inner_of_commute_of_form hSE hcard hS₁ (UnitaryTwisted J hJ)
    (fun γ hγ hγS hγS₁ => unitary_form J f hf hKcard hfixed hJ S hS γ hγ hγS hγS₁)
    (fun _ _ _ _ _ _ _ _ h₁ h₂ => unitary_not_twisted_mul J f hf hKcard hfixed hJ h₁ h₂)
    α β hα hβ hαβ

theorem e4Inner_of_mulEquiv_psu3 {X : Type*} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) : E4Inner X := by
  let k := GaloisField 2 f
  let L := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP L 2 := CharP.of_ringHom_of_ne_zero (algebraMap k L) 2 (by norm_num)
  have hKcard : Nat.card L = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : L // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  exact (e4Inner_projectiveSpecialUnitary J f hf hKcard hfixed hJ).of_mulEquiv (e.trans e₂.symm)

end CFSG.ComponentClassification.RankTwoBender
