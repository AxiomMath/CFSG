module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherToolkit
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

section Model

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem exists_coordHom (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hβS : β • S = S)
    (hβS₁ : β • (hermitianWeylPSU J hJ • S) = hermitianWeylPSU J hJ • S) :
    ∃ ψ : hermitianUnipotentCoord J →* hermitianUnipotentCoord J, Function.Injective ψ ∧
      (∀ z, hermitianUnipotentPSU J hJ (ψ z) = β (hermitianUnipotentPSU J hJ z)) ∧
      ∀ k : Kˣ, ∃ k' : Kˣ,
        ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hconjU : ∀ (k : Kˣ) (z : hermitianUnipotentCoord J),
      hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹ =
        U (hermitianTorusAction J k z) := unitaryCoverTorus_conj_root J hJ
  obtain ⟨hNR, -⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  have hHN : unitaryCoverTorus J hJ ≤
      Subgroup.normalizer (((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) : Set _) := by
    rw [hS]
    exact unitaryCoverTorus_le_normalizer J hJ
  rw [← hS] at hNR
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
  have hβH : ∀ k : Kˣ, ∃ k' : Kˣ, β (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k' := by
    intro k
    have h1 := Omega.mem_normalizer_smul (α := β) (hHN ⟨k, rfl⟩)
    have h2 := Omega.mem_normalizer_smul (α := β) (hHN₁ ⟨k, rfl⟩)
    rw [hβS] at h1
    rw [hβS₁] at h2
    obtain ⟨k', hk'⟩ := Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2
    exact ⟨k', hk'.symm⟩
  have hRS : ∀ z, U z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := fun z => by
    rw [hS]
    exact ⟨z, rfl⟩
  have hex : ∀ z : hermitianUnipotentCoord J, ∃ z', β (U z) = U z' := by
    intro z
    have h := InvInner.apply_mem_of_smul_eq hβS (hRS z)
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
  have hψU : ∀ z, U (ψ z) = β (U z) := fun z => (hψf z).symm
  refine ⟨ψ, fun z z' h => hU (β.injective (by rw [← hψU, ← hψU, h])), hψU, ?_⟩
  intro k
  obtain ⟨k', hk'⟩ := hβH k
  refine ⟨k', fun z => hU ?_⟩
  calc U (ψ (hermitianTorusAction J k z)) = β (U (hermitianTorusAction J k z)) := hψU _
    _ = β (hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹) := by
        rw [hconjU]
    _ = β (hermitianTorusPSU J hJ k) * β (U z) * (β (hermitianTorusPSU J hJ k))⁻¹ := by
        rw [map_mul, map_mul, mulAut_apply_inv]
    _ = hermitianTorusPSU J hJ k' * U (ψ z) * (hermitianTorusPSU J hJ k')⁻¹ := by
        rw [hk', hψU]
    _ = U (hermitianTorusAction J k' (ψ z)) := hconjU k' (ψ z)

theorem four_le_two_pow {f : ℕ} (hf : 2 ≤ f) : 4 ≤ 2 ^ f :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem unitary_inv_fix (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hγγ : γ * γ = 1) (hγS : γ • S = S)
    (hγS₁ : γ • (hermitianWeylPSU J hJ • S) = hermitianWeylPSU J hJ • S) (hγ1 : γ ≠ 1) :
    (∀ z ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), γ z = z) ∧
      ∀ r ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), γ r = r →
        r ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  classical
  have hq4 := four_le_two_pow hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  obtain ⟨ψ, hψinj, hψU, hψtor⟩ := exists_coordHom J f hf hKcard hfixed hJ S hS γ hγS hγS₁
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hψψ : ∀ z, ψ (ψ z) = z := fun z => hU (by
    rw [hψU, hψU]
    change (γ * γ) (U z) = U z
    rw [hγγ, MulAut.one_apply])
  have hψcen := UnitaryCoordAut.center_fixed J (2 ^ f) hKcard hfixed hq4 hJ ψ hψψ hψtor
  obtain ⟨lam, -, hform⟩ :=
    UnitaryCoordAut.coordAut_form J (2 ^ f) hKcard hfixed hq4 hJ ψ hψinj hψcen hψtor
  have hmemZ : ∀ z, U z ∈ sylowCenter (unitaryCoverRoot J hJ) ↔ z.1.1 = 0 :=
    mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ
  rcases hform with hid | hconj
  ·
    exfalso
    apply hγ1
    obtain ⟨-, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
    obtain ⟨hSE, -, -, -⟩ :=
      benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
    rw [← hS] at hcard
    have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
      intro h
      apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
      rw [← hS]
      exact (Sylow.smul_eq_iff_mem_normalizer).mp h
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
  · rw [hS]
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨z, rfl⟩ := (sylowCenter_le _ hx : x ∈ unitaryCoverRoot J hJ)
      rw [← hψU, hψcen z ((hmemZ z).mp hx)]
    · rintro x ⟨z, rfl⟩ hfix
      have hz : ψ z = z := hU (by rw [hψU]; exact hfix)
      apply (hmemZ z).mpr
      have h2 := (hconj z).2
      rw [hz] at h2
      have h3 : z.1.1 * J.conj z.1.1 = 0 := by linear_combination -h2
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact (map_eq_zero J.conj).mp h4

theorem eq_one_of_untwisted (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) {n : ℕ} (hβn : β ^ 2 ^ n = 1)
    (hβS : β • S = S) (hβS₁ : β • (hermitianWeylPSU J hJ • S) = hermitianWeylPSU J hJ • S)
    (lam : K) (hβ : ∀ z, ∃ z', β (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ z' ∧
      z'.1.1 = lam * z.1.1 ∧ z'.1.2 = z.1.2) : β = 1 := by
  classical
  have hq4 := four_le_two_pow hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hiter : ∀ (m : ℕ) (z : hermitianUnipotentCoord J), ∃ z',
      (β ^ m) (U z) = U z' ∧ z'.1.1 = lam ^ m * z.1.1 ∧ z'.1.2 = z.1.2 := by
    intro m
    induction m with
    | zero => exact fun z => ⟨z, by simp⟩
    | succ m ih =>
      intro z
      obtain ⟨z', hz', hz'1, hz'2⟩ := ih z
      obtain ⟨z'', hz'', hz''1, hz''2⟩ := hβ z'
      refine ⟨z'', ?_, ?_, ?_⟩
      · rw [pow_succ', MulAut.mul_apply, hz', hz'']
      · rw [hz''1, hz'1, pow_succ]
        ring
      · rw [hz''2, hz'2]
  obtain ⟨z₁, hz₁⟩ :=
    unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ (Multiplicative.ofAdd 1)
  have hz₁1 : z₁.1.1 = 1 := congrArg Multiplicative.toAdd hz₁
  obtain ⟨z', hz', hz'1, -⟩ := hiter (2 ^ n) z₁
  rw [hβn, MulAut.one_apply] at hz'
  have hzz : z₁ = z' := hU hz'
  rw [← hzz, hz₁1, mul_one] at hz'1
  have hlam_pow : lam ^ (2 ^ n) = 1 := hz'1.symm
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hlam_pow
    exact zero_ne_one hlam_pow
  have hlam_card : lam ^ (Nat.card K - 1) = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have := FiniteField.pow_card_sub_one_eq_one lam hlam0
    rwa [← Nat.card_eq_fintype_card] at this
  have hcop : Nat.Coprime (2 ^ n) (Nat.card K - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left, hKcard]
    have hev : Even (2 ^ f) := (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
    have hpos : 0 < (2 ^ f) ^ 2 := by positivity
    exact Nat.Even.sub_odd hpos (hev.pow_of_ne_zero (by decide)) odd_one
  have hlam1 : lam = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hlam_pow, hlam_card⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  obtain ⟨-, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  rw [← hS] at hcard
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  refine Omega.eq_one_of_centralizes hSE hcard hS₁ β hβS hβS₁ fun s hs => ?_
  rw [hS] at hs
  obtain ⟨z, rfl⟩ := hs
  obtain ⟨z', hz', hz'1, hz'2⟩ := hβ z
  rw [hz']
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rw [hz'1, hlam1, one_mul]
  · exact hz'2

theorem exists_twisted_of_outer (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (P : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hP : IsPGroup 2 P)
    (hPS : ∀ β ∈ P, β • S = S)
    (hPZ : ∀ β ∈ P, ∀ z ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      β z = z)
    (hinn : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), MulAut.conj s ∈ P)
    {α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} (hα : α ∈ P)
    (hout : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), α ≠ MulAut.conj s) :
    ∃ r ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), ∃ lam : K,
      (MulAut.conj r)⁻¹ * α ∈ P ∧
      ((MulAut.conj r)⁻¹ * α) • (hermitianWeylPSU J hJ • S) = hermitianWeylPSU J hJ • S ∧
      ∀ z, ∃ z', ((MulAut.conj r)⁻¹ * α) (hermitianUnipotentPSU J hJ z) =
        hermitianUnipotentPSU J hJ z' ∧ z'.1.1 = lam * J.conj z.1.1 := by
  classical
  have hq4 := four_le_two_pow hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨-, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  rw [← hS] at hcard
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hmemZ : ∀ z, U z ∈ sylowCenter (unitaryCoverRoot J hJ) ↔ z.1.1 = 0 :=
    mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ
  obtain ⟨r, hr, hrS₁⟩ := Omega.exists_conj_adjust hSE hcard hS₁ α (hPS α hα)
  set α' := (MulAut.conj r)⁻¹ * α with hα'
  have hα'P : α' ∈ P := P.mul_mem (P.inv_mem (hinn r hr)) hα
  have hα'S : α' • S = S := hPS α' hα'P
  obtain ⟨ψ, hψinj, hψU, hψtor⟩ := exists_coordHom J f hf hKcard hfixed hJ S hS α' hα'S hrS₁
  have hψcen : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z := fun z hz0 => hU (by
    rw [hψU]
    exact hPZ α' hα'P (U z) (by rw [hS]; exact (hmemZ z).mpr hz0))
  obtain ⟨lam, -, hform⟩ :=
    UnitaryCoordAut.coordAut_form J (2 ^ f) hKcard hfixed hq4 hJ ψ hψinj hψcen hψtor
  rcases hform with hid | hconj
  · exfalso
    obtain ⟨n, hn⟩ := hP ⟨α', hα'P⟩
    have hn' : α' ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have h1 := eq_one_of_untwisted J f hf hKcard hfixed hJ S hS α' hn' hα'S hrS₁ lam
      (fun z => ⟨ψ z, (hψU z).symm, (hid z).1, (hid z).2⟩)
    apply hout r hr
    rw [show α = MulAut.conj r * α' by rw [hα', mul_inv_cancel_left], h1, mul_one]
  · exact ⟨r, hr, lam, hα'P, hrS₁, fun z => ⟨ψ z, (hψU z).symm, (hconj z).1⟩⟩

theorem unitary_outer_pair (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (P : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hP : IsPGroup 2 P)
    (hPS : ∀ β ∈ P, β • S = S)
    (hPZ : ∀ β ∈ P, ∀ z ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      β z = z)
    (hinn : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), MulAut.conj s ∈ P)
    {α₁ α₂ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} (h₁ : α₁ ∈ P) (h₂ : α₂ ∈ P)
    (hout₁ : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), α₁ ≠ MulAut.conj s)
    (hout₂ : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), α₂ ≠ MulAut.conj s) :
    ∃ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), α₁ * α₂ = MulAut.conj s := by
  classical
  have hq4 := four_le_two_pow hf
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hmemZ : ∀ z, U z ∈ sylowCenter (unitaryCoverRoot J hJ) ↔ z.1.1 = 0 :=
    mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ
  obtain ⟨r₁, hr₁, l₁, hα₁P, hα₁S₁, hα₁⟩ :=
    exists_twisted_of_outer J f hf hKcard hfixed hJ S hS P hP hPS hPZ hinn h₁ hout₁
  obtain ⟨r₂, hr₂, l₂, hα₂P, hα₂S₁, hα₂⟩ :=
    exists_twisted_of_outer J f hf hKcard hfixed hJ S hS P hP hPS hPZ hinn h₂ hout₂
  set α'₁ := (MulAut.conj r₁)⁻¹ * α₁ with hα'₁
  set α'₂ := (MulAut.conj r₂)⁻¹ * α₂ with hα'₂
  set β := α'₁ * α'₂ with hβdef
  have hβP : β ∈ P := P.mul_mem hα₁P hα₂P
  have hβS : β • S = S := hPS β hβP
  have hβS₁ : β • (hermitianWeylPSU J hJ • S) = hermitianWeylPSU J hJ • S := by
    rw [hβdef, mul_smul, hα₂S₁, hα₁S₁]
  obtain ⟨ψ, hψinj, hψU, hψtor⟩ := exists_coordHom J f hf hKcard hfixed hJ S hS β hβS hβS₁
  have hψcen : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z := fun z hz0 => hU (by
    rw [hψU]
    exact hPZ β hβP (U z) (by rw [hS]; exact (hmemZ z).mpr hz0))
  have hfst : ∀ z, (ψ z).1.1 = l₁ * J.conj l₂ * z.1.1 := by
    intro z
    obtain ⟨z₂, hz₂, hz₂1⟩ := hα₂ z
    obtain ⟨z₁₂, hz₁₂, hz₁₂1⟩ := hα₁ z₂
    have hzz : ψ z = z₁₂ := hU (by rw [hψU, hβdef, MulAut.mul_apply, hz₂, hz₁₂])
    rw [hzz, hz₁₂1, hz₂1, map_mul, J.conj_involutive]
    ring
  obtain ⟨lam, hNlam, hform⟩ :=
    UnitaryCoordAut.coordAut_form J (2 ^ f) hKcard hfixed hq4 hJ ψ hψinj hψcen hψtor
  have hβ1 : β = 1 := by
    rcases hform with hid | hconj
    · obtain ⟨n, hn⟩ := hP ⟨β, hβP⟩
      have hn' : β ^ 2 ^ n = 1 := congrArg Subtype.val hn
      exact eq_one_of_untwisted J f hf hKcard hfixed hJ S hS β hn' hβS hβS₁ lam
        (fun z => ⟨ψ z, (hψU z).symm, (hid z).1, (hid z).2⟩)
    · exfalso
      have hcomp : ∀ a : K, l₁ * J.conj l₂ * a = lam * J.conj a := by
        intro a
        obtain ⟨z, hz⟩ :=
          unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ (Multiplicative.ofAdd a)
        have hza : z.1.1 = a := congrArg Multiplicative.toAdd hz
        rw [← hza, ← hfst z, (hconj z).1]
      have hl : lam = l₁ * J.conj l₂ := by
        have h := hcomp 1
        rw [mul_one, map_one, mul_one] at h
        exact h.symm
      have hl0 : lam ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hNlam
        exact zero_ne_one hNlam
      obtain ⟨a, ha⟩ : ∃ a : K, J.conj a ≠ a := by
        by_contra hall
        push Not at hall
        have h1 : Nat.card {x : K // J.conj x = x} = Nat.card K :=
          Nat.card_congr (Equiv.subtypeUnivEquiv hall)
        rw [hfixed, hKcard] at h1
        nlinarith
      apply ha
      have h := hcomp a
      rw [← hl] at h
      exact (mul_left_cancel₀ hl0 h).symm
  have hconjφ : ∀ (φ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) x,
      φ * MulAut.conj x = MulAut.conj (φ x) * φ := by
    intro φ x
    ext g
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, mulAut_apply_inv]
  have hmem : α'₁ r₂ ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    InvInner.apply_mem_of_smul_eq (hPS α'₁ hα₁P) hr₂
  refine ⟨r₁ * α'₁ r₂, mul_mem hr₁ hmem, ?_⟩
  have e₁ : α₁ = MulAut.conj r₁ * α'₁ := by rw [hα'₁, mul_inv_cancel_left]
  have e₂ : α₂ = MulAut.conj r₂ * α'₂ := by rw [hα'₂, mul_inv_cancel_left]
  calc α₁ * α₂ = MulAut.conj r₁ * (α'₁ * MulAut.conj r₂) * α'₂ := by rw [e₁, e₂]; group
    _ = MulAut.conj r₁ * MulAut.conj (α'₁ r₂) * β := by rw [hconjφ, hβdef]; group
    _ = MulAut.conj (r₁ * α'₁ r₂) := by rw [hβ1, mul_one, map_mul]

theorem unitary_inv_fix_root (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ)
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (hγγ : γ * γ = 1)
    (hγ : ¬ ∃ y, γ = MulAut.conj y)
    (hγS : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      γ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) :
    (∀ z ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), γ z = z) ∧
      ∀ r ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), γ r = r →
        r ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨-, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  rw [← hS] at hcard
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  rcases invDichotomyAt_root J f hf hKcard hfixed hJ S hS γ hγγ hγS with hin | ⟨x, hxN, hxS⟩
  · exact absurd hin hγ
  have hγS' : γ • S = S := Omega.smul_eq_of_mapsTo hγS
  have hγS₀ : γ • (x • S) = x • S := by
    apply Omega.smul_eq_of_mapsTo
    intro y hy
    show γ y ∈ ((x • S : Sylow 2 _) : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    rw [Omega.mem_conj_smul_iff] at hy ⊢
    have h1 := hxS _ hy
    have h2 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [h2] at h1
    exact h1
  have hS₀ : x • S ≠ S := fun h => hxN (Sylow.smul_eq_iff_mem_normalizer.mp h)
  obtain ⟨r, hr, hrS⟩ := Omega.exists_smul_eq hSE hcard hS₀ hS₁
  set γ' := MulAut.conj r * γ * (MulAut.conj r)⁻¹ with hγ'def
  have hrS' : MulAut.conj r • S = S := Omega.conj_smul_self hr
  have hγ'S : γ' • S = S := by
    rw [hγ'def, mul_smul, mul_smul, inv_smul_eq_iff.mpr hrS'.symm, hγS', hrS']
  have hγ'S₁ : γ' • (hermitianWeylPSU J hJ • S) = hermitianWeylPSU J hJ • S := by
    rw [← hrS, Sylow.smul_def, hγ'def, mul_smul, mul_smul, inv_smul_smul, hγS₀]
  have hγ'γ' : γ' * γ' = 1 := by
    rw [hγ'def, show MulAut.conj r * γ * (MulAut.conj r)⁻¹ * (MulAut.conj r * γ *
      (MulAut.conj r)⁻¹) = MulAut.conj r * (γ * γ) * (MulAut.conj r)⁻¹ by group, hγγ, mul_one,
      mul_inv_cancel]
  have hγ'1 : γ' ≠ 1 := by
    intro h
    apply hγ
    refine ⟨1, ?_⟩
    have h2 : γ = (MulAut.conj r)⁻¹ * γ' * MulAut.conj r := by rw [hγ'def]; group
    rw [h2, h, mul_one, inv_mul_cancel, map_one]
  obtain ⟨hZ, hfix⟩ := unitary_inv_fix J f hf hKcard hfixed hJ S hS γ' hγ'γ' hγ'S hγ'S₁ hγ'1
  have hγ'app : ∀ y, γ' y = r * γ (r⁻¹ * y * r) * r⁻¹ := fun y => by
    rw [hγ'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
      MulAut.conj_apply]
  have hrZ : ∀ z ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      r⁻¹ * z * r = z := fun z hz => by
    rw [mul_assoc, ← (mem_sylowCenter.mp hz).2 r hr, inv_mul_cancel_left]
  refine ⟨fun z hz => ?_, fun y hy hyfix => ?_⟩
  · have h1 := hZ z hz
    rw [hγ'app, hrZ z hz] at h1
    calc γ z = r⁻¹ * (r * γ z * r⁻¹) * r := by group
      _ = r⁻¹ * z * r := by rw [h1]
      _ = z := hrZ z hz
  · have hy' : r * y * r⁻¹ ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      mul_mem (mul_mem hr hy) (inv_mem hr)
    have h1 := hfix _ hy' (by
      rw [hγ'app, show r⁻¹ * (r * y * r⁻¹) * r = y by group, hyfix])
    have h2 := mem_sylowCenter.mp h1
    refine mem_sylowCenter.mpr ⟨hy, fun t ht => ?_⟩
    have h3 := h2.2 (r * t * r⁻¹) (mul_mem (mul_mem hr ht) (inv_mem hr))
    calc t * y = r⁻¹ * ((r * t * r⁻¹) * (r * y * r⁻¹)) * r := by group
      _ = r⁻¹ * ((r * y * r⁻¹) * (r * t * r⁻¹)) * r := by rw [h3]
      _ = y * t := by group

theorem sq_mem_sylowCenter_root (J : HermitianForm 3 K) (q : ℕ) (hKcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (hq : 2 ≤ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentPSU J hJ z ^ 2 ∈ sylowCenter (unitaryCoverRoot J hJ) := by
  rw [sq, ← map_mul, mem_sylowCenter_root J q hKcard hfixed hq hJ]
  change z.1.1 + z.1.1 = 0
  exact CharTwo.add_self_eq_zero _

end Model

section Transport

variable {X : Type*} [Group X] [Finite X] {f : ℕ}

theorem exists_mulEquiv_root (hf : 2 ≤ f) (e : X ≃* PSU3 2 f) (R : Sylow 2 X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (J : HermitianForm 3 K)
      (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]),
      Nat.card K = (2 ^ f) ^ 2 ∧ Nat.card {x : K // J.conj x = x} = 2 ^ f ∧
      ∃ (φ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)),
        (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ ∧
          (R : Subgroup X).map φ.toMonoidHom = S := by
  obtain ⟨K, _, _, _, J, hJ, hKcard, hfixed, ⟨e'⟩⟩ :=
    Asc76X.exists_mulEquiv_hermitian_of_mulEquiv_psu3 hf e
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  let R' : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) R' S
  refine ⟨K, inferInstance, inferInstance, inferInstance, J, hJ, hKcard, hfixed,
    e'.trans (MulAut.conj g), S, hS, ?_⟩
  ext x
  rw [← hg, Omega.mem_conj_smul_iff]
  change x ∈ (R : Subgroup X).map (e'.trans (MulAut.conj g)).toMonoidHom ↔
    g⁻¹ * x * g ∈ (R : Subgroup X).map e'.toMonoidHom
  rw [AschbacherToolkit.Bender.AutTransport.mem_map_iff',
    AschbacherToolkit.Bender.AutTransport.mem_map_iff']
  rfl

theorem inv_fix_of_not_inner_psu3 (hf : 2 ≤ f) (e : X ≃* PSU3 2 f) (α : MulAut X)
    (hαα : α * α = 1) (hα : ¬ ∃ y, α = MulAut.conj y) (R : Sylow 2 X)
    (hαR : ∀ r ∈ (R : Subgroup X), α r ∈ (R : Subgroup X)) :
    (∀ z ∈ sylowCenter (R : Subgroup X), α z = z) ∧
      ∀ r ∈ (R : Subgroup X), α r = r → r ∈ sylowCenter (R : Subgroup X) := by
  obtain ⟨K, _, _, _, J, hJ, hKcard, hfixed, φ, S, hS, hRS⟩ := exists_mulEquiv_root hf e R
  set γ := MulAut.congr φ α with hγdef
  have hγapp : ∀ x, γ (φ x) = φ (α x) := AutTransport.congr_apply' φ α
  have hγγ : γ * γ = 1 := by rw [hγdef, ← map_mul, hαα, map_one]
  have hγ : ¬ ∃ y, γ = MulAut.conj y := by
    rintro ⟨y, hy⟩
    apply hα
    refine ⟨φ.symm y, (MulAut.congr φ).injective ?_⟩
    rw [AutTransport.congr_conj, MulEquiv.apply_symm_apply]
    exact hy
  have hmemS : ∀ x, φ x ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ (R : Subgroup X) := fun x => by
    rw [← hRS]
    exact AutTransport.mem_map_iff φ
  have hmemZ : ∀ x, φ x ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ sylowCenter (R : Subgroup X) := fun x => by
    rw [← hRS]
    exact AutTransport.mem_sylowCenter_map φ
  have hγS : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      γ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro s hs
    obtain ⟨x, rfl⟩ := φ.surjective s
    rw [hγapp, hmemS]
    exact hαR x ((hmemS x).mp hs)
  obtain ⟨hZ, hfix⟩ := unitary_inv_fix_root J f hf hKcard hfixed hJ S hS γ hγγ hγ hγS
  refine ⟨fun z hz => φ.injective ?_, fun r hr hrfix => ?_⟩
  · rw [← hγapp]
    exact hZ _ ((hmemZ z).mpr hz)
  · exact (hmemZ r).mp (hfix _ ((hmemS r).mpr hr) (by rw [hγapp, hrfix]))

theorem outer_pair_psu3 (hf : 2 ≤ f) (e : X ≃* PSU3 2 f) (R : Sylow 2 X)
    (P : Subgroup (MulAut X)) (hP : IsPGroup 2 P)
    (hPR : ∀ β ∈ P, ∀ r ∈ (R : Subgroup X), β r ∈ (R : Subgroup X))
    (hPZ : ∀ β ∈ P, ∀ z ∈ sylowCenter (R : Subgroup X), β z = z)
    (hinn : ∀ r ∈ (R : Subgroup X), MulAut.conj r ∈ P)
    {α₁ α₂ : MulAut X} (h₁ : α₁ ∈ P) (h₂ : α₂ ∈ P)
    (hout₁ : ∀ r ∈ (R : Subgroup X), α₁ ≠ MulAut.conj r)
    (hout₂ : ∀ r ∈ (R : Subgroup X), α₂ ≠ MulAut.conj r) :
    ∃ r ∈ (R : Subgroup X), α₁ * α₂ = MulAut.conj r := by
  obtain ⟨K, _, _, _, J, hJ, hKcard, hfixed, φ, S, hS, hRS⟩ := exists_mulEquiv_root hf e R
  set Φ := MulAut.congr φ with hΦ
  have hΦapp : ∀ β x, Φ β (φ x) = φ (β x) := fun β x => AutTransport.congr_apply' φ β x
  have hmemS : ∀ x, φ x ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ (R : Subgroup X) := fun x => by
    rw [← hRS]
    exact AutTransport.mem_map_iff φ
  have hmemZ : ∀ x, φ x ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ sylowCenter (R : Subgroup X) := fun x => by
    rw [← hRS]
    exact AutTransport.mem_sylowCenter_map φ
  set P' := P.map Φ.toMonoidHom with hP'
  have hP'2 : IsPGroup 2 P' := hP.map _
  have hP'S : ∀ β ∈ P', β • S = S := by
    rintro _ ⟨β, hβ, rfl⟩
    apply Omega.smul_eq_of_mapsTo
    intro s hs
    obtain ⟨x, rfl⟩ := φ.surjective s
    change Φ β (φ x) ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    rw [hΦapp, hmemS]
    exact hPR β hβ x ((hmemS x).mp hs)
  have hP'Z : ∀ β ∈ P', ∀ z ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      β z = z := by
    rintro _ ⟨β, hβ, rfl⟩ z hz
    obtain ⟨x, rfl⟩ := φ.surjective z
    change Φ β (φ x) = φ x
    rw [hΦapp, hPZ β hβ x ((hmemZ x).mp hz)]
  have hinn' : ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      MulAut.conj s ∈ P' := by
    intro s hs
    obtain ⟨x, rfl⟩ := φ.surjective s
    exact ⟨MulAut.conj x, hinn x ((hmemS x).mp hs), AutTransport.congr_conj φ x⟩
  have hout' : ∀ {α : MulAut X}, (∀ r ∈ (R : Subgroup X), α ≠ MulAut.conj r) →
      ∀ s ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)), Φ α ≠ MulAut.conj s := by
    intro α hα s hs h
    obtain ⟨x, rfl⟩ := φ.surjective s
    apply hα x ((hmemS x).mp hs)
    apply Φ.injective
    rw [h, AutTransport.congr_conj]
  obtain ⟨s, hs, hs'⟩ := unitary_outer_pair J f hf hKcard hfixed hJ S hS P' hP'2 hP'S hP'Z hinn'
    ⟨α₁, h₁, rfl⟩ ⟨α₂, h₂, rfl⟩ (hout' hout₁) (hout' hout₂)
  obtain ⟨x, rfl⟩ := φ.surjective s
  refine ⟨x, (hmemS x).mp hs, Φ.injective ?_⟩
  show MulAut.congr φ (α₁ * α₂) = MulAut.congr φ (MulAut.conj x)
  rw [map_mul, AutTransport.congr_conj]
  exact hs'

theorem card_commutator_congr {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) :
    Nat.card (commutator A) = Nat.card (commutator B) := by
  rw [← card_map_of_injective (K := commutator A) (f := ψ.toMonoidHom) ψ.injective]
  congr 1
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective]

theorem sylow_psu3 (hf : 2 ≤ f) (e : X ≃* PSU3 2 f) (R : Sylow 2 X) :
    Nat.card (R : Subgroup X) = (2 ^ f) ^ 3 ∧
      Nat.card (sylowCenter (R : Subgroup X)) = 2 ^ f ∧
      (∀ x ∈ (R : Subgroup X), x ^ 2 = 1 → x ∈ sylowCenter (R : Subgroup X)) ∧
      (∀ x ∈ (R : Subgroup X), x ^ 2 ∈ sylowCenter (R : Subgroup X)) ∧
      Nat.card (commutator (R : Subgroup X)) = 2 ^ f := by
  have hB := Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e
  obtain ⟨-, -, hZcard, hRcard⟩ := benderBorel_sylowCenter hB R
  have hq4 := four_le_two_pow hf
  obtain ⟨K, _, _, _, J, hJ, hKcard, hfixed, φ, S, hS, hRS⟩ := exists_mulEquiv_root hf e R
  have hmemZ : ∀ x, φ x ∈ sylowCenter (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      x ∈ sylowCenter (R : Subgroup X) := fun x => by
    rw [← hRS]
    exact AutTransport.mem_sylowCenter_map φ
  refine ⟨hRcard, hZcard, fun x hx hx2 => ⟨hx,
    Asc76X.mem_centralizer_of_fusionBenderBorel hB (by omega) R hx hx2⟩, fun x hx => ?_, ?_⟩
  · have hφx : φ x ∈ unitaryCoverRoot J hJ := by
      rw [← hS, ← hRS]
      exact (AutTransport.mem_map_iff φ).mpr hx
    obtain ⟨z, hz⟩ := hφx
    apply (hmemZ (x ^ 2)).mp
    rw [map_pow, hS, ← hz]
    exact sq_mem_sylowCenter_root J (2 ^ f) hKcard hfixed (by omega) hJ z
  · have hroot := (unitaryCoverRoot_nativeStructure J (2 ^ f) hKcard hfixed hJ).2.2
    rw [← hroot, card_commutator_congr (((MulEquiv.subgroupMap φ (R : Subgroup X)).trans
      (MulEquiv.subgroupCongr hRS)).trans (MulEquiv.subgroupCongr hS))]

end Transport

end CFSG.ComponentClassification.GMS78
