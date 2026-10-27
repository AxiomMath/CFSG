module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_13
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitaryCoord
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace UnitaryAut

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open scoped Matrix LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem weylGL_mul_self : (hermitianWeylGL : GL (Fin 3) K) * hermitianWeylGL = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (hermitianWeylMatrix * hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) i j =
    (1 : Matrix (Fin 3) (Fin 3) K) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

omit [Finite K] [CharP K 2] in
theorem weyl_conj_torus (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) :
    hermitianWeylPSU J hJ * hermitianTorusPSU J hJ k * (hermitianWeylPSU J hJ)⁻¹ =
      hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
  have hWinv : (hermitianWeylGL : GL (Fin 3) K)⁻¹ = hermitianWeylGL :=
    inv_eq_of_mul_eq_one_right weylGL_mul_self
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).mpr hk
  have hGL : hermitianWeylGL * hermitianTorusGL J k * hermitianWeylGL =
      hermitianTorusGL J (Units.map J.conj.toMonoidHom k)⁻¹ := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (hermitianWeylMatrix * hermitianTorusMatrix J k * hermitianWeylMatrix :
      Matrix (Fin 3) (Fin 3) K) i j =
        hermitianTorusMatrix J (Units.map J.conj.toMonoidHom k)⁻¹ i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianWeylMatrix, hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three,
        Units.val_inv_eq_inv_val, map_inv₀, J.conj_involutive (k : K)]
    all_goals field_simp
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk hermitianWeylGL *
      Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) *
      (Matrix.ProjGenLinGroup.mk hermitianWeylGL)⁻¹ =
    Matrix.ProjGenLinGroup.mk (hermitianTorusGL J (Units.map J.conj.toMonoidHom k)⁻¹)
  rw [← map_inv, ← map_mul, ← map_mul, hWinv, hGL]

theorem weyl_not_mem_normalizer (J : HermitianForm 3 K) (q : ℕ) (hKcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hermitianWeylPSU J hJ ∉
      Subgroup.normalizer
        ((unitaryCoverRoot J hJ : Subgroup _) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  intro hw
  obtain ⟨z, hz⟩ := unitaryCoverFirstCoord_surjective J q hKcard hfixed hJ (Multiplicative.ofAdd 1)
  have hz1 : z.1.1 = 1 := congrArg Multiplicative.toAdd hz
  have hmem : hermitianWeylPSU J hJ * hermitianUnipotentPSU J hJ z * (hermitianWeylPSU J hJ)⁻¹ ∈
      unitaryCoverRoot J hJ :=
    (Subgroup.mem_normalizer_iff.mp hw _).mp ⟨z, rfl⟩
  obtain ⟨z', hz'⟩ := hmem
  have hWinv : (hermitianWeylGL : GL (Fin 3) K)⁻¹ = hermitianWeylGL :=
    inv_eq_of_mul_eq_one_right weylGL_mul_self
  have hPGL : Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z') =
      Matrix.ProjGenLinGroup.mk (hermitianWeylGL * hermitianUnipotentGL J z * hermitianWeylGL) := by
    have h := congrArg Subtype.val hz'
    change Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z') =
      Matrix.ProjGenLinGroup.mk hermitianWeylGL *
        Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) *
        (Matrix.ProjGenLinGroup.mk hermitianWeylGL)⁻¹ at h
    rw [h, ← map_inv, ← map_mul, ← map_mul, hWinv]
  set A : GL (Fin 3) K := hermitianWeylGL * hermitianUnipotentGL J z * hermitianWeylGL with hA
  have hc : A * (hermitianUnipotentGL J z')⁻¹ ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul, map_inv, ← hPGL, mul_inv_cancel]
  obtain ⟨c, hcs⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
  have hAeq : (A : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) c * hermitianUnipotentMatrix J z' := by
    have h1 : A = (A * (hermitianUnipotentGL J z')⁻¹) * hermitianUnipotentGL J z' := by group
    rw [h1, Matrix.GeneralLinearGroup.coe_mul, ← hcs]
    rfl
  have h21 := congrFun (congrFun hAeq 2) 1
  change (hermitianWeylMatrix * hermitianUnipotentMatrix J z * hermitianWeylMatrix :
    Matrix (Fin 3) (Fin 3) K) 2 1 = _ at h21
  simp [hermitianWeylMatrix, hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three,
    hz1] at h21

omit [Finite K] [CharP K 2] in
theorem mem_sylowCenter_root_of_fst (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {z : hermitianUnipotentCoord J}
    (hz : z.1.1 = 0) : hermitianUnipotentPSU J hJ z ∈ sylowCenter (unitaryCoverRoot J hJ) := by
  refine mem_sylowCenter.mpr ⟨⟨z, rfl⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  rw [UnitaryCoord.mul_comm_iff, hz, map_zero, mul_zero, zero_mul]

theorem mem_sylowCenter_root (J : HermitianForm 3 K) (q : ℕ) (hKcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (hq : 2 ≤ q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentPSU J hJ z ∈ sylowCenter (unitaryCoverRoot J hJ) ↔ z.1.1 = 0 := by
  refine ⟨fun hZ => ?_, mem_sylowCenter_root_of_fst J hJ⟩
  by_contra hz
  obtain ⟨u, hu⟩ : ∃ u : K, J.conj u ≠ u := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card {x : K // J.conj x = x} = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hcon)
    rw [hfixed, hKcard] at h1
    have : q * 1 < q * q := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    rw [sq] at h1
    omega
  have hcz : J.conj z.1.1 ≠ 0 := (map_ne_zero J.conj).mpr hz
  obtain ⟨w, hw⟩ := unitaryCoverFirstCoord_surjective J q hKcard hfixed hJ
    (Multiplicative.ofAdd (u / J.conj z.1.1))
  have hw1 : w.1.1 = u / J.conj z.1.1 := congrArg Multiplicative.toAdd hw
  have hcomm := (mem_sylowCenter.mp hZ).2 _ ⟨w, rfl⟩
  rw [← map_mul, ← map_mul] at hcomm
  have hwz := (UnitaryCoord.mul_comm_iff J z w).mp (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hcomm)
  apply hu
  rw [hw1, map_div₀, J.conj_involutive] at hwz
  have e1 : u / J.conj z.1.1 * J.conj z.1.1 = u := div_mul_cancel₀ u hcz
  have e2 : z.1.1 * (J.conj u / z.1.1) = J.conj u := by field_simp
  rw [e1, e2] at hwz
  exact hwz.symm

theorem exists_sylow_eq_root (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ :=
  ⟨unitaryCoverSylow J f hf hKcard hfixed hJ, unitaryCoverSylow_coe J f hf hKcard hfixed hJ⟩

theorem normalizer_and_card_sylow (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (∀ g ∈ Subgroup.normalizer ((unitaryCoverRoot J hJ : Subgroup _) :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      ∃ r ∈ unitaryCoverRoot J hJ, ∃ h ∈ unitaryCoverTorus J hJ, g = r * h) ∧
    Nat.card (Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) =
      Nat.card (unitaryCoverRoot J hJ) + 1 := by
  let q := 2 ^ f
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G := Finite.of_injective Subtype.val Subtype.coe_injective
  rcases huppert_II_10_12 J q hKcard hfixed hJ with
    ⟨hΩcard, rho, a, _hinj, _hnatural, _hUcard,
      ⟨R, D, hRle, hDle, hN, _hinf, hsup, _hcyc, _hRcard,
        _hcomm, _hcommcard, _hDcard, hreg, ⟨coord, hcoord⟩,
        hDcoord, hDsurj⟩, htwo, _hGcard, _hthree⟩
  have hmatch (z : hermitianUnipotentCoord J) :
      (coord z : G) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    have hMeq : M = hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    simpa only [hermitianUnipotentPSU_val, hMeq] using hproj
  have hrangeR : unitaryCoverRoot J hJ = R := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rw [← hmatch]
      exact (coord z).property
    · intro hx
      obtain ⟨z, hz⟩ := coord.surjective ⟨x, hx⟩
      exact ⟨z, (hmatch z).symm.trans (congrArg Subtype.val hz)⟩
  have hmatrix (k : Kˣ) (M : GL (Fin 3) K)
      (hM : (M : Matrix (Fin 3) (Fin 3) K) =
        !![(J.conj (k : K))⁻¹, 0, 0;
           0, J.conj (k : K) * (k : K)⁻¹, 0;
           0, 0, (k : K)]) : M = hermitianTorusGL J k := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [hM, hermitianTorusGL_val]
    rfl
  have hrangeD : unitaryCoverTorus J hJ = D := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨h, M, hM, hproj⟩ := hDsurj k
      have hh : (h : G) = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        simpa only [hmatrix k M hM, hermitianTorusPSU_val] using hproj
      rw [← hh]
      exact h.property
    · intro hx
      obtain ⟨k, M, hM, hproj⟩ := hDcoord ⟨x, hx⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simpa only [hmatrix k M hM, hermitianTorusPSU_val] using hproj.symm
  let : MulAction G Ω := MulAction.compHom Ω rho
  have hstab : (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho =
      MulAction.stabilizer G a := by
    ext g
    rfl
  have hRle' : R ≤ MulAction.stabilizer G a := hstab ▸ hRle
  have hN' : MulAction.stabilizer G a ≤ Subgroup.normalizer (R : Set G) := hstab ▸ hN
  have hsup' : R ⊔ D = MulAction.stabilizer G a := hsup.trans hstab
  have hRne : R ≠ ⊥ := by
    rw [← hrangeR]
    intro h
    obtain ⟨z, hz⟩ :=
      unitaryCoverFirstCoord_surjective J q hKcard hfixed hJ (Multiplicative.ofAdd 1)
    have hmem : hermitianUnipotentPSU J hJ z ∈ unitaryCoverRoot J hJ := ⟨z, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : z = 1 := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by rw [hmem, map_one])
    have h2 : z.1.1 = 1 := congrArg Multiplicative.toAdd hz
    rw [h1] at h2
    exact zero_ne_one h2
  have hreg' : ∀ b c : Ω, b ≠ a → c ≠ a → ∃! r : R, (r : G) • b = c := hreg
  have hnorm := CFSG.BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl R a hRle' hRne
    hreg' hN'
  have hDN : D ≤ Subgroup.normalizer (R : Set G) := (le_sup_right.trans hsup'.le).trans hN'
  constructor
  · intro g hg
    rw [hrangeR] at hg ⊢
    rw [hrangeD]
    rw [hnorm, ← hsup'] at hg
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left R D hDN, Set.mem_mul] at hg
    obtain ⟨r, hr, h, hh, hrh⟩ := hg
    exact ⟨r, hr, h, hh, hrh.symm⟩
  · obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
    let : MulAction.IsMultiplyPretransitive G Ω 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro b c d e hbc hde
      exact htwo b c d e hbc hde
    have : MulAction.IsPretransitive G Ω :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hindex := MulAction.index_stabilizer_of_transitive G a
    have hRcard : Nat.card (unitaryCoverRoot J hJ) = q ^ 3 :=
      (unitaryCoverRoot_nativeStructure J q hKcard hfixed hJ).1
    rw [Sylow.card_eq_index_normalizer S]
    change (Subgroup.normalizer (((S : Subgroup G)) : Set G)).index = _
    rw [hS, hrangeR, hnorm, hindex, hΩcard, ← hrangeR, hRcard]

theorem center_eq_bot (J : HermitianForm 3 K) (q : ℕ) (hq : 2 < q) (hKcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J q hq hKcard hfixed
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J)) with h | h
  · exact h
  · exfalso
    apply weyl_not_mem_normalizer J q hKcard hfixed hJ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hw : hermitianWeylPSU J hJ ∈ Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) := by
      rw [h]
      exact Subgroup.mem_top _
    have hc := Subgroup.mem_center_iff.mp hw x
    rw [← hc, mul_inv_cancel_right]

end UnitaryAut

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
