module

public import CFSG.LocalAnalysis.SectionRank.CyclicQuotientRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterFix
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructureTorus

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

@[expose]
def psuConjHom : J.unitarySubgroup →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun A := psuAut J (MulAut.conj (A : GL (Fin 3) K))
    (map_conj_unitary (A := (A : GL (Fin 3) K)) J A.2)
  map_one' := by
    simpa only [Subgroup.coe_one, map_one] using
      psuAut_one J (Subgroup.map_id J.specialSubgroup)
  map_mul' A B := by
    have h12 : J.specialSubgroup.map
        (MulAut.conj (A : GL (Fin 3) K) * MulAut.conj (B : GL (Fin 3) K)).toMonoidHom =
        J.specialSubgroup := by
      simpa only [Subgroup.coe_mul, map_mul] using
        map_conj_unitary (A := ((A * B : J.unitarySubgroup) : GL (Fin 3) K)) J (A * B).2
    simpa only [Subgroup.coe_mul, map_mul] using
      psuAut_mul J (MulAut.conj (A : GL (Fin 3) K)) (MulAut.conj (B : GL (Fin 3) K))
        (map_conj_unitary (A := (A : GL (Fin 3) K)) J A.2)
        (map_conj_unitary (A := (B : GL (Fin 3) K)) J B.2) h12

theorem psuConjHom_apply (A : J.unitarySubgroup) :
    psuConjHom J A = psuAut J (MulAut.conj (A : GL (Fin 3) K))
      (map_conj_unitary (A := (A : GL (Fin 3) K)) J A.2) := rfl

theorem coe_psuConjHom_psuMk (A : J.unitarySubgroup) (g : J.specialSubgroup) :
    ((psuConjHom J A (psuMk J g) : ProjectiveSpecialUnitaryMatrixGroup J) :
        Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk ((A : GL (Fin 3) K) * (g : GL (Fin 3) K)
        * (A : GL (Fin 3) K)⁻¹) := by
  have hx : psuMk J g = (⟨Matrix.ProjGenLinGroup.mk (g : GL (Fin 3) K),
      Subgroup.mem_map_of_mem _ g.2⟩ : ProjectiveSpecialUnitaryMatrixGroup J) := rfl
  rw [hx, psuConjHom_apply]
  simpa [MulAut.conj_apply] using coe_psuAut_mk J (MulAut.conj (A : GL (Fin 3) K))
    (map_conj_unitary (A := (A : GL (Fin 3) K)) J A.2) g.2

theorem ringAut_conj_comm (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (σ : K ≃+* K) (x : K) :
    σ (J.conj x) = J.conj (σ x) := by
  rw [CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (p ^ f) hK hfix x,
    map_pow, ← CFSG.BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J (p ^ f) hK hfix
      (σ x)]

theorem map_glAut_special (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)
    (σ : K ≃+* K) :
    J.specialSubgroup.map (glAut σ : MulAut (GL (Fin 3) K)).toMonoidHom = J.specialSubgroup := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact glAut_mem_specialSubgroup hJ (ringAut_conj_comm J hK hfix σ) hg
  · rw [Subgroup.card_map_of_injective (f := (glAut σ).toMonoidHom) (glAut σ).injective]

@[expose]
def psuFieldHom (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) :
    (K ≃+* K) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun σ := psuAut J (glAut σ) (map_glAut_special J hJ hK hfix σ)
  map_one' := by
    simpa only [map_one] using psuAut_one J (Subgroup.map_id J.specialSubgroup)
  map_mul' σ τ := by
    simpa only [map_mul] using
      psuAut_mul J (glAut σ) (glAut τ) (map_glAut_special J hJ hK hfix σ)
        (map_glAut_special J hJ hK hfix τ) _

theorem psuFieldHom_apply (σ : K ≃+* K) :
    psuFieldHom J hJ hK hfix σ =
      psuAut J (glAut σ) (map_glAut_special J hJ hK hfix σ) := rfl

theorem glAut_mem_unitary (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)
    (σ : K ≃+* K) {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup) :
    glAut σ A ∈ J.unitarySubgroup := by
  have hJσ : J.form.map σ = J.form := by
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hT : J.conjTranspose ((A : Matrix (Fin 3) (Fin 3) K).map σ) =
      (J.conjTranspose (A : Matrix (Fin 3) (Fin 3) K)).map σ := by
    ext i j
    simp [HermitianForm.conjTranspose, ringAut_conj_comm J hK hfix σ]
  rw [HermitianForm.mem_unitarySubgroup_iff] at hA ⊢
  rw [coe_glAut, hT, ← hJσ, ← map_mul_ringEquiv, ← map_mul_ringEquiv, hJσ, hA, hJσ]

theorem coe_psuFieldHom_psuMk (σ : K ≃+* K) (g : J.specialSubgroup) :
    ((psuFieldHom J hJ hK hfix σ (psuMk J g) : ProjectiveSpecialUnitaryMatrixGroup J) :
        Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk ((glAut σ) (g : GL (Fin 3) K)) := by
  rw [psuFieldHom_apply]
  exact coe_psuAut_mk J (glAut σ) (map_glAut_special J hJ hK hfix σ) g.2

variable (hq : 2 < p ^ f)

theorem exists_eq_psuConj_mul_psuField (hq : 2 < p ^ f)
    (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ (A : J.unitarySubgroup) (σ : K ≃+* K),
      β = psuConjHom J A * psuFieldHom J hJ hK hfix σ := by
  obtain ⟨σ, A, hA, hβ⟩ :=
    exists_isometry_psu_of_card Fact.out hq hK hfix hJ β
  refine ⟨⟨A, hA⟩, σ, ?_⟩
  refine mulAut_ext_mk J fun g hg => ?_
  obtain ⟨hg', hβg⟩ := hβ ⟨g, hg⟩
  have hx : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
      ProjectiveSpecialUnitaryMatrixGroup J) = psuMk J ⟨g, hg⟩ := rfl
  rw [hx, hβg, MulAut.mul_apply]
  have hfield : psuFieldHom J hJ hK hfix σ (psuMk J ⟨g, hg⟩) =
      psuMk J ⟨glAut σ g, glAut_mem_specialSubgroup hJ
        (ringAut_conj_comm J hK hfix σ) hg⟩ :=
    Subtype.ext (coe_psuFieldHom_psuMk J hJ hK hfix σ ⟨g, hg⟩)
  rw [hfield, coe_psuConjHom_psuMk, coe_psuMk]

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

theorem pgl_conj_smul (A u : GL (Fin 3) K) (x : ℙ K (Fin 3 → K)) :
    (Matrix.ProjGenLinGroup.mk (A * u * A⁻¹) : Matrix.ProjGenLinGroup (Fin 3) K) •
        ((Matrix.ProjGenLinGroup.mk A) • x) =
      (Matrix.ProjGenLinGroup.mk A) • ((Matrix.ProjGenLinGroup.mk u) • x) := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.PGL.mk_smul_mk, Projectivization.PGL.mk_smul_mk,
      Projectivization.PGL.mk_smul_mk, Projectivization.PGL.mk_smul_mk]
    congr 1
    change (((A * u * A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *ᵥ
        (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    have h : A * u * A⁻¹ * A = A * u := by group
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using
      congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h

theorem smul_mem_isotropicSet_unitary (A : J.unitarySubgroup) {x : ℙ K (Fin 3 → K)}
    (hx : x ∈ isotropicSet J) :
    (Matrix.ProjGenLinGroup.mk (A : GL (Fin 3) K) • x) ∈ isotropicSet J := by
  obtain ⟨v, hv, rfl, hiso⟩ := hx
  refine ⟨(A : GL (Fin 3) K) *ᵥ v, (smul_ne_zero_iff_ne A).2 hv, ?_, ?_⟩
  · rw [Projectivization.PGL.mk_smul_mk]
    rfl
  · rw [selfPairing_mulVec J A.2 v]
    exact hiso

@[expose]
def guSmul (A : J.unitarySubgroup) (x : IsoPoint J) : IsoPoint J :=
  ⟨Matrix.ProjGenLinGroup.mk (A : GL (Fin 3) K) • (x : ℙ K (Fin 3 → K)),
    smul_mem_isotropicSet_unitary J A x.2⟩

@[simp] theorem coe_guSmul (A : J.unitarySubgroup) (x : IsoPoint J) :
    ((guSmul J A x : IsoPoint J) : ℙ K (Fin 3 → K)) =
      Matrix.ProjGenLinGroup.mk (A : GL (Fin 3) K) • (x : ℙ K (Fin 3 → K)) := rfl

theorem root_eq_psuMk (z : Coord J) :
    root J hJ z = psuMk J (hermitianUnipotentSU J hJ z) := rfl

theorem coe_root_eq_mk (z : Coord J) :
    ((root J hJ z : ProjectiveSpecialUnitaryMatrixGroup J) :
        Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) := rfl

theorem guSmul_conj_root (A : J.unitarySubgroup) (z : Coord J) (x : IsoPoint J) :
    (psuConjHom J A (root J hJ z)) • guSmul J A x = guSmul J A (root J hJ z • x) := by
  apply Subtype.ext
  rw [coe_smul, coe_guSmul, coe_guSmul]
  rw [root_eq_psuMk J hJ z]
  rw [show ((psuConjHom J A (psuMk J (hermitianUnipotentSU J hJ z)) :
      ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk ((A : GL (Fin 3) K) * (hermitianUnipotentGL J z)
        * (A : GL (Fin 3) K)⁻¹) from coe_psuConjHom_psuMk J A (hermitianUnipotentSU J hJ z)]
  rw [coe_smul]
  rw [show ((psuMk J (hermitianUnipotentSU J hJ z) :
      ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) =
      Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) from
    coe_psuMk (hermitianUnipotentSU J hJ z)]
  exact pgl_conj_smul (A : GL (Fin 3) K) (hermitianUnipotentGL J z)
    (x : ℙ K (Fin 3 → K))

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

theorem root_fixed_eq_pinf {r : rootGroup J hJ} (hr : r ≠ 1) {x : IsoPoint J}
    (hx : (r : ProjectiveSpecialUnitaryMatrixGroup J) • x = x) : x = pinf J hJ := by
  by_contra hxne
  obtain ⟨r₀, _, huniq⟩ := rootGroup_regular J hJ x x hxne hxne
  have h1 : (1 : rootGroup J hJ) • x = x := one_smul _ _
  have h2 : r = r₀ := huniq r hx
  have h3 : (1 : rootGroup J hJ) = r₀ := huniq 1 h1
  exact hr (h2.trans h3.symm)

variable (hq : 1 < p ^ f)

theorem guSmul_pinf_of_stabilizes_rootGroup (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hq : 1 < p ^ f)
    (A : J.unitarySubgroup)
    (hAR : ∀ z : Coord J, psuConjHom J A (root J hJ z) ∈ rootGroup J hJ) :
    guSmul J A (pinf J hJ) = pinf J hJ := by
  have hcard : 1 < Nat.card (rootGroup J hJ) := by
    rw [card_rootGroup J hJ (p ^ f) hK hfix]
    have h2 : 2 ≤ p ^ f := by omega
    nlinarith [pow_pos (by omega : 0 < p ^ f) 3]
  have hne : rootGroup J hJ ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot (rootGroup J hJ)).mp hcard
  obtain ⟨⟨r, hrR⟩, hrne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  set z : Coord J := (rootCoord J hJ).symm ⟨r, hrR⟩ with hz
  have hrz : root J hJ z = r := by
    rw [← coe_rootCoord, MulEquiv.apply_symm_apply]
  have hrzne : root J hJ z ≠ 1 := by
    rw [hrz]
    exact fun h => hrne (Subtype.ext h)
  have hcne : psuConjHom J A (root J hJ z) ≠ 1 := by
    intro h
    apply hrzne
    have hinj : Function.Injective (psuConjHom J A) := (psuConjHom J A).injective
    exact hinj (h.trans (map_one (psuConjHom J A)).symm)
  have hfixz : (⟨psuConjHom J A (root J hJ z), hAR z⟩ : rootGroup J hJ) •
      guSmul J A (pinf J hJ) = guSmul J A (pinf J hJ) := by
    show (psuConjHom J A (root J hJ z)) • guSmul J A (pinf J hJ) = _
    rw [guSmul_conj_root J hJ A z (pinf J hJ), root_smul_pinf]
  exact root_fixed_eq_pinf J hJ (by simpa using hcne) hfixz

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

theorem first_column_of_fixes_pinf (A : J.unitarySubgroup)
    (h : guSmul J A (pinf J hJ) = pinf J hJ) :
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
  have h' := congrArg (fun x : IsoPoint J => (x : ℙ K (Fin 3 → K))) h
  rw [coe_guSmul, coe_pinf] at h'
  set v : Fin 3 → K := ![1, 0, 0] with hv
  have hvne : v ≠ 0 := by rw [hv]; exact ne_zero_of_apply_zero_ne_zero (by simp)
  have hsm : ((Matrix.ProjGenLinGroup.mk (A : GL (Fin 3) K)) • (Projectivization.mk K v hvne))
      = Projectivization.mk K (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        ((smul_ne_zero_iff_ne (A : GL (Fin 3) K)).2 hvne) :=
    Projectivization.PGL.mk_smul_mk (A : GL (Fin 3) K) hvne
  rw [hsm] at h'
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h'
  constructor
  · have h1 := congrFun hc 1
    simp [v, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1
    exact h1.symm
  · have h2 := congrFun hc 2
    simp [v, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h2
    exact h2.symm

theorem unitary_entries_of_upper (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (A : J.unitarySubgroup)
    (h10 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) :
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 ∧
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
        (J.conj (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0))⁻¹ ∧
      J.conj (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
  set M : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hA : ((A : GL (Fin 3) K)) ∈ J.unitarySubgroup := A.2
  rw [HermitianForm.mem_unitarySubgroup_iff] at hA
  rw [hJ, ← hM] at hA
  have h20' : J.conj (M 2 2) * M 0 0 = 1 := by
    have h := congrFun (congrFun hA 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose, h10, h20] at h
    exact h
  have ha : M 0 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h20'
    exact zero_ne_one h20'
  have h22 : M 2 2 = (J.conj (M 0 0))⁻¹ := by
    have h := congrArg J.conj h20'
    rw [map_mul, map_one, conj_conj] at h
    exact eq_inv_of_mul_eq_one_left h
  have h21 : M 2 1 = 0 := by
    have h := congrFun (congrFun hA 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose, h10, h20] at h
    rcases h with h | h
    · exact (map_eq_zero_iff J.conj J.conj.injective).mp h
    · exact absurd h ha
  have h11 : J.conj (M 1 1) * M 1 1 = 1 := by
    have h := congrFun (congrFun hA 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, HermitianForm.conjTranspose, h21, h10, h20] at h
    simpa using h
  exact ⟨h21, ha, h22, h11⟩

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)

theorem diag3_mem_unitary (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {a b c : Kˣ}
    (hb : (b : K) * J.conj (b : K) = 1) (hc : (c : K) = (J.conj (a : K))⁻¹) :
    diag3 a b c ∈ J.unitarySubgroup := by
  have hb' : J.conj (b : K) * (b : K) = 1 := by rw [mul_comm]; exact hb
  rw [HermitianForm.mem_unitarySubgroup_iff, coe_diag3, hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hb', hc]

theorem det_diag3 (a b c : Kˣ) :
    Matrix.GeneralLinearGroup.det (diag3 a b c) = a * b * c := by
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, coe_diag3, Matrix.det_fin_three]
  norm_num [Matrix.mul_apply, Fin.sum_univ_three]

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

theorem det_of_upper (A : GL (Fin 3) K)
    (h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 =
      (J.conj ((A : Matrix (Fin 3) (Fin 3) K) 0 0))⁻¹) :
    (A : Matrix (Fin 3) (Fin 3) K).det =
      (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
        (J.conj ((A : Matrix (Fin 3) (Fin 3) K) 0 0))⁻¹ := by
  rw [Matrix.det_fin_three, h10, h20, h21, h22]
  ring

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

private theorem diag3_inv_mul_diag_entries (a b c : Kˣ) (M : Matrix (Fin 3) (Fin 3) K)
    (haa : (a : K) = M 0 0) (hbb : (b : K) = M 1 1)
    (hcc : (c : K) = (J.conj (a : K))⁻¹)
    (h22 : M 2 2 = (J.conj (a : K))⁻¹) :
    ((diag3 a b c)⁻¹ * M) 0 0 = 1 ∧ ((diag3 a b c)⁻¹ * M) 1 1 = 1 ∧
      ((diag3 a b c)⁻¹ * M) 2 2 = 1 := by
  rw [coe_diag3_inv]
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [Matrix.mul_apply] <;>
    simp only [Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.zero_apply, mul_zero,
      zero_mul, add_zero, mul_one, zero_add, Units.val_inv_eq_inv_val, inv_inv, ← haa, ← hbb,
      hcc, h22]
  · exact inv_mul_cancel₀ a.ne_zero
  · exact inv_mul_cancel₀ b.ne_zero
  · refine mul_inv_cancel₀ ?_
    intro h
    exact a.ne_zero (J.conj.injective (h.trans (map_zero J.conj).symm))

theorem exists_diag_mul_upper_unitriangular (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (A : J.unitarySubgroup)
    (h10 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (ha : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0)
    (h22 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
      (J.conj (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0))⁻¹)
    (h11 : J.conj (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1) :
    ∃ (D N : J.unitarySubgroup) (a b : Kˣ),
      ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          !![(a : K), 0, 0; 0, (b : K), 0; 0, 0, (J.conj (a : K))⁻¹] ∧
      A = D * N ∧
      ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧
      ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
      ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 ∧
      Matrix.GeneralLinearGroup.det ((N : GL (Fin 3) K)) = 1 := by
  set M : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hb : M 1 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h11
    exact zero_ne_one h11
  set a : Kˣ := Units.mk0 (M 0 0) ha
  set b : Kˣ := Units.mk0 (M 1 1) hb
  have hb' : (b : K) * J.conj (b : K) = 1 := by
    show M 1 1 * J.conj (M 1 1) = 1
    rw [mul_comm]
    exact h11
  have hcne : (J.conj (a : K))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    intro h
    exact a.ne_zero (J.conj.injective (h.trans (map_zero J.conj).symm))
  set c : Kˣ := Units.mk0 ((J.conj (a : K))⁻¹) hcne
  have hc : (c : K) = (J.conj (a : K))⁻¹ := rfl
  have hD : diag3 a b c ∈ J.unitarySubgroup := diag3_mem_unitary J hJ hb' hc
  have hN : (diag3 a b c)⁻¹ * (A : GL (Fin 3) K) ∈ J.unitarySubgroup :=
    J.unitarySubgroup.mul_mem (J.unitarySubgroup.inv_mem hD) A.2
  have hdetA : Matrix.GeneralLinearGroup.det (A : GL (Fin 3) K) = a * b * c := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply,
      det_of_upper J (A : GL (Fin 3) K) h10 h20 h21 h22]
    rfl
  have hdiag := diag3_inv_mul_diag_entries (J := J) a b c
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) rfl rfl hc h22
  refine ⟨⟨diag3 a b c, hD⟩, ⟨(diag3 a b c)⁻¹ * (A : GL (Fin 3) K), hN⟩, a, b,
    ?_, ?_, hdiag.1, ?_, ?_, hdiag.2.1, ?_, hdiag.2.2, ?_⟩
  · rw [coe_diag3]
    rfl
  · apply Subtype.ext
    show (A : GL (Fin 3) K) = diag3 a b c * ((diag3 a b c)⁻¹ * (A : GL (Fin 3) K))
    group
  · show ((diag3 a b c)⁻¹ * (A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0
    rw [coe_diag3_inv, Matrix.mul_apply]
    simp [Fin.sum_univ_three, h10, h20, hM.symm]
  · show ((diag3 a b c)⁻¹ * (A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0
    rw [coe_diag3_inv, Matrix.mul_apply]
    simp [Fin.sum_univ_three, h10, h20, hM.symm]
  · show ((diag3 a b c)⁻¹ * (A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0
    rw [coe_diag3_inv, Matrix.mul_apply]
    simp [Fin.sum_univ_three, h10, h20, h21, hM.symm]
  · rw [map_mul, MonoidHom.map_inv (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ),
      det_diag3, hdetA]
    exact inv_mul_cancel _

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem psuAut_eq_of_eq {θ₁ θ₂ : MulAut (GL (Fin 3) K)}
    (hθ : θ₁ = θ₂) (h₁ : J.specialSubgroup.map θ₁.toMonoidHom = J.specialSubgroup)
    (h₂ : J.specialSubgroup.map θ₂.toMonoidHom = J.specialSubgroup) :
    psuAut J θ₁ h₁ = psuAut J θ₂ h₂ := by
  subst hθ
  rfl

theorem diag3_scalar_center (b : Kˣ) :
    diag3 b b b ∈ Subgroup.center (GL (Fin 3) K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag3, Matrix.mul_apply, Fin.sum_univ_three, mul_assoc, mul_left_comm, mul_comm]

theorem psuConjHom_scalar (b : Kˣ)
    (hD : diag3 b b b ∈ J.unitarySubgroup) :
    psuConjHom J ⟨diag3 b b b, hD⟩ = 1 := by
  rw [psuConjHom_apply]
  have hconj : MulAut.conj (diag3 b b b) = 1 := by
    apply MulEquiv.ext
    intro g
    rw [MulAut.conj_apply, MulAut.one_apply]
    have h := (Subgroup.mem_center_iff.mp (diag3_scalar_center b) g)
    calc diag3 b b b * g * (diag3 b b b)⁻¹ = g * diag3 b b b * (diag3 b b b)⁻¹ := by
          rw [← h]
      _ = g := by rw [mul_assoc, mul_inv_cancel, mul_one]
  exact (psuAut_eq_of_eq J hconj _ (Subgroup.map_id J.specialSubgroup)).trans (psuAut_one J _)

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem psuConjHom_psuMk (N : J.specialSubgroup) :
    psuConjHom J ⟨(N : GL (Fin 3) K), J.specialSubgroup_le_unitarySubgroup N.2⟩ =
      MulAut.conj (psuMk J N) := by
  refine mulAut_ext_mk J fun g hg => ?_
  have hx : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
      ProjectiveSpecialUnitaryMatrixGroup J) = psuMk J ⟨g, hg⟩ := rfl
  rw [hx, coe_psuConjHom_psuMk, MulAut.conj_apply,
    show (psuMk J) N * (psuMk J) ⟨g, hg⟩ * ((psuMk J) N)⁻¹ =
      (psuMk J) (N * ⟨g, hg⟩ * N⁻¹) from by rw [map_mul, map_mul, map_inv],
    coe_psuMk]
  rfl

def diagTorus : Kˣ →* J.unitarySubgroup where
  toFun c := ⟨diag3 c 1 (Units.mk0 ((J.conj (c : K))⁻¹) (inv_ne_zero (by
      intro h
      exact c.ne_zero (J.conj.injective (h.trans (map_zero J.conj).symm))))),
    diag3_mem_unitary J hJ (by simp) rfl⟩
  map_one' := by
    apply Subtype.ext
    rw [Subgroup.coe_one, ← diag3_one]
    congr 1
    exact Units.ext (by simp)
  map_mul' c d := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, diag3_mul]
    congr 2
    exact Units.ext (by simp [map_mul, map_inv, mul_comm])

def torusAut : Kˣ →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (psuConjHom J).comp (diagTorus J hJ)

theorem isCyclic_torusAut_range : IsCyclic (torusAut J hJ).range := by
  haveI : IsCyclic Kˣ := inferInstance
  exact isCyclic_of_surjective (torusAut J hJ).mrangeRestrict
    (torusAut J hJ).mrangeRestrict_surjective

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem diag3_mem_torusAut_range {a b c : Kˣ}
    (hb : (b : K) * J.conj (b : K) = 1) (hc : (c : K) = (J.conj (a : K))⁻¹)
    (hD : diag3 a b c ∈ J.unitarySubgroup) :
    psuConjHom J ⟨diag3 a b c, hD⟩ ∈ (torusAut J hJ).range := by
  have hbconj : J.conj (b : K) = (b : K)⁻¹ := eq_inv_of_mul_eq_one_right hb
  set e : Kˣ := a / b
  have he : (e : K) = (a : K) / (b : K) := by simp [e]
  set e3 : Kˣ := Units.mk0 ((J.conj (e : K))⁻¹) (inv_ne_zero (by
    intro h
    exact e.ne_zero (J.conj.injective (h.trans (map_zero J.conj).symm))))
  have heq : diag3 a b c = diag3 e 1 e3 * diag3 b b b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diag3, Matrix.mul_apply, Fin.sum_univ_three, e, e3, he, hc, hbconj, map_div₀,
        map_inv₀]
    field_simp
  have hE : diag3 e 1 e3 ∈ J.unitarySubgroup := by
    refine diag3_mem_unitary (a := e) (b := 1) (c := e3) J hJ ?_ ?_
    · simp
    · rfl
  have hS : diag3 b b b ∈ J.unitarySubgroup := by
    refine diag3_mem_unitary (a := b) (b := b) (c := b) J hJ ?_ ?_
    · simpa using hb
    · rw [hbconj, inv_inv]
  have hsplit : (⟨diag3 a b c, hD⟩ : J.unitarySubgroup) =
      ⟨diag3 e 1 e3, hE⟩ * ⟨diag3 b b b, hS⟩ := by
    apply Subtype.ext
    show diag3 a b c = diag3 e 1 e3 * diag3 b b b
    exact heq
  rw [hsplit, map_mul, psuConjHom_scalar]
  exact ⟨e, by rw [torusAut, MonoidHom.comp_apply, diagTorus]; rfl⟩

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem eq_hermitianUnipotent_of_unitriangular (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (N : J.specialSubgroup)
    (h00 : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1)
    (h10 : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h11 : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1)
    (h21 : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (h22 : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1) :
    ∃ z : Coord J, (N : GL (Fin 3) K) = hermitianUnipotentGL J z := by
  have hmem : (N : GL (Fin 3) K) ∈ J.unitarySubgroup := J.specialSubgroup_le_unitarySubgroup N.2
  rw [HermitianForm.mem_unitarySubgroup_iff, hJ] at hmem
  have hz : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 =
      -J.conj (((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1) := by
    have h := congrFun (congrFun hmem 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, HermitianForm.conjTranspose, h00, h10, h11,
      h20, h21, h22] at h
    linear_combination h
  have hq : ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 +
      J.conj (((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2) +
      ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1 *
        J.conj (((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1) = 0 := by
    have h := congrFun (congrFun hmem 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, HermitianForm.conjTranspose, h00, h10, h11,
      h20, h21, h22] at h
    rw [hz] at h
    simp only [map_neg, map_mul, map_inv₀, mul_neg, neg_mul, neg_neg, conj_conj] at h
    simpa only [add_assoc, add_comm, add_left_comm] using h
  refine ⟨⟨(((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1,
    ((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2), hq⟩, ?_⟩
  apply Units.ext
  rw [hermitianUnipotentGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, hz, h00, h10, h11, h20, h21, h22]

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem psuConjHom_mem_sup_of_upper (A : J.unitarySubgroup)
    (h10 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0)
    (ha : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0)
    (h22 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 =
      (J.conj (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0))⁻¹)
    (h11 : J.conj (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1) *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1) :
    psuConjHom J A ∈
      (rootGroup J hJ).map (MulAut.conj) ⊔ (torusAut J hJ).range := by
  obtain ⟨D, N, a, b, hDform, hA, hN00, hN10, hN20, hN11, hN21, hN22, hdetN⟩ :=
    exists_diag_mul_upper_unitriangular J hJ A h10 h20 h21 ha h22 h11
  set c : Kˣ := Units.mk0 ((J.conj (a : K))⁻¹) (inv_ne_zero (by
    intro h
    exact a.ne_zero (J.conj.injective (h.trans (map_zero J.conj).symm))))
  have hb : (b : K) * J.conj (b : K) = 1 := by
    have hA11 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = (b : K) := by
      have hmat : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((D : J.unitarySubgroup) : GL (Fin 3) K) *
            ((N : J.unitarySubgroup) : GL (Fin 3) K) := by
        rw [hA]
        simp
      have h := congrFun (congrFun hmat 1) 1
      rw [Matrix.mul_apply] at h
      simp only [Fin.sum_univ_three, hDform, hN11, hN10, hN21, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.of_apply, Matrix.zero_apply, zero_mul, mul_one, zero_add, add_zero] at h
      exact h
    rw [hA11] at h11
    rw [mul_comm]
    exact h11
  have hDmem : diag3 a b c ∈ J.unitarySubgroup := diag3_mem_unitary J hJ hb rfl
  have hDtorus : psuConjHom J D ∈ (torusAut J hJ).range := by
    have hDdiag : D = ⟨diag3 a b c, hDmem⟩ := by
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [coe_diag3]
      exact congrFun (congrFun hDform i) j
    rw [hDdiag]
    exact diag3_mem_torusAut_range J hJ hb rfl hDmem
  have hNroot : psuConjHom J N ∈ (rootGroup J hJ).map (MulAut.conj) := by
    have hNS : ((N : GL (Fin 3) K)) ∈ J.specialSubgroup := by
      rw [HermitianForm.mem_specialSubgroup_iff]
      exact ⟨N.2, hdetN⟩
    obtain ⟨z, hz⟩ := eq_hermitianUnipotent_of_unitriangular J hJ ⟨(N : GL (Fin 3) K), hNS⟩
      hN00 hN10 hN20 hN11 hN21 hN22
    have hpsu : psuConjHom J N =
        MulAut.conj (psuMk J ⟨(N : GL (Fin 3) K), hNS⟩) :=
      psuConjHom_psuMk (N := ⟨(N : GL (Fin 3) K), hNS⟩)
    have hroot : psuMk J ⟨(N : GL (Fin 3) K), hNS⟩ = root J hJ z := by
      apply Subtype.ext
      rw [coe_psuMk]
      rw [show ((⟨(N : GL (Fin 3) K), hNS⟩ : J.specialSubgroup) : GL (Fin 3) K) =
          (N : GL (Fin 3) K) from rfl, hz]
      exact (coe_root_eq_mk J hJ z).symm
    rw [hpsu, hroot]
    exact Subgroup.mem_map_of_mem _ (root_mem_rootGroup J hJ z)
  rw [hA, map_mul]
  have hmem := Subgroup.mul_mem_sup hDtorus hNroot
  simpa [sup_comm] using hmem

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

theorem psuField_conj_psuConj (σ : K ≃+* K) (A : J.unitarySubgroup) :
    psuFieldHom J hJ hK hfix σ * psuConjHom J A * (psuFieldHom J hJ hK hfix σ)⁻¹ =
      psuConjHom J ⟨(glAut σ) (A : GL (Fin 3) K),
        glAut_mem_unitary J hJ hK hfix σ A.2⟩ := by
  have hf : ∀ (τ : K ≃+* K) (x : J.specialSubgroup),
      psuFieldHom J hJ hK hfix τ (psuMk J x) =
        psuMk J ⟨(glAut τ) (x : GL (Fin 3) K),
          glAut_mem_specialSubgroup hJ (ringAut_conj_comm J hK hfix τ) x.2⟩ :=
    fun τ x => Subtype.ext (coe_psuFieldHom_psuMk J hJ hK hfix τ x)
  have hc : ∀ (B : J.unitarySubgroup) (x : J.specialSubgroup),
      psuConjHom J B (psuMk J x) =
        psuMk J ⟨(B : GL (Fin 3) K) * (x : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹,
          conj_mem_specialSubgroup B.2 x.2⟩ :=
    fun B x => Subtype.ext (coe_psuConjHom_psuMk J B x)
  refine mulAut_ext_mk J fun g hg => ?_
  have hx : (⟨Matrix.ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
      ProjectiveSpecialUnitaryMatrixGroup J) = psuMk J ⟨g, hg⟩ := rfl
  rw [hx, MulAut.mul_apply, MulAut.mul_apply,
    show (psuFieldHom J hJ hK hfix σ)⁻¹ = psuFieldHom J hJ hK hfix σ⁻¹ from
      (map_inv _ _).symm]
  rw [hf σ⁻¹ ⟨g, hg⟩, hc A ⟨(glAut σ⁻¹) (g : GL (Fin 3) K),
    glAut_mem_specialSubgroup hJ (ringAut_conj_comm J hK hfix σ⁻¹) hg⟩,
    hf σ ⟨(A : GL (Fin 3) K) * (glAut σ⁻¹) (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹,
      conj_mem_specialSubgroup A.2
        (glAut_mem_specialSubgroup hJ (ringAut_conj_comm J hK hfix σ⁻¹) hg)⟩,
    hc ⟨(glAut σ) (A : GL (Fin 3) K), glAut_mem_unitary J hJ hK hfix σ A.2⟩ ⟨g, hg⟩]
  rw [coe_psuMk, coe_psuMk]
  congr 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
  rw [map_mul, map_mul, map_inv]
  congr 1
  rw [show (glAut σ) ((glAut σ)⁻¹ (g : GL (Fin 3) K)) = g from by
    rw [← MulAut.mul_apply, mul_inv_cancel]
    rfl]

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

open CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter in
theorem psuFieldHom_root (σ : K ≃+* K) (z : Coord J) :
    psuFieldHom J hJ hK hfix σ (root J hJ z) =
      root J hJ (sigmaCoord J σ (ringAut_conj_comm J hK hfix σ) z) := by
  have h1 : root J hJ z = psuMk J (hermitianUnipotentSU J hJ z) := rfl
  have h2 : root J hJ (sigmaCoord J σ (ringAut_conj_comm J hK hfix σ) z) =
      psuMk J (hermitianUnipotentSU J hJ
        (sigmaCoord J σ (ringAut_conj_comm J hK hfix σ) z)) := rfl
  rw [h1, h2]
  apply Subtype.ext
  rw [coe_psuFieldHom_psuMk, coe_psuMk]
  exact congrArg Matrix.ProjGenLinGroup.mk
    (glAut_hermitianUnipotentGL J σ (ringAut_conj_comm J hK hfix σ) z)

open CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter in
theorem psuFieldHom_stabilizes_rootGroup (σ : K ≃+* K) :
    (rootGroup J hJ).map (psuFieldHom J hJ hK hfix σ).toMonoidHom = rootGroup J hJ := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    change psuFieldHom J hJ hK hfix σ (root J hJ z) ∈ rootGroup J hJ
    rw [psuFieldHom_root J hJ hK hfix σ z]
    exact root_mem_rootGroup J hJ _
  · rw [Subgroup.card_map_of_injective (f := (psuFieldHom J hJ hK hfix σ).toMonoidHom)
      (psuFieldHom J hJ hK hfix σ).injective]

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

theorem commutator_le_of_factor_maps {Γ U S : Type*} [Group Γ] [Group U] [Group S]
    (φ : U →* Γ) (ψ : S →* Γ) (act : S → U → U)
    (hS : ∀ s t : S, s * t = t * s)
    (hconj : ∀ (s : S) (x : U), ψ s * φ x * (ψ s)⁻¹ = φ (act s x))
    {A : Subgroup Γ} (hdecomp : ∀ α ∈ A, ∃ x s, φ x * ψ s = α)
    {W : Subgroup Γ}
    (hword : ∀ (x y : U) (s t : S), φ x * ψ s ∈ A → φ y * ψ t ∈ A →
      φ (x * (act s y) * (act t x)⁻¹ * y⁻¹) ∈ W) :
    ⁅A, A⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro α hα β hβ
  obtain ⟨x, s, rfl⟩ := hdecomp α hα
  obtain ⟨y, t, rfl⟩ := hdecomp β hβ
  have hst : ψ s * ψ t = ψ t * ψ s := by rw [← map_mul, ← map_mul, hS]
  have e1 : ψ s * φ y = φ (act s y) * ψ s := by
    rw [← hconj s y]; group
  have e2 : ψ t * (φ x)⁻¹ = (φ (act t x))⁻¹ * ψ t := by
    rw [← hconj t x]; group
  have hst' : ψ t * (ψ s)⁻¹ = (ψ s)⁻¹ * ψ t := by
    calc ψ t * (ψ s)⁻¹ = (ψ s)⁻¹ * (ψ s * ψ t) * (ψ s)⁻¹ := by group
      _ = (ψ s)⁻¹ * (ψ t * ψ s) * (ψ s)⁻¹ := by rw [hst]
      _ = (ψ s)⁻¹ * ψ t := by group
  have key : φ x * ψ s * (φ y * ψ t) * (φ x * ψ s)⁻¹ * (φ y * ψ t)⁻¹ =
      φ (x * (act s y) * (act t x)⁻¹ * y⁻¹) := by
    calc φ x * ψ s * (φ y * ψ t) * (φ x * ψ s)⁻¹ * (φ y * ψ t)⁻¹
        = φ x * (ψ s * φ y) * ψ t * ((ψ s)⁻¹ * (φ x)⁻¹) * ((ψ t)⁻¹ * (φ y)⁻¹) := by group
      _ = φ x * (φ (act s y) * ψ s) * ψ t * ((ψ s)⁻¹ * (φ x)⁻¹) *
            ((ψ t)⁻¹ * (φ y)⁻¹) := by rw [e1]
      _ = φ x * φ (act s y) * (ψ s * ψ t) * ((ψ s)⁻¹ * (φ x)⁻¹) *
            ((ψ t)⁻¹ * (φ y)⁻¹) := by group
      _ = φ x * φ (act s y) * (ψ t * ψ s) * ((ψ s)⁻¹ * (φ x)⁻¹) *
            ((ψ t)⁻¹ * (φ y)⁻¹) := by rw [hst]
      _ = φ x * φ (act s y) * ψ t * ((ψ s * (ψ s)⁻¹) * (φ x)⁻¹) *
            ((ψ t)⁻¹ * (φ y)⁻¹) := by group
      _ = φ x * φ (act s y) * (ψ t * (φ x)⁻¹) * ((ψ t)⁻¹ * (φ y)⁻¹) := by group
      _ = φ x * φ (act s y) * ((φ (act t x))⁻¹ * ψ t) * ((ψ t)⁻¹ * (φ y)⁻¹) := by rw [e2]
      _ = φ x * φ (act s y) * (φ (act t x))⁻¹ * (φ y)⁻¹ := by group
      _ = φ (x * (act s y) * (act t x)⁻¹ * y⁻¹) := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  change (φ x * ψ s * (φ y * ψ t) * (φ x * ψ s)⁻¹ * (φ y * ψ t)⁻¹) ∈ W
  rw [key]
  exact hword x y s t ‹φ x * ψ s ∈ A› ‹φ y * ψ t ∈ A›

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped LinearAlgebra.Projectivization Matrix

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

def coordConj (c : Kˣ) (z : Coord J) : Coord J :=
  ⟨(c * z.1.1, c * z.1.2 * J.conj c), by
    change c * z.1.2 * J.conj c + J.conj (c * z.1.2 * J.conj c) +
        c * z.1.1 * J.conj (c * z.1.1) = 0
    simp only [map_mul, conj_conj]
    linear_combination (c * J.conj c) * z.2⟩

theorem conj_diag3_hermitianUnipotentGL (c : Kˣ) (z : Coord J) :
    diag3 c 1 (Units.mk0 ((J.conj (c : K))⁻¹) (inv_ne_zero (by
        intro h
        exact c.ne_zero (J.conj.injective (h.trans (map_zero J.conj).symm)))))
      * hermitianUnipotentGL J z
      * (diag3 c 1 (Units.mk0 ((J.conj (c : K))⁻¹) (inv_ne_zero (by
        intro h
        exact c.ne_zero (J.conj.injective (h.trans (map_zero J.conj).symm))))))⁻¹ =
    hermitianUnipotentGL J (coordConj J c z) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    coe_diag3, coe_diag3_inv]
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentGL, hermitianUnipotentMatrix, coordConj, Matrix.mul_apply,
      Fin.sum_univ_three, map_mul] <;> ring

theorem torusAut_maps_rootGroup (c : Kˣ) :
    (rootGroup J hJ).map (torusAut J hJ c).toMonoidHom = rootGroup J hJ := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    have h : torusAut J hJ c (root J hJ z) = root J hJ (coordConj J c z) := by
      apply Subtype.ext
      show ((psuConjHom J (diagTorus J hJ c) (root J hJ z) :
        ProjectiveSpecialUnitaryMatrixGroup J) : Matrix.ProjGenLinGroup (Fin 3) K) = _
      rw [root_eq_psuMk, coe_psuConjHom_psuMk]
      exact congrArg Matrix.ProjGenLinGroup.mk (conj_diag3_hermitianUnipotentGL J c z)
    show torusAut J hJ c (root J hJ z) ∈ rootGroup J hJ
    rw [h]
    exact root_mem_rootGroup J hJ _
  · rw [Subgroup.card_map_of_injective (torusAut J hJ c).injective]

theorem torusAut_mem_rootGroup (c : Kˣ) {x : ProjectiveSpecialUnitaryMatrixGroup J}
    (hx : x ∈ rootGroup J hJ) : torusAut J hJ c x ∈ rootGroup J hJ := by
  have h := Subgroup.mem_map_of_mem (torusAut J hJ c).toMonoidHom hx
  rwa [torusAut_maps_rootGroup] at h

theorem conj_conj_mulAut (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (r : ProjectiveSpecialUnitaryMatrixGroup J) :
    MulAut.conj β (MulAut.conj r) = MulAut.conj (β r) := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
    MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv]

theorem torusAut_range_le_normalizer_map_conj :
    (torusAut J hJ).range ≤
      Subgroup.normalizer
        (((rootGroup J hJ).map (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
          MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :
          Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  rintro α ⟨c, rfl⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    change MulAut.conj (torusAut J hJ c) (MulAut.conj r) = x at hxy
    rw [← hxy, conj_conj_mulAut]
    exact Subgroup.mem_map_of_mem _ (torusAut_mem_rootGroup J hJ c hr)
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨MulAut.conj ((torusAut J hJ c)⁻¹ r),
      Subgroup.mem_map_of_mem _ ?_, ?_⟩
    · rw [← map_inv]
      exact torusAut_mem_rootGroup J hJ c⁻¹ hr
    · change MulAut.conj (torusAut J hJ c) (MulAut.conj ((torusAut J hJ c)⁻¹ r)) =
        MulAut.conj r
      rw [conj_conj_mulAut]
      simp

theorem guSmul_one (x : IsoPoint J) : guSmul J 1 x = x := by
  apply Subtype.ext
  rw [coe_guSmul]
  simp

theorem guSmul_mul (A B : J.unitarySubgroup) (x : IsoPoint J) :
    guSmul J (A * B) x = guSmul J A (guSmul J B x) := by
  apply Subtype.ext
  rw [coe_guSmul, coe_guSmul, coe_guSmul]
  rw [show (((A * B : J.unitarySubgroup) : GL (Fin 3) K)) =
    (A : GL (Fin 3) K) * (B : GL (Fin 3) K) from rfl, map_mul, mul_smul]

instance instMulActionUnitarySubgroup : MulAction J.unitarySubgroup (IsoPoint J) where
  smul := guSmul J
  one_smul := guSmul_one J
  mul_smul := guSmul_mul J

def stabPinf : Subgroup J.unitarySubgroup :=
  MulAction.stabilizer J.unitarySubgroup (pinf J hJ)

theorem mem_stabPinf {A : J.unitarySubgroup} :
    A ∈ stabPinf J hJ ↔ guSmul J A (pinf J hJ) = pinf J hJ :=
  MulAction.mem_stabilizer_iff

theorem fixes_pinf_of_first_column (A : J.unitarySubgroup)
    (h10 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h20 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) :
    guSmul J A (pinf J hJ) = pinf J hJ := by
  apply Subtype.ext
  rw [coe_guSmul, coe_pinf, Projectivization.PGL.mk_smul_mk]
  refine (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨(A : GL (Fin 3) K) 0 0, ?_⟩
  funext i
  fin_cases i <;>
    simp [Units.smul_def, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10, h20]

theorem glAut_mem_stabPinf (σ : K ≃+* K) {A : J.unitarySubgroup}
    (hA : A ∈ stabPinf J hJ) :
    (⟨(glAut σ) (A : GL (Fin 3) K),
      glAut_mem_unitary J hJ hK hfix σ A.2⟩ : J.unitarySubgroup) ∈ stabPinf J hJ := by
  obtain ⟨h10, h20⟩ := first_column_of_fixes_pinf J hJ A ((mem_stabPinf J hJ).1 hA)
  rw [mem_stabPinf]
  refine fixes_pinf_of_first_column J hJ _ ?_ ?_
  · rw [coe_glAut]
    simp [h10]
  · rw [coe_glAut]
    simp [h20]

end

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model
open CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped LinearAlgebra.Projectivization Matrix commutatorElement

noncomputable section

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

theorem mem_stabPinf_of_factor (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hq : 2 < p ^ f)
    {A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hA : ∀ α ∈ A, (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ)
    {x : J.unitarySubgroup} {s : K ≃+* K}
    (hxs : psuConjHom J x * psuFieldHom J hJ hK hfix s ∈ A) :
    x ∈ stabPinf J hJ := by
  have hroot : ∀ z : Coord J, psuConjHom J x (root J hJ z) ∈ rootGroup J hJ := by
    have hprod : (rootGroup J hJ).map
        (psuConjHom J x * psuFieldHom J hJ hK hfix s).toMonoidHom = rootGroup J hJ :=
      hA _ hxs
    rw [show ((psuConjHom J x * psuFieldHom J hJ hK hfix s)).toMonoidHom =
        (psuConjHom J x).toMonoidHom.comp (psuFieldHom J hJ hK hfix s).toMonoidHom from rfl,
      ← Subgroup.map_map, psuFieldHom_stabilizes_rootGroup J hJ hK hfix s] at hprod
    intro z
    have hmem := Subgroup.mem_map_of_mem (psuConjHom J x).toMonoidHom
      (root_mem_rootGroup J hJ z)
    rwa [hprod] at hmem
  exact (mem_stabPinf J hJ).2
    (guSmul_pinf_of_stabilizes_rootGroup J hJ hK hfix (by omega) x hroot)

theorem commutator_le_of_stabilizes_rootGroup
    (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)
    (hq : 2 < p ^ f)
    {A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hA : ∀ α ∈ A, (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ) :
    ⁅A, A⁆ ≤ (rootGroup J hJ).map (MulAut.conj :
      ProjectiveSpecialUnitaryMatrixGroup J →*
        MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ⊔ (torusAut J hJ).range := by
  classical
  refine commutator_le_of_factor_maps (φ := psuConjHom J)
    (ψ := psuFieldHom J hJ hK hfix)
    (act := fun σ (x : J.unitarySubgroup) =>
      (⟨(glAut σ) (x : GL (Fin 3) K),
        glAut_mem_unitary J hJ hK hfix σ x.2⟩ : J.unitarySubgroup))
    ?_ ?_ ?_ ?_
  · intro s t
    haveI : IsCyclic (K ≃+* K) := CFSG.GH74.GLS.IVK.ringAut_isCyclic K
    exact IsCyclic.commGroup.mul_comm s t
  · intro σ x
    exact psuField_conj_psuConj J hJ hK hfix σ x
  · intro β _
    obtain ⟨x, s, hxs⟩ := exists_eq_psuConj_mul_psuField J hJ hK hfix hq β
    exact ⟨x, s, hxs.symm⟩
  · intro x y s t hxs hyt
    have hx : x ∈ stabPinf J hJ := mem_stabPinf_of_factor J hJ hK hfix hq hA hxs
    have hy : y ∈ stabPinf J hJ := mem_stabPinf_of_factor J hJ hK hfix hq hA hyt
    have hsy : (⟨(glAut s) (y : GL (Fin 3) K),
        glAut_mem_unitary J hJ hK hfix s y.2⟩ : J.unitarySubgroup) ∈ stabPinf J hJ :=
      glAut_mem_stabPinf J hJ hK hfix s hy
    have htx : (⟨(glAut t) (x : GL (Fin 3) K),
        glAut_mem_unitary J hJ hK hfix t x.2⟩ : J.unitarySubgroup) ∈ stabPinf J hJ :=
      glAut_mem_stabPinf J hJ hK hfix t hx
    have hword : x * (⟨(glAut s) (y : GL (Fin 3) K),
          glAut_mem_unitary J hJ hK hfix s y.2⟩ : J.unitarySubgroup) *
        (⟨(glAut t) (x : GL (Fin 3) K),
          glAut_mem_unitary J hJ hK hfix t x.2⟩ : J.unitarySubgroup)⁻¹ * y⁻¹ ∈
        stabPinf J hJ :=
      (stabPinf J hJ).mul_mem ((stabPinf J hJ).mul_mem ((stabPinf J hJ).mul_mem hx hsy)
        ((stabPinf J hJ).inv_mem htx)) ((stabPinf J hJ).inv_mem hy)
    obtain ⟨h10, h20⟩ := first_column_of_fixes_pinf J hJ _
      ((mem_stabPinf J hJ).1 hword)
    obtain ⟨h21, ha, h22, h11⟩ := unitary_entries_of_upper J hJ _ h10 h20
    exact psuConjHom_mem_sup_of_upper J hJ _ h10 h20 h21 ha h22 h11

theorem pRank_three_commutator_le_one_of_stabilizes_rootGroup
    (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)
    (hp3 : p ≠ 3) (hq : 2 < p ^ f)
    {A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))}
    (hA : ∀ α ∈ A, (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ) :
    CFSG.Open.pRank 3 ⁅A, A⁆ ≤ 1 := by
  have hW := commutator_le_of_stabilizes_rootGroup J hJ hK hfix hq hA
  have hT : IsPGroup p ((rootGroup J hJ).map (MulAut.conj :
      ProjectiveSpecialUnitaryMatrixGroup J →*
        MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :=
    IsPGroup.map (isPGroup_rootGroup J hJ hK hfix)
      (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
        MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
  have hJc : IsCyclic (torusAut J hJ).range := isCyclic_torusAut_range J hJ
  have hNB : (rootGroup J hJ).map (MulAut.conj :
        ProjectiveSpecialUnitaryMatrixGroup J →*
          MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ⊔ (torusAut J hJ).range ≤
      Subgroup.normalizer (((rootGroup J hJ).map (MulAut.conj :
        ProjectiveSpecialUnitaryMatrixGroup J →*
          MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :
        Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) :=
    sup_le Subgroup.le_normalizer (torusAut_range_le_normalizer_map_conj J hJ)
  have hrank : CFSG.Open.pRank 3 ((rootGroup J hJ).map (MulAut.conj :
        ProjectiveSpecialUnitaryMatrixGroup J →*
          MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ⊔ (torusAut J hJ).range) ≤ 1 :=
    CFSG.SectionRank.pRank_le_one_of_isPGroup_sup_cyclic
      (Y := MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (p := p) (r := 3)
      (by norm_num) hp3 hT hJc rfl hNB
  exact (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hW).trans hrank

theorem pRank_three_commutator_le_one_of_stabilizes_sylow
    {L : Type} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hp3 : p ≠ 3)
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (e : L ≃* CFSG.AGLEmbedding.CatGroup d) (U : Sylow p L)
    (A : Subgroup (MulAut L))
    (hA : ∀ α ∈ A, (U : Subgroup L).map α.toMonoidHom = U) :
    CFSG.Open.pRank 3 ⁅A, A⁆ ≤ 1 := by
  classical
  have hcm : CFSG.Open.StatedClassicalModel L .PSU 3 p d.1.fieldExponent :=
    statedClassicalModel hd ⟨e⟩
  obtain ⟨-, hf, hq, K, hKfield, hKfin, J, hJ, hKcard, hfix, ⟨eP⟩⟩ :=
    exists_equiv_psu (f := d.1.fieldExponent) hcm
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hKcard hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq eP U S
  let Φ : MulAut L ≃* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := MulAut.congr e'
  let A' : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := A.map Φ.toMonoidHom
  have hA' : ∀ β ∈ A', (rootGroup J hJ).map β.toMonoidHom = rootGroup J hJ := by
    intro β hβ
    obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.mp hβ
    rw [← hS, ← he', Subgroup.map_map]
    change Subgroup.map ((Φ α).toMonoidHom.comp e'.toMonoidHom) U =
      Subgroup.map e'.toMonoidHom U
    have hcomp : (Φ α).toMonoidHom.comp e'.toMonoidHom =
        e'.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp [Φ, MulAut.congr_apply]
    rw [hcomp, ← Subgroup.map_map, hA α hα]
  have hstep : CFSG.Open.pRank 3 ⁅A', A'⁆ ≤ 1 :=
    pRank_three_commutator_le_one_of_stabilizes_rootGroup J hJ hKcard hfix hp3 hq hA'
  have hmap : (⁅A, A⁆).map Φ.toMonoidHom = ⁅A', A'⁆ := by
    rw [Subgroup.map_commutator]
  calc CFSG.Open.pRank 3 ⁅A, A⁆
      ≤ CFSG.Open.pRank 3 ((⁅A, A⁆).map Φ.toMonoidHom) :=
        CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 3) Φ.toMonoidHom Φ.injective _
    _ = CFSG.Open.pRank 3 ⁅A', A'⁆ := by rw [hmap]
    _ ≤ 1 := hstep

end

end CFSG.AGLEmbedding.UnitaryModel
