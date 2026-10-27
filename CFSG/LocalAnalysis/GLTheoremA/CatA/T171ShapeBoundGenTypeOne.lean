module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem linTypeOne_commuting (hLB : LinBlockInnDiag)
    {G : Type} [Group G] [Finite G] {p N n : ℕ} {L J A : Subgroup G} {d b : G}
    {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ n)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ,
      LargeEvenInduces θ (conjRel a) φ)
    (hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hsetup : Setup p L J A d b)
    (M : LiftMap (L := L) (A := A) (S := Set.univ) θ hact hS)
    (hc : ∃ c : Kˣ, (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p))
    (hcomm : M.mat ⟨b, hsetup.b_mem⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
      M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨b, hsetup.b_mem⟩) : False := by
  classical
  obtain ⟨c, hc⟩ := hc
  obtain ⟨mat, hmat, hind⟩ := M
  let s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹
  let D : GL (Fin N) K := s * mat ⟨d, hsetup.d_mem⟩
  let Mb : GL (Fin N) K := mat ⟨b, hsetup.b_mem⟩
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hDnorm : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    Subgroup.mul_mem _ (TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs)
      (hS (hmat ⟨d, hsetup.d_mem⟩))
  have hBnorm : Mb ∈
      Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    hS (hmat ⟨b, hsetup.b_mem⟩)
  have hsMd : s * mat ⟨d, hsetup.d_mem⟩ = mat ⟨d, hsetup.d_mem⟩ * s :=
    (Subgroup.mem_center_iff.mp
      (TableB.scalars_le_center hs) (mat ⟨d, hsetup.d_mem⟩)).symm
  have hsMb : s * Mb = Mb * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalars_le_center hs) Mb).symm
  have hDpow : D ^ p = 1 := by
    have hsp : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) ((c⁻¹ : Kˣ) ^ p) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c⁻¹ p).symm
    rw [show D = s * mat ⟨d, hsetup.d_mem⟩ from rfl,
      Commute.mul_pow hsMd p, hsp, hc, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hcommD : Commute D Mb := by
    show D * Mb = Mb * D
    rw [show D = s * mat ⟨d, hsetup.d_mem⟩ from rfl]
    calc (s * mat ⟨d, hsetup.d_mem⟩) * Mb
        = s * (mat ⟨d, hsetup.d_mem⟩ * Mb) := by group
      _ = s * (Mb * mat ⟨d, hsetup.d_mem⟩) := by rw [← hcomm]
      _ = (s * Mb) * mat ⟨d, hsetup.d_mem⟩ := by group
      _ = (Mb * s) * mat ⟨d, hsetup.d_mem⟩ := by rw [hsMb]
      _ = Mb * (s * mat ⟨d, hsetup.d_mem⟩) := by group
  have hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hDnorm⟩) := by
    have hsub : (⟨D, hDnorm⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) =
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) *
        ⟨mat ⟨d, hsetup.d_mem⟩, hS (hmat ⟨d, hsetup.d_mem⟩)⟩ := Subtype.ext rfl
    have hscalar : TableB.projConj (LargeEvenSLGroup (Fin N) K)
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) = 1 :=
      TableB.projConj_of_scalar (LargeEvenSLGroup (Fin N) K) hs
    rw [hsub, map_mul, hscalar, one_mul]
    exact hind ⟨d, hsetup.d_mem⟩
  exact hsetup.nonID (hLB G p L J A d b N n K hcard hsetup.toWSetup θ D Mb hDnorm hBnorm hDpow
    hcommD hDind (hind ⟨b, hsetup.b_mem⟩))

theorem scalar_mul_mem_guSet {N n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    {M : GL (Fin N) K} (hM : M ∈ LargeEvenGUSet (Fin N) K (2 ^ n)) (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin N) c * M ∈
      LargeEvenGUSet (Fin N) K (2 ^ n) := by
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨μ, hμ0, hμq, hMeq⟩ := hM
  have hbar : ∀ X : Matrix (Fin N) (Fin N) K, X.map h.bar = X.map (· ^ 2 ^ n) := fun X => by
    ext i j
    rfl
  have hMeq' : Matrix.transpose (((M : Matrix (Fin N) (Fin N) K)).map h.bar) *
      (M : Matrix (Fin N) (Fin N) K) = μ • 1 := by
    rw [hbar]
    exact hMeq
  have h2 : (2 ^ n) ^ 2 = Nat.card K := by
    rw [h.card]
    conv_lhs => rw [← pow_mul]
    rw [Nat.mul_comm n 2]
  have hcq : (c : K) ^ (2 ^ n) ^ 2 = (c : K) := by
    rw [h2, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card (c : K)
  have hpow : ((c : K) ^ (2 ^ n + 1) * μ) ^ 2 ^ n =
      (c : K) ^ (2 ^ n + 1) * μ := by
    rw [mul_pow, ← pow_mul, hμq]
    congr 1
    rw [show (2 ^ n + 1) * 2 ^ n = (2 ^ n) ^ 2 + 2 ^ n by ring, pow_add, hcq,
      mul_comm, pow_succ]
  refine ⟨(c : K) ^ (2 ^ n + 1) * μ, mul_ne_zero (pow_ne_zero _ c.ne_zero) hμ0, hpow, ?_⟩
  rw [TableB.coe_scalar_mul]
  have hstep : Matrix.transpose ((((c : K) • (M : Matrix (Fin N) (Fin N) K)).map h.bar)) =
      h.bar (c : K) • Matrix.transpose (((M : Matrix (Fin N) (Fin N) K)).map h.bar) :=
    TableB.transpose_map_smul h.bar (c : K) (M : Matrix (Fin N) (Fin N) K)
  calc Matrix.transpose ((((c : K) • (M : Matrix (Fin N) (Fin N) K)).map (· ^ 2 ^ n))) *
        ((c : K) • (M : Matrix (Fin N) (Fin N) K))
      = Matrix.transpose ((((c : K) • (M : Matrix (Fin N) (Fin N) K)).map h.bar)) *
        ((c : K) • (M : Matrix (Fin N) (Fin N) K)) := by rw [hbar]
    _ = (h.bar (c : K) • Matrix.transpose (((M : Matrix (Fin N) (Fin N) K)).map h.bar)) *
        ((c : K) • (M : Matrix (Fin N) (Fin N) K)) := by rw [hstep]
    _ = (h.bar (c : K) * (c : K)) •
        (Matrix.transpose (((M : Matrix (Fin N) (Fin N) K)).map h.bar) *
          (M : Matrix (Fin N) (Fin N) K)) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = (h.bar (c : K) * (c : K) * μ) • (1 : Matrix (Fin N) (Fin N) K) := by
        rw [hMeq', smul_smul]
    _ = ((c : K) ^ (2 ^ n + 1) * μ) • (1 : Matrix (Fin N) (Fin N) K) := by
        rw [UnitaryFieldData.bar_apply, pow_succ]

theorem uniTypeOne_commuting (hUB : UniBlockInnDiag)
    {G : Type} [Group G] [Finite G] {p N n : ℕ} {L J A : Subgroup G} {d b : G}
    {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hN : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2))
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)}
    {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K N)) (LargeEvenGUSet (Fin N) K (2 ^ n)),
      LargeEvenInduces θ (conjRel a) φ}
    {hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆ Subgroup.normalizer
      (unitarySU 2 n K N : Set (GL (Fin N) K))}
    (hsetup : Setup p L J A d b)
    (M : LiftMap (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n)) θ hact hS)
    (hc : ∃ c : Kˣ, (M.mat ⟨d, hsetup.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p))
    (hcomm : M.mat ⟨b, hsetup.b_mem⟩ * M.mat ⟨d, hsetup.d_mem⟩ =
      M.mat ⟨d, hsetup.d_mem⟩ * M.mat ⟨b, hsetup.b_mem⟩) : False := by
  classical
  obtain ⟨c, hc⟩ := hc
  obtain ⟨mat, hmat, hind⟩ := M
  let s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹
  let D : GL (Fin N) K := s * mat ⟨d, hsetup.d_mem⟩
  let Mb : GL (Fin N) K := mat ⟨b, hsetup.b_mem⟩
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hDgu : D ∈ LargeEvenGUSet (Fin N) K (2 ^ n) :=
    scalar_mul_mem_guSet h (hmat ⟨d, hsetup.d_mem⟩) c⁻¹
  have hBgu : Mb ∈ LargeEvenGUSet (Fin N) K (2 ^ n) := hmat ⟨b, hsetup.b_mem⟩
  have hDnorm : D ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer h hDgu
  have hBnorm : Mb ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    hS hBgu
  have hsMd : s * mat ⟨d, hsetup.d_mem⟩ = mat ⟨d, hsetup.d_mem⟩ * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center c⁻¹)
      (mat ⟨d, hsetup.d_mem⟩)).symm
  have hsMb : s * Mb = Mb * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center c⁻¹) Mb).symm
  have hDpow : D ^ p = 1 := by
    have hsp : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) ((c⁻¹ : Kˣ) ^ p) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c⁻¹ p).symm
    rw [show D = s * mat ⟨d, hsetup.d_mem⟩ from rfl,
      Commute.mul_pow hsMd p, hsp, hc, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hcommD : Commute D Mb := by
    show D * Mb = Mb * D
    rw [show D = s * mat ⟨d, hsetup.d_mem⟩ from rfl]
    calc (s * mat ⟨d, hsetup.d_mem⟩) * Mb
        = s * (mat ⟨d, hsetup.d_mem⟩ * Mb) := by group
      _ = s * (Mb * mat ⟨d, hsetup.d_mem⟩) := by rw [← hcomm]
      _ = (s * Mb) * mat ⟨d, hsetup.d_mem⟩ := by group
      _ = (Mb * s) * mat ⟨d, hsetup.d_mem⟩ := by rw [hsMb]
      _ = Mb * (s * mat ⟨d, hsetup.d_mem⟩) := by group
  have hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩) := by
    have hsub : (⟨D, hDnorm⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) =
        (⟨s, TableB.scalar_mem_normalizer (unitarySU 2 n K N) hs⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) *
        ⟨mat ⟨d, hsetup.d_mem⟩, hS (hmat ⟨d, hsetup.d_mem⟩)⟩ := Subtype.ext rfl
    have hscalar : TableB.projConj (unitarySU 2 n K N)
        (⟨s, TableB.scalar_mem_normalizer (unitarySU 2 n K N) hs⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) = 1 :=
      TableB.projConj_of_scalar (unitarySU 2 n K N) hs
    rw [hsub, map_mul, hscalar, one_mul]
    exact hind ⟨d, hsetup.d_mem⟩
  exact hsetup.nonID (hUB G p L J A d b N n K h hN hNq hsetup.toWSetup θ D Mb hDgu hBgu hDnorm
    hBnorm hDpow hcommD hDind (hind ⟨b, hsetup.b_mem⟩))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
