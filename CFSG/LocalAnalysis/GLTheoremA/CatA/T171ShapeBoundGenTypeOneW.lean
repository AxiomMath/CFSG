module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenTypeOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeWSetup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem linTypeOne_commuting_of_wSetup (hLB : LinBlockInnDiag)
    {G : Type} [Group G] [Finite G] {p N n : ℕ} {L J A : Subgroup G} {d b : G}
    {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ n)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    (hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ,
      LargeEvenInduces θ (conjRel a) φ)
    (hS : (Set.univ : Set (GL (Fin N) K)) ⊆ Subgroup.normalizer
      (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hw : WSetup p L J A d b)
    (hnonID : ¬ InnDiagOn p (Subgroup.zpowers b) J)
    (M : LiftMap (L := L) (A := A) (S := Set.univ) θ hact hS)
    (hc : ∃ c : Kˣ, (M.mat ⟨d, hw.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p))
    (hcomm : M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ =
      M.mat ⟨d, hw.d_mem⟩ * M.mat ⟨b, hw.b_mem⟩) : False := by
  classical
  obtain ⟨c, hc⟩ := hc
  obtain ⟨mat, hmat, hind⟩ := M
  let s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹
  let D : GL (Fin N) K := s * mat ⟨d, hw.d_mem⟩
  let Mb : GL (Fin N) K := mat ⟨b, hw.b_mem⟩
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hDnorm : D ∈ Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    Subgroup.mul_mem _ (TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs)
      (hS (hmat ⟨d, hw.d_mem⟩))
  have hBnorm : Mb ∈
      Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)) :=
    hS (hmat ⟨b, hw.b_mem⟩)
  have hsMd : s * mat ⟨d, hw.d_mem⟩ = mat ⟨d, hw.d_mem⟩ * s :=
    (Subgroup.mem_center_iff.mp
      (TableB.scalars_le_center hs) (mat ⟨d, hw.d_mem⟩)).symm
  have hsMb : s * Mb = Mb * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalars_le_center hs) Mb).symm
  have hDpow : D ^ p = 1 := by
    have hsp : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) ((c⁻¹ : Kˣ) ^ p) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c⁻¹ p).symm
    rw [show D = s * mat ⟨d, hw.d_mem⟩ from rfl,
      Commute.mul_pow hsMd p, hsp, hc, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hcommD : Commute D Mb := by
    show D * Mb = Mb * D
    rw [show D = s * mat ⟨d, hw.d_mem⟩ from rfl]
    calc (s * mat ⟨d, hw.d_mem⟩) * Mb
        = s * (mat ⟨d, hw.d_mem⟩ * Mb) := by group
      _ = s * (Mb * mat ⟨d, hw.d_mem⟩) := by rw [← hcomm]
      _ = (s * Mb) * mat ⟨d, hw.d_mem⟩ := by group
      _ = (Mb * s) * mat ⟨d, hw.d_mem⟩ := by rw [hsMb]
      _ = Mb * (s * mat ⟨d, hw.d_mem⟩) := by group
  have hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin N) K) ⟨D, hDnorm⟩) := by
    have hsub : (⟨D, hDnorm⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) =
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) *
        ⟨mat ⟨d, hw.d_mem⟩, hS (hmat ⟨d, hw.d_mem⟩)⟩ := Subtype.ext rfl
    have hscalar : TableB.projConj (LargeEvenSLGroup (Fin N) K)
        (⟨s, TableB.scalar_mem_normalizer (LargeEvenSLGroup (Fin N) K) hs⟩ :
          Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K))) = 1 :=
      TableB.projConj_of_scalar (LargeEvenSLGroup (Fin N) K) hs
    rw [hsub, map_mul, hscalar, one_mul]
    exact hind ⟨d, hw.d_mem⟩
  exact hnonID (hLB G p L J A d b N n K hcard hw θ D Mb hDnorm hBnorm hDpow
    hcommD hDind (hind ⟨b, hw.b_mem⟩))

theorem uniTypeOne_commuting_of_wSetup (hUB : UniBlockInnDiag)
    {G : Type} [Group G] [Finite G] {p N n : ℕ} {L J A : Subgroup G} {d b : G}
    {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hN : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2))
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K N)}
    {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K N)) (LargeEvenGUSet (Fin N) K (2 ^ n)),
      LargeEvenInduces θ (conjRel a) φ}
    {hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆ Subgroup.normalizer
      (unitarySU 2 n K N : Set (GL (Fin N) K))}
    (hw : WSetup p L J A d b)
    (hnonID : ¬ InnDiagOn p (Subgroup.zpowers b) J)
    (M : LiftMap (L := L) (A := A) (S := LargeEvenGUSet (Fin N) K (2 ^ n)) θ hact hS)
    (hc : ∃ c : Kˣ, (M.mat ⟨d, hw.d_mem⟩) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p))
    (hcomm : M.mat ⟨b, hw.b_mem⟩ * M.mat ⟨d, hw.d_mem⟩ =
      M.mat ⟨d, hw.d_mem⟩ * M.mat ⟨b, hw.b_mem⟩) : False := by
  classical
  obtain ⟨c, hc⟩ := hc
  obtain ⟨mat, hmat, hind⟩ := M
  let s : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹
  let D : GL (Fin N) K := s * mat ⟨d, hw.d_mem⟩
  let Mb : GL (Fin N) K := mat ⟨b, hw.b_mem⟩
  have hs : s ∈ LargeEvenScalars (Fin N) K := by
    rw [largeEvenScalars_def]
    exact ⟨c⁻¹, rfl⟩
  have hDgu : D ∈ LargeEvenGUSet (Fin N) K (2 ^ n) :=
    scalar_mul_mem_guSet h (hmat ⟨d, hw.d_mem⟩) c⁻¹
  have hBgu : Mb ∈ LargeEvenGUSet (Fin N) K (2 ^ n) := hmat ⟨b, hw.b_mem⟩
  have hDnorm : D ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer h hDgu
  have hBnorm : Mb ∈ Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K)) :=
    hS hBgu
  have hsMd : s * mat ⟨d, hw.d_mem⟩ = mat ⟨d, hw.d_mem⟩ * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center c⁻¹)
      (mat ⟨d, hw.d_mem⟩)).symm
  have hsMb : s * Mb = Mb * s :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center c⁻¹) Mb).symm
  have hDpow : D ^ p = 1 := by
    have hsp : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) ((c⁻¹ : Kˣ) ^ p) :=
      (map_pow (Matrix.GeneralLinearGroup.scalar (Fin N)) c⁻¹ p).symm
    rw [show D = s * mat ⟨d, hw.d_mem⟩ from rfl,
      Commute.mul_pow hsMd p, hsp, hc, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hcommD : Commute D Mb := by
    show D * Mb = Mb * D
    rw [show D = s * mat ⟨d, hw.d_mem⟩ from rfl]
    calc (s * mat ⟨d, hw.d_mem⟩) * Mb
        = s * (mat ⟨d, hw.d_mem⟩ * Mb) := by group
      _ = s * (Mb * mat ⟨d, hw.d_mem⟩) := by rw [← hcomm]
      _ = (s * Mb) * mat ⟨d, hw.d_mem⟩ := by group
      _ = (Mb * s) * mat ⟨d, hw.d_mem⟩ := by rw [hsMb]
      _ = Mb * (s * mat ⟨d, hw.d_mem⟩) := by group
  have hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (unitarySU 2 n K N) ⟨D, hDnorm⟩) := by
    have hsub : (⟨D, hDnorm⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) =
        (⟨s, TableB.scalar_mem_normalizer (unitarySU 2 n K N) hs⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) *
        ⟨mat ⟨d, hw.d_mem⟩, hS (hmat ⟨d, hw.d_mem⟩)⟩ := Subtype.ext rfl
    have hscalar : TableB.projConj (unitarySU 2 n K N)
        (⟨s, TableB.scalar_mem_normalizer (unitarySU 2 n K N) hs⟩ :
          Subgroup.normalizer (unitarySU 2 n K N : Set (GL (Fin N) K))) = 1 :=
      TableB.projConj_of_scalar (unitarySU 2 n K N) hs
    rw [hsub, map_mul, hscalar, one_mul]
    exact hind ⟨d, hw.d_mem⟩
  exact hnonID (hUB G p L J A d b N n K h hN hNq hw θ D Mb hDgu hBgu hDnorm
    hBnorm hDpow hcommD hDind (hind ⟨b, hw.b_mem⟩))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
