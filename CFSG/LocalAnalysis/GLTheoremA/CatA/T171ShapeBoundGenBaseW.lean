module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeWSetup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L J A : Subgroup G} {d b : G} {p N n : ℕ}
variable {K : Type} [Field K] [Finite K]
variable {H : Subgroup (GL (Fin N) K)} {S : Set (GL (Fin N) K)}
variable {θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj H}
variable {hact : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) S,
  LargeEvenInduces θ (conjRel a) φ}
variable {hS : S ⊆ Subgroup.normalizer (H : Set (GL (Fin N) K))}

theorem LiftMap.d_pow_eq_one_of_wSetup (hw : WSetup p L J A d b) : d ^ p = 1 :=
  (WSetup.elem hw).2 d hw.d_mem

theorem LiftMap.automorphisms_commute_of_wSetup (M : LiftMap (L := L) (A := A) θ hact hS)
    (hw : WSetup p L J A d b) (a : ↥A) :
    TableB.projConj H ⟨M.mat a, hS (M.mem a)⟩ *
        TableB.projConj H ⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩ =
      TableB.projConj H ⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩ *
        TableB.projConj H ⟨M.mat a, hS (M.mem a)⟩ := by
  have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hw.idiag
  have hcomm : (a : G) * d = d * (a : G) :=
    IsElemAbelian.comm (WSetup.elem hw) a.2 hw.d_mem
  have h1 : LargeEvenInduces θ (conjRel ((a : G) * d))
      (TableB.projConj H ⟨M.mat a, hS (M.mem a)⟩ *
        TableB.projConj H ⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩) :=
    largeEvenInduces_mul (hAnorm a.2) (hAnorm hw.d_mem) hcomm
      (M.ind a) (M.ind ⟨d, hw.d_mem⟩)
  have h2 : LargeEvenInduces θ (conjRel (d * (a : G)))
      (TableB.projConj H ⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩ *
        TableB.projConj H ⟨M.mat a, hS (M.mem a)⟩) :=
    largeEvenInduces_mul (hAnorm hw.d_mem) (hAnorm a.2) hcomm.symm
      (M.ind ⟨d, hw.d_mem⟩) (M.ind a)
  rw [hcomm] at h1
  exact largeEvenInduces_unique h1 h2
    (conjRel_total (hAnorm (by exact A.mul_mem hw.d_mem a.2)))

theorem LiftMap.commutator_mem_scalars_of_wSetup (M : LiftMap (L := L) (A := A) θ hact hS)
    (hw : WSetup p L J A d b) (a : ↥A)
    (hker : ∀ (X : Subgroup.normalizer (H : Set (GL (Fin N) K))),
      TableB.projConj H X = 1 → (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K) :
    M.mat a * M.mat ⟨d, hw.d_mem⟩ * (M.mat a)⁻¹ * (M.mat ⟨d, hw.d_mem⟩)⁻¹ ∈
      LargeEvenScalars (Fin N) K := by
  let X : Subgroup.normalizer (H : Set (GL (Fin N) K)) := ⟨M.mat a, hS (M.mem a)⟩
  let Y : Subgroup.normalizer (H : Set (GL (Fin N) K)) :=
    ⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩
  have hcomm : TableB.projConj H X * TableB.projConj H Y =
      TableB.projConj H Y * TableB.projConj H X :=
    M.automorphisms_commute_of_wSetup hw a
  have hmul : TableB.projConj H (X * Y * X⁻¹ * Y⁻¹) =
      TableB.projConj H X * TableB.projConj H Y * (TableB.projConj H X)⁻¹ *
        (TableB.projConj H Y)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  have hcone : TableB.projConj H (X * Y * X⁻¹ * Y⁻¹) = 1 := by
    rw [hmul, hcomm]
    group
  have h := hker (X * Y * X⁻¹ * Y⁻¹) hcone
  simpa [X, Y] using h

theorem LiftMap.dpow_mem_scalars_of_wSetup (M : LiftMap (L := L) (A := A) θ hact hS)
    (hw : WSetup p L J A d b)
    (hker : ∀ (X : Subgroup.normalizer (H : Set (GL (Fin N) K))),
      TableB.projConj H X = 1 → (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K) :
    (M.mat ⟨d, hw.d_mem⟩) ^ p ∈ LargeEvenScalars (Fin N) K := by
  have hAnorm : A ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S11.le_normalizer_of_innerDiag hw.idiag
  have hD := M.ind ⟨d, hw.d_mem⟩
  have hpow := largeEvenInduces_pow (hAnorm hw.d_mem) hD p
  have hp : d ^ p = 1 := LiftMap.d_pow_eq_one_of_wSetup hw
  rw [hp] at hpow
  have hone : LargeEvenInduces θ (conjRel (1 : G)) (1 : MulAut (LargeEvenProj H)) :=
    largeEvenInduces_one (rel := conjRel (1 : G)) fun l l' hl => by
      have hl' : (l' : G) = (l : G) := by simpa [conjRel] using hl
      exact Subtype.ext hl'.symm
  have heq : (TableB.projConj H ⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩) ^ p = 1 :=
    largeEvenInduces_unique hpow hone (conjRel_total (Subgroup.one_mem _))
  have hproj : TableB.projConj H
      (⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩ ^ p) = 1 := by
    simpa only [map_pow] using heq
  have hval : (⟨M.mat ⟨d, hw.d_mem⟩, hS (M.mem ⟨d, hw.d_mem⟩)⟩ ^ p :
      Subgroup.normalizer (H : Set (GL (Fin N) K))) =
      ⟨(M.mat ⟨d, hw.d_mem⟩) ^ p,
        Subgroup.pow_mem _ (hS (M.mem ⟨d, hw.d_mem⟩)) p⟩ := Subtype.ext rfl
  rw [hval] at hproj
  exact hker _ hproj

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
