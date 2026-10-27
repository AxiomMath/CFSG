module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Disc3
open scoped MatrixGroups

section Final


@[expose] def NotAllTypeTwoOfS3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6Three Ω K S R z →
      ∀ W ∈ WSet Ω, MuIsoS3 Ω W → ¬ AllTypeTwo K z

theorem dataOfStd6Three_of (hmu : NotAllTypeTwoOfS3) : DataOfStd6Three := by
  intro G _ _ _ Ω K S R z hstd W hW hWS hS3
  have hΩ : Ω = CoreAssembly.conjClass K := hstd.eq_conjClass
  have hW' : W ∈ WSet (CoreAssembly.conjClass K) := hΩ ▸ hW
  exact ⟨hstd.tight, hmu G Ω K S R z hstd W hW hS3, hstd.cex, hstd.exists_sylow_le,
    hstd.le_centralizer, hW', hWS⟩

structure Thm6Open3 : Prop where
  notAllTypeTwo : NotAllTypeTwoOfS3
  mu : C19_2Three
  sd : C19_4Three
  e2 : C19_11b3 → C19_E2Prime3

theorem Thm6Open3.toLayer (L : Thm6Open3) : Thm6Layer3 where
  data := dataOfStd6Three_of L.notAllTypeTwo
  mu := L.mu
  sd := L.sd
  e2 := L.e2

theorem thm6A3_of_open3 (L : Thm6Open3) (h : C19_11b3) : Thm6A3 :=
  thm6A3_of_c19_11b3 L.toLayer h

end Final

end CFSG.ClassicalInvolution.Q3.Q3T6
