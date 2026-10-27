
module

public import CFSG.GH74.GLS.C3.Prop121.MooreFiniteBase

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Perm.Sign
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.Data.Fintype.Perm
public import CFSG.GH74.GLS.C3.Prop121.MooreFiniteInputs
public meta import CFSG.GH74.GLS.C3.Prop121.MooreFiniteInputs
public import Certificates.Certificate5093

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Equiv Perm

theorem searchAll5_true : searchAll5 a4C5 oddC5 evenC5 :=
  Certificates.certificate5093.1

theorem moore_finite_five
    (c : Perm (Fin 6)) (hc : c = cEnd5) (s1 sg s2 s3 : Perm (Fin 6))
    (h1 : s1 * s1 = 1 ∧ sign s1 = 1 ∧ s1 ≠ 1 ∧ (c * s1) ^ 3 = 1)
    (hs : sg * sg = 1 ∧ sign sg = -1 ∧ sg * c * sg⁻¹ = c⁻¹ ∧ sg * s1 = s1 * sg)
    (h2 : s2 * s2 = 1 ∧ sign s2 = 1 ∧ s2 * c * s2⁻¹ = c⁻¹ ∧ sg * s2 = s2 * sg)
    (h3 : s3 * s3 = 1 ∧ sign s3 = 1 ∧ s3 * c * s3⁻¹ = c⁻¹ ∧ sg * s3 = s3 * sg ∧
      s3 * s1 = s1 * s3 ∧ (s2 * s3) ^ 3 = 1 ∧ s2 ≠ s3) :
    (s1 * s2) ^ 3 = 1 := by
  subst hc
  have e2 : s2 ∈ evenC5.filter fun s => sg * s = s * sg :=
    Finset.mem_filter.2 ⟨mem_evenC5.2 ⟨h2.1, h2.2.1, h2.2.2.1⟩, h2.2.2.2⟩
  have e3 : s3 ∈ (evenC5.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s :=
    Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_evenC5.2 ⟨h3.1, h3.2.1, h3.2.2.1⟩, h3.2.2.2.1⟩,
      h3.2.2.2.2.1⟩
  exact searchAll5_true s1 (mem_a4C5.2 h1) sg (mem_oddC5.2 ⟨hs.1, hs.2.1, hs.2.2.1⟩) hs.2.2.2
    s2 e2 s3 e3 h3.2.2.2.2.2.1 h3.2.2.2.2.2.2

theorem searchAll6_true : searchAll6 a4C6 oddC6 evenC6 :=
  Certificates.certificate5093.2

theorem moore_finite_six
    (c : Perm (Fin 7)) (hc : c = cEnd6) (s1 sg s2 s3 s4 : Perm (Fin 7))
    (h1 : s1 * s1 = 1 ∧ sign s1 = 1 ∧ s1 ≠ 1 ∧ (c * s1) ^ 3 = 1)
    (hs : sg * sg = 1 ∧ sign sg = -1 ∧ sg * c * sg⁻¹ = c⁻¹ ∧ sg * s1 = s1 * sg)
    (h2 : s2 * s2 = 1 ∧ sign s2 = 1 ∧ s2 * c * s2⁻¹ = c⁻¹ ∧ sg * s2 = s2 * sg)
    (h3 : s3 * s3 = 1 ∧ sign s3 = 1 ∧ s3 * c * s3⁻¹ = c⁻¹ ∧ sg * s3 = s3 * sg ∧
      s3 * s1 = s1 * s3 ∧ (s2 * s3) ^ 3 = 1 ∧ s2 ≠ s3)
    (h4 : s4 * s4 = 1 ∧ sign s4 = 1 ∧ s4 * c * s4⁻¹ = c⁻¹ ∧ sg * s4 = s4 * sg ∧
      s4 * s1 = s1 * s4 ∧ (s3 * s4) ^ 3 = 1 ∧ (s2 * s4) ^ 2 = 1 ∧ s2 ≠ s4) :
    (s1 * s2) ^ 3 = 1 := by
  subst hc
  have e2 : s2 ∈ evenC6.filter fun s => sg * s = s * sg :=
    Finset.mem_filter.2 ⟨mem_evenC6.2 ⟨h2.1, h2.2.1, h2.2.2.1⟩, h2.2.2.2⟩
  have e3 : s3 ∈ (evenC6.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s :=
    Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_evenC6.2 ⟨h3.1, h3.2.1, h3.2.2.1⟩, h3.2.2.2.1⟩,
      h3.2.2.2.2.1⟩
  have e4 : s4 ∈ (evenC6.filter fun s => sg * s = s * sg).filter fun s => s * s1 = s1 * s :=
    Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_evenC6.2 ⟨h4.1, h4.2.1, h4.2.2.1⟩, h4.2.2.2.1⟩,
      h4.2.2.2.2.1⟩
  exact searchAll6_true s1 (mem_a4C6.2 h1) sg (mem_oddC6.2 ⟨hs.1, hs.2.1, hs.2.2.1⟩) hs.2.2.2
    s2 e2 s3 e3 h3.2.2.2.2.2.1 h3.2.2.2.2.2.2 s4 e4 h4.2.2.2.2.2.1 h4.2.2.2.2.2.2.1
    h4.2.2.2.2.2.2.2

end CFSG.GH74.GLS.C3.Prop121
