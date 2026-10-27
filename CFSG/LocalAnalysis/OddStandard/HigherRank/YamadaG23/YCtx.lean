module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def zt (s : Setting3 G L) : Subgroup G := closure {s.fr.z, s.t}

@[expose] def C0 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := centIn e.T₁ s.fr.A

@[expose] def BranchA {s : Setting3 G L} (e : Setting3.Ext s) : Prop := C0 e = zt s

@[expose] def C1 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := s.fr.A ⊔ C0 e

@[expose] def M2 (s : Setting3 G L) : Subgroup G := ⁅s.C₂, normIn L s.fr.B⁆ ⊔ s.fr.B

@[expose] def R2 (s : Setting3 G L) : Subgroup G := s.R ⊔ M2 s

@[expose] def C3 (s : Setting3 G L) : Subgroup G :=
  pCoreOf 2 ⁅centIn (normalizer ((s.fr.F ⊔ zpowers s.t : Subgroup G) : Set G)) s.fr.F,
    normIn s.H s.fr.F⁆ ⊔ (s.fr.F ⊔ zpowers s.t)

@[expose] def M3 (s : Setting3 G L) : Subgroup G := ⁅C3 s, normIn L s.fr.F⁆ ⊔ s.fr.F

@[expose] def S3 (s : Setting3 G L) : Subgroup G := s.fr.S ⊔ M3 s

@[expose] def R3 (s : Setting3 G L) : Subgroup G := s.R ⊔ M3 s

@[expose] def C4 (s : Setting3 G L) : Subgroup G :=
  pCoreOf 2 ⁅centIn (normalizer ((s.fr.E ⊔ zpowers s.t : Subgroup G) : Set G)) s.fr.E,
    normIn s.H s.fr.E⁆ ⊔ (s.fr.E ⊔ zpowers s.t)

@[expose] def V1 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := C0 e ⊓ M3 s

@[expose] def AV1 {s : Setting3 G L} (e : Setting3.Ext s) : Subgroup G := s.fr.A ⊔ V1 e

@[expose] def IsQuotIso (N C : Subgroup G) (Q : Type) [Group Q] : Prop :=
  C ≤ N ∧ ∃ φ : ↥N →* Q, Function.Surjective φ ∧ φ.ker = C.subgroupOf N

@[expose] def blockStab : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {σ | ∀ i j : Fin 6, i.val / 3 = j.val / 3 ↔ (σ i).val / 3 = (σ j).val / 3}
  mul_mem' := by
    intro a b ha hb i j
    exact (hb i j).trans (ha (b i) (b j))
  one_mem' := by
    intro i j
    exact Iff.rfl
  inv_mem' := by
    intro a ha i j
    have h := ha (a⁻¹ i) (a⁻¹ j)
    simpa using h.symm

structure Intro5 {s : Setting3 G L} (e : Setting3.Ext s) (d : G) : Prop where
  centT : centIn s.T s.fr.A = zt s
  dihedral : Nonempty (↥(C0 e) ≃* DihedralGroup 4)
  eq_R1 : C0 e = centIn e.R₁ s.fr.A
  gen : C0 e = closure {s.t, d}
  eStar : maxElemAbelian (C0 e) = {zt s, closure {s.fr.z, d}}
  R1_eq : e.R₁ = s.R ⊔ zpowers d

variable (G L) in
structure Ctx5pre where
  s : Setting3 G L
  e : Setting3.Ext s
  notA : ¬ BranchA e
  d : G
  d_mem : d ∈ C0 e
  d_order : orderOf d = 2
  d_not_mem : d ∉ zt s
  intro5 : Intro5 e d

variable (G L) in
structure Ctx5 extends Ctx5pre G L where
  g : G
  g_spec : s.R ≠ s.T →
    g ∈ s.T ∧ g ∉ s.R ∧ ActsAs L g s.fr'.σ ∧ g ^ 2 = 1 ∧ g * d * g⁻¹ = d

variable (G L) in
structure Ctx6 extends Ctx5 G L where
  hV : V1 e = zpowers (d * s.t)

variable (G L) in
structure Ctx7 extends Ctx5 G L where
  hV : V1 e = closure {s.fr.z, d}

end CFSG.OddStandard.HigherRank.YamadaG23
