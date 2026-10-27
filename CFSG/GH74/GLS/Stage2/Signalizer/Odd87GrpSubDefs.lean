module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

variable {A : Type} [Group A]

@[expose] def secY (z : A) (X J : Subgroup A) : Subgroup A := J ⊔ X ⊔ zpowers z

theorem z_mem_secY (z : A) (X J : Subgroup A) : z ∈ secY z X J :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem X_le_secY (z : A) (X J : Subgroup A) : X ≤ secY z X J :=
  (le_sup_right : X ≤ J ⊔ X).trans (le_sup_left : J ⊔ X ≤ (J ⊔ X) ⊔ zpowers z)

theorem J_le_secY (z : A) (X J : Subgroup A) : J ≤ secY z X J :=
  (le_sup_left : J ≤ J ⊔ X).trans (le_sup_left : J ⊔ X ≤ (J ⊔ X) ⊔ zpowers z)

abbrev secB (z : A) (X J : Subgroup A) : Type := ↥(secY z X J) ⧸ pPrimeCore 2 ↥(secY z X J)

@[expose] def secZ (z : A) (X J : Subgroup A) : secB z X J := QuotientGroup.mk ⟨z, z_mem_secY z X J⟩

@[expose] def secX (z : A) (X J : Subgroup A) : Subgroup (secB z X J) :=
  (X.subgroupOf (secY z X J)).map (QuotientGroup.mk' _)

@[expose] def secJ (z : A) (X J : Subgroup A) : Subgroup (secB z X J) :=
  (J.subgroupOf (secY z X J)).map (QuotientGroup.mk' _)

structure SubHyp [Finite A] (z : A) (p : ℕ) (X J : Subgroup A) : Prop where
  A4 : Sig4A z (⊤ : Subgroup A) p X
  z2 : z * z = 1
  comp : IsComponent J
  XJ : X ≤ normalizer (J : Set A)
  zJ : z ∈ normalizer (J : Set A)
  JX : ⁅J, X⁆ ≠ ⊥

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
