module

public import Certificates.Certificate442010
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkSound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

namespace Pk

abbrev tA : P45 := Certificates.P43Twin.tA ()

abbrev tB : P45 := Certificates.P43Twin.tB ()

abbrev gz : P45 := Certificates.OmegaPk.g0 ()

abbrev P0 : Subgroup P45 := QP45.originalSubgroup

abbrev Cs : Subgroup P45 := P0 ⊓ centralizer ({tA} : Set P45)

abbrev CBs : Subgroup P45 := P0 ⊓ centralizer ({tB} : Set P45)

abbrev Cl : List P45 := Certificates.OmegaPk.clA ()

abbrev CBl : List P45 := Certificates.OmegaPk.clB ()

abbrev Sl : List SL23 := Certificates.OmegaPk.allSL ()

abbrev rhoF : SL23 → P45 := Certificates.OmegaPk.rhoOf (Certificates.OmegaPk.rhoTab ())

abbrev Q1l : List P45 := Certificates.P43Twin.Q1 ()

abbrev Q2l : List P45 := Certificates.P43Twin.Q2 ()

theorem facts : Certificates.OmegaPk.Facts :=
  Certificates.certificate442010

theorem mem_Sl : ∀ A : SL23, A ∈ Sl := by decide +kernel

theorem rho_props :
    (∀ A B : SL23, rhoF (A * B) = rhoF A * rhoF B) ∧ (∀ A : SL23, rhoF A = 1 → A = 1) ∧
      (∀ A : SL23, rhoF A ∈ P0) ∧ (∀ A : SL23, rhoF A * tA = tA * rhoF A) ∧
      ∃ A : SL23, rhoF A = tA :=
  facts.rho

theorem rho_hom :
    ∀ A B : SL23, rhoF (A * B) = rhoF A * rhoF B :=
  facts.rho.1

@[expose] def rho : SL23 →* P45 := MonoidHom.mk' rhoF rho_hom

theorem rho_apply (A : SL23) : rho A = rhoF A := rfl

@[expose] def KA : Subgroup P45 := (rho).range

@[expose] def KB : Subgroup P45 := CFSG.conjugate KA gz

theorem mem_KA {x : P45} : x ∈ KA ↔ ∃ A : SL23, rhoF A = x := by
  simp only [KA, MonoidHom.mem_range, rho_apply]

theorem mem_KB {x : P45} :
    x ∈ KB ↔ ∃ A : SL23, Certificates.OmegaPk.cj gz (rhoF A) = x := by
  rw [KB, CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨A, rfl⟩ := mem_KA.1 hy
    exact ⟨A, by simp [Certificates.OmegaPk.cj, MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨A, rfl⟩
    exact ⟨rhoF A, mem_KA.2 ⟨A, rfl⟩, by simp [Certificates.OmegaPk.cj, MulAut.conj_apply,
      mul_assoc]⟩

end Pk

end CFSG.OddStandard.SmallF3.Omega
