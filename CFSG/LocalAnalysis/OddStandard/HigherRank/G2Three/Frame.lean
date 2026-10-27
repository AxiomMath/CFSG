module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GH74.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1

open Subgroup CFSG.Open
open scoped commutatorElement

structure SFrame (Γ : Type) [Group Γ] where
  u₁ : Γ
  b₁ : Γ
  u₂ : Γ
  b₂ : Γ
  h₀ : Γ

structure Frame (Γ : Type) [Group Γ] extends SFrame Γ where
  σ : Γ

namespace SFrame

variable {Γ : Type} [Group Γ] (fr : SFrame Γ)

@[expose] def a₁ : Γ := fr.u₁ * fr.b₁ ^ 3 * fr.u₁⁻¹

@[expose] def a₂ : Γ := fr.u₂ * fr.b₂ ^ 3 * fr.u₂⁻¹

@[expose] def z : Γ := fr.b₁ ^ 2

@[expose] def Z : Subgroup Γ := zpowers fr.z

@[expose] def S : Subgroup Γ := closure {fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀}

@[expose] def A : Subgroup Γ := closure {fr.a₁, fr.b₁, fr.a₂, fr.b₂}

@[expose] def B : Subgroup Γ := centIn fr.S (closure {fr.b₁ * fr.b₂})

@[expose] def E : Subgroup Γ := closure {fr.b₁ * fr.b₂, fr.a₁ * fr.b₁ * fr.a₂, fr.z}

@[expose] def F : Subgroup Γ := closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z}

@[expose] def K₁ : Subgroup Γ := closure {fr.u₁, fr.b₁}

@[expose] def K₂ : Subgroup Γ := closure {fr.u₂, fr.b₂}

@[expose] def X₁ : Subgroup Γ := zpowers fr.u₁

@[expose] def X₂ : Subgroup Γ := zpowers fr.u₂

end SFrame

namespace Frame

variable {Γ : Type} [Group Γ] (fr : Frame Γ)

@[expose] def Sσ : Subgroup Γ := closure {fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ}

end Frame

@[expose] def innerAut (Q : Type) [Group Q] : Subgroup (MulAut Q) :=
  (MulAut.conj : Q →* MulAut Q).range

end CFSG.OddStandard.HigherRank.G2Three.Sec1
