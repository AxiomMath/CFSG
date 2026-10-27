module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapLift

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G]

@[expose] noncomputable def Siggrp (ι : Perm (Fin 10) →* G) : Subgroup G := (ι.comp liftS8).range

@[expose] noncomputable def Agrp (ι : Perm (Fin 10) →* G) : Subgroup G :=
  (alternatingGroup (Fin 8)).map (ι.comp liftS8)

@[expose] def Egrp (z : G) (ι : Perm (Fin 10) →* G) : Subgroup G :=
  zpowers z ⊔ zpowers (ι τ₀)

@[expose] def CEgrp (z : G) (ι : Perm (Fin 10) →* G) : Subgroup G :=
  centralizer ({z} : Set G) ⊓ centralizer ({ι τ₀} : Set G)

@[expose] def Dgrp (z g : G) : Subgroup G := Subgroup.closure {z, g}

structure GElt (z : G) (ι : Perm (Fin 10) →* G) (g : G) : Prop where
  conj_z : g * z * g⁻¹ = ι τ₀
  conj_x₁ : g * ι τ₀ * g⁻¹ = z
  comm_A : ∀ ρ ∈ alternatingGroup (Fin 8), g * ι (liftS8 ρ) = ι (liftS8 ρ) * g
  sq : g * g = 1 ∨ g * g = z * ι τ₀
  e₀ : ∃ e₀ : G, (e₀ = 1 ∨ e₀ = z * ι τ₀) ∧ ∀ ρ : Perm (Fin 8),
    g * ι (liftS8 ρ) * g⁻¹ = ι (liftS8 ρ) * (if sign ρ = 1 then 1 else e₀)

end CFSG.OddStandard.AltStdSec.SwapPartner
