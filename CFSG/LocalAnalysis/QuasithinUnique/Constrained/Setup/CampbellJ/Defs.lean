module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMnorm

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] {k : Type*} [Field k]

structure PartnerCoreJ (S Fp Zp : Subgroup G) : Prop where
  normal : ∀ s ∈ CFSG.Quasithin.thompsonJ S, ∀ x ∈ Fp, s * x * s⁻¹ ∈ Fp
  zcentral : ∀ s ∈ CFSG.Quasithin.thompsonJ S, ∀ z ∈ Zp, s * z = z * s
  commJ : ⁅CFSG.Quasithin.thompsonJ S, Fp⁆ = Zp
  commA : ∀ A, CFSG.Quasithin.IsMaxElemAbelian S A → ⁅A, Fp⁆ = ⊥ ∨ ⁅A, Fp⁆ = Zp
  sup_max : ∀ A, CFSG.Quasithin.IsMaxElemAbelian S A →
    CFSG.Quasithin.IsMaxElemAbelian S (Fp ⊔ (A ⊓ Subgroup.centralizer (Fp : Set G)))

structure LamHyp (S : Sylow 2 G)
    (Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))) : Prop where
  inner : ∀ x ∈ (S : Subgroup G) ⊓ Hone S, ∃ β ∈ Λ,
    ∀ y : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)),
      ((β y : ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : G) = x⁻¹ * y * x
  vmod : ∀ β ∈ Λ,
    aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) β (Vmod G) ≤ CFSG.pCore 2 G

@[expose] def WJ (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) : Subgroup G :=
  ⨆ u ∈ Hone S, cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u

@[expose] def B0J (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (A : Subgroup G) : Subgroup G :=
  Fcore G ⊔ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ⊔
    (A ⊓ Subgroup.centralizer ((Fcore G ⊔
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) : Subgroup G) : Set G))

@[expose] def PminusJ (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) : Subgroup G :=
  cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm (Fcore G)) g

@[expose] def BbJ (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (A : Subgroup G) (g : G) :
    Subgroup G :=
  PminusJ S α g ⊔ (B0J S α A ⊓ Subgroup.centralizer ((PminusJ S α g : Subgroup G) : Set G))

@[expose] def YsubJ (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (g : G) : Subgroup G :=
  cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α.symm
    (cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) g)) g

structure DoubleSetupJ (S : Sylow 2 G) (ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k)
    (ψ : Ecore G →* Multiplicative (Fin 2 → k))
    (Λ : Subgroup (MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))))
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) (A : Subgroup G) (g : G) :
    Prop where
  seed : IsSeed S ρ (Ecore G) ψ
  lam : LamHyp S Λ
  hαΛ : α ∈ Λ
  hα : ¬ ⁅Hone S, aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ ≤ Fcore G
  hA : CFSG.Quasithin.IsMaxElemAbelian (S : Subgroup G) A
  hAQ : ¬ A ≤ CFSG.pCore 2 G
  hgH : g ∈ Hone S
  hgM : g ∉ Mnorm S ρ
  hg2 : g * g = 1

end CFSG.QuasithinUnique.Setup.CampbellJ

end
