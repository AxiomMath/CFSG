module

public import CFSG.LocalAnalysis.ComponentInitial.TwoCentralizersGlobalInner
public import CFSG.Monster.B.Cbar.SylowControl
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric

public section

namespace CFSG.ComponentClassification.BMCase

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem global_inner_of_centralizer {x : G} (hx : orderOf x = 2) {Q : Subgroup G}
    (hQH : Q ≤ centralizer ({x} : Set G))
    (hQn : (Q.subgroupOf (centralizer ({x} : Set G))).Normal)
    (hQe : CFSG.IsExtraspecialPGroup 2 Q) (hZQ : (center Q).map Q.subtype = zpowers x)
    (hCQ : centralizer ({x} : Set G) ⊓ centralizer (Q : Set G) = zpowers x)
    (hker : ∀ h ∈ centralizer ({x} : Set G),
      (∀ q ∈ Q, h * q * h⁻¹ * q⁻¹ ∈ zpowers x) ↔ h ∈ Q)
    (hautH : ∀ β : MulAut (centralizer ({x} : Set G)), ∃ h, β = MulAut.conj h)
    {t : G} (hyQ : t * x * t⁻¹ ∈ Q) (hyx : t * x * t⁻¹ ∉ zpowers x)
    (hgen : closure ((centralizer ({x} : Set G) : Set G) ∪ {t}) = ⊤)
    {h : G} (hh : h ∈ centralizer ({x} : Set G)) (ht : h * (t * h * t⁻¹) = t) :
    ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsyl, -⟩ := CFSG.Monster.B.prime_centralizer_sylow_control hx hQH hQn hQe.1 hZQ hCQ
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 (centralizer ({x} : Set G))))
  obtain ⟨T, -, hT⟩ := hsyl P
  have hyQ' : t⁻¹⁻¹ * x * t⁻¹ ∈ Q := by rwa [inv_inv]
  have hyx' : t⁻¹⁻¹ * x * t⁻¹ ∉ zpowers x := by rwa [inv_inv]
  have hgen' : centralizer ({x} : Set G) ⊔ centralizer ({t⁻¹⁻¹ * x * t⁻¹} : Set G) = ⊤ := by
    rw [inv_inv]
    exact centralizer_sup_centralizer_conj_eq_top hgen hh ht
  exact CFSG.LocalAnalysis.ComponentInitial.two_centralizers_force_global_inner_automorphisms hx
    T hT hQH hQn hQe hZQ hker hautH hyQ' hyx' hgen'

end CFSG.ComponentClassification.BMCase
