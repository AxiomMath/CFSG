module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSecG
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecLiftAux
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

theorem SecOfG.exists_hom {G : Type} [Group G] [Finite G] {B : Type} [Group B] [Finite B]
    {z : G} {b : B} (h : SecOfG G z B b) :
    ∃ (H₀ : Subgroup G) (π : ↥H₀ →* B), H₀ ≠ ⊤ ∧ Function.Surjective π ∧
      Odd (Nat.card π.ker) ∧ ∃ hz : z ∈ H₀, π ⟨z, hz⟩ = b := by
  obtain ⟨H₀, H₁, hn, hz, hne, hodd, e, he⟩ := h
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' H₁)).ker = H₁ := by
    ext x
    simp
  refine ⟨H₀, e.toMonoidHom.comp (QuotientGroup.mk' H₁), hne,
    e.surjective.comp (QuotientGroup.mk'_surjective H₁), ?_, hz, he⟩
  rw [hker]
  exact hodd

section SecLift
variable {G : Type} [Group G] [Finite G] {B : Type} [Group B] [Finite B]

theorem exists_pcomp_lift {H₀ : Subgroup G} (π : ↥H₀ →* B) (hπ : Function.Surjective π)
    (hodd : Odd (Nat.card π.ker)) {J : Subgroup B} (hJ : IsComponent J) :
    ∃ Jt : Subgroup G, IsPCompIn 2 H₀ Jt ∧ (Jt.subgroupOf H₀).map π = J ∧
      Nonempty (Hat Jt ≃* Hat J) ∧
      ∀ x : ↥H₀, π x ∈ centralizer (J : Set B) →
        (x : G) ∈ centralizerSection Jt (pPrimeCoreOf 2 Jt) := by
  obtain ⟨L, hL, hLJ, ⟨e⟩, hcent⟩ := subsec_lift_pcomp π hπ hodd hJ
  have hsub : (L.map H₀.subtype).subgroupOf H₀ = L :=
    Subgroup.comap_map_eq_self_of_injective H₀.subtype_injective L
  refine ⟨L.map H₀.subtype, ⟨Subgroup.map_subtype_le L, ?_⟩, ?_, ?_, ?_⟩
  · rw [hsub]
    exact hL
  · rw [hsub]
    exact hLJ
  · let ψ : ↥L ≃* ↥(L.map H₀.subtype) := L.equivMapOfInjective H₀.subtype H₀.subtype_injective
    let e₁ : (↥L ⧸ pPrimeCore 2 ↥L) ≃* Hat (L.map H₀.subtype) :=
      QuotientGroup.congr _ _ ψ (pPrimeCore_map_iso 2 ψ)
    exact ⟨e₁.symm.trans e⟩
  · intro x hx
    exact subsec_map_mem_centralizerSection H₀.subtype H₀.subtype_injective L (hcent x hx)
end SecLift

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
