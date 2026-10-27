module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Gen
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup
open scoped MatrixGroups

namespace Ivk95Cfg

variable {J : Type} [Group J] [Finite J] {z : J}

theorem false_of_sl2_in_centralizer (h : Ivk95Cfg z) {I : Subgroup ↥(centralizer ({z} : Set J))}
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (e : ↥I ≃* SL(2, F))
    (hI : ∀ a ∈ I, ∀ b ∈ (Ez z).subgroupOf (centralizer ({z} : Set J)), a * b = b * a) :
    False := by
  refine h.false_of_sl2_centralizing hodd (I := I.map (centralizer ({z} : Set J)).subtype)
    (e.symm.trans (I.equivMapOfInjective _ (centralizer ({z} : Set J)).subtype_injective)) ?_
  rintro _ ⟨a, ha, rfl⟩ k hk
  have hkC : k ∈ centralizer ({z} : Set J) := h.le_cent hk
  have hak := hI a ha ⟨k, hkC⟩ (Subgroup.mem_subgroupOf.mpr hk)
  exact congrArg Subtype.val hak

theorem false_of_shape (h : Ivk95Cfg z) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂))
    (S : Ivk47ab.Shape ↥(centralizer ({z} : Set J)) F₁ F₂) : False := by
  rcases CFSG.LocalCores.component_normal_subgroup h.isComponent (GHInv.normal_I₂ S) with hle | hbot
  · exact h.false_of_sl2_in_centralizer hodd₁ S.e₁ fun a ha b hb => S.comm a ha b (hle hb)
  · have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact h.false_of_sl2_in_centralizer hodd₂ S.e₂ fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp (hc hb) a ha

end Ivk95Cfg

end CFSG.GH74.GLS.IVK.Proofs2
