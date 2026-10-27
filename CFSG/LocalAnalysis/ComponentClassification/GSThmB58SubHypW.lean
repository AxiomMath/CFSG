module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

structure Hyp52W (H : Type) [Group H] [Finite H] where
  a : H
  J : Subgroup H
  S : Subgroup H
  B : Subgroup H
  K : Subgroup H
  x : H
  kProper : Assembly.KProper Blueprint.Catalog H
  kGroup_normalizer : SectionRank.IsKGroupCat ↥(normalizer (B : Set H))
  normalizer_ne_top : normalizer (B : Set H) ≠ ⊤
  orderOf_a : orderOf a = 2
  J_le : J ≤ centralizer ({a} : Set H)
  isPComponent_J : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H)))
  smallType : SmallType J
  S_le : S ≤ centralizer ({a} : Set H) ⊓ normalizer (J : Set H)
  S_sylow : ∃ R : Sylow 2 ↥(centralizer ({a} : Set H) ⊓ normalizer (J : Set H)),
    (R : Subgroup _) = S.subgroupOf (centralizer ({a} : Set H) ⊓ normalizer (J : Set H))
  B_le : B ≤ S ⊓ coreActionKernel J
  B_ne_bot : B ≠ ⊥
  a_mem_normalizer : a ∈ normalizer (B : Set H)
  isComponent_bar : wbarImage B (GSLit.fixedLayer J B) ≤
      centralizer ({wbarMk B ⟨a, a_mem_normalizer⟩} : Set (Wbar B)) ∧
    IsComponent ((wbarImage B (GSLit.fixedLayer J B)).subgroupOf
      (centralizer ({wbarMk B ⟨a, a_mem_normalizer⟩} : Set (Wbar B))))
  isStandard_bar : IsStandardSubgroup (wbarImage B (GSLit.fixedLayer J B))
  conjClosure_eq : conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set H))) =
    layerIn (normalizer (B : Set H))
  commutator_eq : ⁅layerIn (normalizer (B : Set H)), zpowers a⁆ =
    layerIn (normalizer (B : Set H))
  B_le_kernel : B ≤ normalizer (B : Set H) ⊓ coreActionKernel (layerIn (normalizer (B : Set H)))
  B_sylow_kernel : ∃ R : Sylow 2 ↥(normalizer (B : Set H) ⊓
      coreActionKernel (layerIn (normalizer (B : Set H)))),
    (R : Subgroup _) = B.subgroupOf
      (normalizer (B : Set H) ⊓ coreActionKernel (layerIn (normalizer (B : Set H))))
  isoCorr_of_le_T : ∀ E : Subgroup H, E ≤ S ⊓ coreActionKernel J ⊓ normalizer (B : Set H) →
    Nat.card B < Nat.card E → ∃ L : Subgroup H, IsoCorrSub a J E L
  isoCorr_of_mem : ∀ E : Subgroup H, E ≤ S ⊓ coreActionKernel J → a ∈ E →
    ∃ L : Subgroup H, IsoCorrSub a J E L
  x_mem : x ∈ S
  inf_conjugate_x : B ⊓ conjugate B x = ⊥
  x_sq_mem : x ^ 2 ∈ S ⊓ coreActionKernel J ⊓ normalizer (B : Set H)
  sylow_layer : ∃ R : Subgroup H, R ≤ S ⊓ normalizer (B : Set H) ∧
    R ≤ layerIn (normalizer (B : Set H)) ⊓
      normalizer ((GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set H)) : Subgroup H) :
        Set H) ∧
    ∃ R' : Sylow 2 ↥(layerIn (normalizer (B : Set H)) ⊓
      normalizer ((GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set H)) : Subgroup H) :
        Set H)),
      (R' : Subgroup _) = R.subgroupOf (layerIn (normalizer (B : Set H)) ⊓
        normalizer ((GSLit.fixedLayer J B ⊔ oddCoreIn (normalizer (B : Set H)) : Subgroup H) :
          Set H))
  isPComponent_K : K ≤ normalizer (B : Set H) ∧
    IsPComponent 2 (K.subgroupOf (normalizer (B : Set H)))
  layer_eq_K : K ⊔ conjugate K a = layerIn (normalizer (B : Set H))
  type_K : GSRestricted (K ⧸ Open.fusionZStar K) ∨
    (conjugate K a ≠ K ∧ Nonempty (K ⧸ Open.fusionZStar K ≃* J ⧸ Open.fusionZStar J))

namespace Hyp52W

variable {H : Type} [Group H] [Finite H] (h : Hyp52W H)

abbrev P : Subgroup H := h.S ⊓ coreActionKernel h.J

abbrev Q : Subgroup H := h.S ⊓ normalizer (h.B : Set H)

abbrev T : Subgroup H := h.Q ⊓ h.P

end Hyp52W

structure Hyp59W (H : Type) [Group H] [Finite H] extends Hyp52W H where
  oddCore_eq_bot : pPrimeCore 2 H = ⊥
  x_cond : x ∈ toHyp52W.P ⊓ normalizer (toHyp52W.Q : Set H) ∨
    (toHyp52W.P ≤ toHyp52W.Q ∧ x ^ 2 = 1)

end CFSG.ComponentClassification.GSThmB
