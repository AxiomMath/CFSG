module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBShell
public import CFSG.LocalAnalysis.ComponentClassification.GSLitFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def oddTwoCore (Y : Type*) [Group Y] : Subgroup Y :=
  (pCore 2 (Y ⧸ pPrimeCore 2 Y)).comap (QuotientGroup.mk' (pPrimeCore 2 Y))

instance oddTwoCore_normal (Y : Type*) [Group Y] : (oddTwoCore Y).Normal := by
  unfold oddTwoCore pCore
  have : (sSup {K : Subgroup (Y ⧸ pPrimeCore 2 Y) | K.Normal ∧ IsPGroup 2 K}).Normal :=
    Subgroup.sSup_normal _ fun _ hK => hK.1
  exact Subgroup.normal_comap _

variable {H : Type*} [Group H]

@[expose] def oddCoreIn (X : Subgroup H) : Subgroup H :=
  (pPrimeCore 2 X).map X.subtype

@[expose] def layerIn (X : Subgroup H) : Subgroup H :=
  (pLayer X 2).map X.subtype

@[expose] def conjClosure (T Y : Subgroup H) : Subgroup H :=
  ⨆ y ∈ Y, conjugate T y

@[expose] def IsoCorrSub (a : H) (J E L : Subgroup H) : Prop :=
  L ≤ normalizer (E : Set H) ∧ IsPComponent 2 (L.subgroupOf (normalizer (E : Set H))) ∧
    conjugate L a = L ∧ GSLit.fixedLayer J E ⊔ oddCoreIn L = L ∧
    GSLit.fixedLayer J E = layerIn (L ⊓ centralizer ({a} : Set H))

abbrev Wbar (B : Subgroup H) : Type _ :=
  ↥(normalizer (B : Set H)) ⧸ oddTwoCore ↥(normalizer (B : Set H))

abbrev wbarMk (B : Subgroup H) : ↥(normalizer (B : Set H)) →* Wbar B :=
  QuotientGroup.mk' (oddTwoCore ↥(normalizer (B : Set H)))

abbrev wbarImage (B Y : Subgroup H) : Subgroup (Wbar B) :=
  (Y.subgroupOf (normalizer (B : Set H))).map (wbarMk B)

structure Hyp52 (H : Type) [Group H] [Finite H] where
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
  isoCorr_of_lt : ∀ E : Subgroup H, E ≤ S ⊓ coreActionKernel J →
    (Nat.card B < Nat.card E ∨ (Nat.card E = Nat.card B ∧
      Nat.card ↥(S ⊓ normalizer (B : Set H)) < Nat.card ↥(S ⊓ normalizer (E : Set H)))) →
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

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

abbrev P : Subgroup H := h.S ⊓ coreActionKernel h.J

abbrev W : Subgroup H := normalizer (h.B : Set H)

abbrev Q : Subgroup H := h.S ⊓ normalizer (h.B : Set H)

abbrev T : Subgroup H := h.Q ⊓ h.P

abbrev D : Subgroup H := h.S ⊓ h.J

abbrev V : Subgroup H := layerIn (normalizer (h.B : Set H))

end Hyp52

structure Hyp59 (H : Type) [Group H] [Finite H] extends Hyp52 H where
  oddCore_eq_bot : pPrimeCore 2 H = ⊥
  x_cond : x ∈ toHyp52.P ⊓ normalizer (toHyp52.Q : Set H) ∨
    (toHyp52.P ≤ toHyp52.Q ∧ x ^ 2 = 1)

end CFSG.ComponentClassification.GSThmB
