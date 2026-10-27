module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

section Config

variable {G : Type} [Group G]

structure L34PartnerConfig (V P Q : Subgroup G) : Prop where
  ne : Q ≠ P
  le_centralizer : P ≤ centralizer (Q : Set G)
  isQuasisimple_left : IsQuasisimple ↥P
  isQuasisimple_right : IsQuasisimple ↥Q
  odd_card_center_left : Odd (Nat.card (center ↥P))
  odd_card_center_right : Odd (Nat.card (center ↥Q))
  isL34Type_left : IsL34Type (↥P ⧸ center ↥P)
  isL34Type_right : IsL34Type (↥Q ⧸ center ↥Q)
  card_V : Nat.card V = 4
  mul_self : ∀ v ∈ V, v * v = 1
  le_centralizer_left : V ≤ centralizer (P : Set G)
  le_centralizer_right : V ≤ centralizer (Q : Set G)
  isComponent_left : ∀ v ∈ V, v ≠ 1 → P ≤ centralizer ({v} : Set G) ∧
    IsComponent (P.subgroupOf (centralizer ({v} : Set G)))
  isComponent_right : ∀ v ∈ V, v ≠ 1 → Q ≤ centralizer ({v} : Set G) ∧
    IsComponent (Q.subgroupOf (centralizer ({v} : Set G)))
  wGroup_left : ∀ I : Subgroup G, I ≤ P → Open.IsElemAbelian 2 I → 8 ≤ Nat.card I →
    wGroup I = ⊥
  wGroup_right : ∀ I : Subgroup G, I ≤ Q → Open.IsElemAbelian 2 I → 8 ≤ Nat.card I →
    wGroup I = ⊥

theorem L34PartnerConfig.symm {V P Q : Subgroup G} (h : L34PartnerConfig V P Q) :
    L34PartnerConfig V Q P where
  ne := h.ne.symm
  le_centralizer := le_centralizer_iff.mp h.le_centralizer
  isQuasisimple_left := h.isQuasisimple_right
  isQuasisimple_right := h.isQuasisimple_left
  odd_card_center_left := h.odd_card_center_right
  odd_card_center_right := h.odd_card_center_left
  isL34Type_left := h.isL34Type_right
  isL34Type_right := h.isL34Type_left
  card_V := h.card_V
  mul_self := h.mul_self
  le_centralizer_left := h.le_centralizer_right
  le_centralizer_right := h.le_centralizer_left
  isComponent_left := h.isComponent_right
  isComponent_right := h.isComponent_left
  wGroup_left := h.wGroup_right
  wGroup_right := h.wGroup_left

end Config

@[expose] def L34ZeroSwappedBar {G : Type} [Group G] (x b : G)
    (hxb : x ∈ centralizer ({b} : Set G)) (P : Subgroup G) : Prop :=
  ∃ L : Subgroup (↥(centralizer ({b} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({b} : Set G))),
    IsComponent L ∧
    L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))
      ⟨x, hxb⟩)).toMonoidHom ≠ L ∧
    ∀ L' : Subgroup (↥(centralizer ({b} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({b} : Set G))),
      IsComponent L' →
        (⁅(P.subgroupOf (centralizer ({b} : Set G))).map
            (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))), L'⁆ ≠ ⊥ ↔
          L' = L ∨ L' = L.map (MulAut.conj (QuotientGroup.mk'
            (pPrimeCore 2 ↥(centralizer ({b} : Set G))) ⟨x, hxb⟩)).toMonoidHom)

@[expose] def L34ZeroHostFree (G : Type) [Group G] : Prop :=
  ∀ (x b : G) (hxb : x ∈ centralizer ({b} : Set G)) (P : Subgroup G), orderOf x = 2 →
    orderOf b = 2 → P ≤ centralizer ({x} : Set G) → P ≤ centralizer ({b} : Set G) →
    IsComponent (P.subgroupOf (centralizer ({x} : Set G))) → Odd (Nat.card (center ↥P)) →
    IsL34Type (↥P ⧸ center ↥P) →
    ∀ L : Subgroup (↥(centralizer ({b} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({b} : Set G))),
      IsComponent L →
      (P.subgroupOf (centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))) ≤ L →
      L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))
        ⟨x, hxb⟩)).toMonoidHom = L →
      ¬ (Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Suz ∨
        Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan ∨
        Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 4)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
