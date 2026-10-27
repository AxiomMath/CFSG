module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S9

@[expose] def isSp8two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B 4 q => q.card = 2 | _ => False

@[expose] def i1431List (i : TauCeti.CFSGIndex) : Prop :=
  i = .sporadic .Co2 ∨ isSp8two i ∨ isD4two i ∨ isU5two i ∨ isU6two i ∨ isU4eight i

@[expose] def isTableU4 (i : TauCeti.CFSGIndex) : Prop :=
  isD4two i ∨ isSp8two i ∨ isU4eight i ∨ isU5two i ∨ isU6two i ∨ isU4two i

end S9

@[expose] def I81U5At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) S9.isU5two →
    ∃ y ∈ L, y ^ 3 = 1 ∧ y ≠ 1 ∧ ∃ J : Subgroup G,
      GLAPComponent 3 (L ⊓ S9.cx y) J ∧ catalogIs (PSimple 3 J) S9.isU4two ∧
      GLAPPrimeCoreOf 3 J ≤ GLAPPrimeCoreOf 3 L

@[expose] def I2811At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J : Subgroup G), GLAPComponent 3 X J → catalogIs (PSimple 3 J) S9.isU4two →
    Odd (Nat.card (GLAPPrimeCoreOf 3 J)) →
    ∃ z ∈ J, z ^ 2 = 1 ∧ z ≠ 1 ∧ ∃ E : Subgroup G, E ≤ J ⊓ S9.cx z ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2

@[expose] def I102U4At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J : Subgroup G), GLAPComponent 3 X J → catalogIs (PSimple 3 J) S9.isU4two →
    ∃ E : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3

@[expose] def I112RkAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B' L' : Subgroup G), CFSG.Open.IsKGroup ↥X → B' ≤ X → IsElemAbelian 3 B' →
    GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B' → GLAPComponent 3 X L' →
    ¬ B' ≤ Subgroup.normalizer (L' : Set G) →
    ∀ b ∈ B', b ∉ Subgroup.normalizer (L' : Set G) → ∀ J' : Subgroup G,
      GLAPComponent 3 (closureIn L' B' ⊓ Subgroup.centralizer ({b} : Set G)) J' →
      ∀ E : Subgroup G, E ≤ J' → IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2

@[expose] def I1431ClAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (a x : G) (K J : Subgroup G), orderOf a = 3 → CFSG.Open.IsKGroup ↥(S9.cx a) → x ∈ S9.cx a →
    orderOf x = 3 → x ∉ Subgroup.zpowers a → GLAPComponent 3 (S9.cx a) K →
    x ∈ Subgroup.normalizer (K : Set G) → GLAPComponent 3 (K ⊓ S9.cx x) J →
    catalogIs (PSimple 3 J) S9.isU4two → ¬ K ≤ J ⊔ GLAPPrimeCoreOf 3 K →
    GLATwoLocalRank 3 G ≤ 4 → catalogIs (PSimple 3 K) S9.i1431List

@[expose] def U4TableAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (K W : Subgroup G) (u : G) (hWN : W ≤ Subgroup.normalizer (K : Set G)) (huW : u ∈ W),
    (∃ X : Subgroup G, GLAPComponent 3 X K) → K ≤ W → u ^ 3 = 1 →
    catalogIs (PSimple 3 K) S9.isTableU4 →
    (∃ J : Subgroup G, GLAPComponent 3 (K ⊓ S9.cx u) J ∧ catalogIs (PSimple 3 J) S9.isU4two) →
    IsPGroup 2 (GLAPPrimeCoreOf 3 (CFSG.HardMathSupport.Solomon.LocalBalance.autBar 3 W K ⊓
      Subgroup.centralizer ({CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨u, hWN huW⟩} :
        Set (MulAut (CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 K)))))

end CFSG.LocalAnalysis.GLTheoremA
