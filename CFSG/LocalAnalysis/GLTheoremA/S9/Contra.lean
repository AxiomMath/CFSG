module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Contra92 (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (q : ℕ) (Q₁ : Subgroup G) : Prop where
  h : H92 p B x L
  setup : Setup92 p q L Q₁
  ne : (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G) ≠ ⊥
  odd : Odd (Nat.card (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G))

structure Concl96 (p : ℕ) (B : Subgroup G) (x : G) (L Q₁ : Subgroup G) : Prop where
  p_eq : p = 3
  type : catalogIs (PSimple p L) isU5two
  card : Nat.card B = 3 ^ 4
  odd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x)))
  center : Q₁ ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ Subgroup.centralizer (L : Set G)

variable {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G}

theorem Contra92.le_L (hC : Contra92 p B x L q Q₁) : Q₁ ≤ L :=
  hC.setup.le_core.trans (Subgroup.map_subtype_le _)

theorem Contra92.le_cx (hC : Contra92 p B x L q Q₁) : Q₁ ≤ cx x :=
  hC.le_L.trans hC.h.comp.1

theorem Contra92.le_pCoreOf_cx (hC : Contra92 p B x L q Q₁) : Q₁ ≤ pCoreOf q (cx x) :=
  hC.setup.le_core.trans (pCoreOf_le_of_isSubnormal hC.setup.prime hC.h.comp.2.1)

end CFSG.LocalAnalysis.GLTheoremA.S9
