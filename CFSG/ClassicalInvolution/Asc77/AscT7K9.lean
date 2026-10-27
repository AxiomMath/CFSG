module

public import CFSG.ClassicalInvolution.Asc77.AscT7K8
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RInnerSL
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7K

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

theorem twinSmallInner_K (p : ℕ) [Fact p.Prime] : TwinSmallInner p :=
  twinSmallInner_of_rows (twinSmallInnerSp p) (twinSmallInnerSL p) (twinSmallInnerSU p)
    (CFSG.ClassicalInvolution.G2D4Models.Twin.twinSmallInnerD4 p)

theorem hyp51_B_proved (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Hyp51 (Subgroup.closure ({u * e, u, z} : Set G)) :=
  hyp51_B (twinSmallInner_K p) g2d4VertexExcl_proved hs hd

theorem c23_5X_one_proved (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Odd (Nat.card ↥(alphaOf (Subgroup.closure ({u, z} : Set G)))) ∧
      ∀ A : Subgroup G, A ≤ Subgroup.closure ({u * e, u, z} : Set G) → IsElemAbelian2 A 2 →
        alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)) :=
  c23_5X_one (twinSmallInner_K p) g2d4VertexExcl_proved hs hd

end T7K

end CFSG.ClassicalInvolution.Asc77
