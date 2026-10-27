module

public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LargeExtraspecial.S10Basic
public import CFSG.LargeExtraspecial.S11Nine
public import CFSG.LargeExtraspecial.BridgeConclusion
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.Sporadic.Co2Smith.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

@[expose] def S8_3Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t →
    (RNOmega S g t 4 ∧ ¬ RNPlus S g t) ∨ (RNOmega S g t 6 ∧ RNPlus S g t) ∨
      (RNOmega S g t 8 ∧ RNPlus S g t) →
    (∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t) ∨
      (RNOmega S g t 6 ∧ RNPlus S g t ∧ S.width = 10) ∨
      (RNOmega S g t 8 ∧ RNPlus S g t ∧ S.width = 12)

@[expose] def S9A6PGLStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t → ∀ (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g), ¬ (A6Case H C ht ht1 hVQ ∨ PGL25Case H C ht ht1 hVQ)

@[expose] def S11_1Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G),
    S11.Hyp S g → ¬ S.IsReducible → 6 ≤ S.width →
    (∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) → S11.Timmesfeld11_1Stmt S

@[expose] def S11_8M2Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S11.Timmesfeld11_8M2 S

@[expose] def S11Alt4Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (k u : G) (τ : S.M),
    S11.Hyp S k → S11.Conf S k (S.ρ τ) τ u → finrank (ZMod 2) (Vt S k (S.ρ τ)) = 3 →
    S.width = 6 → ¬ S.IsReducible → Bridge.TimmesfeldAlt4 S.width S.Mbar

@[expose] def S13_9Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    S10.Hyp10 S g t → S11.NoA2All S → ¬ S.IsReducible → 7 ≤ S.width →
    Bridge.TimmesfeldAlt3 S.width S.Mbar

@[expose] def S10Alt4Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    S10.Hyp10 S g t → S11.NoA2All S → ¬ S.IsReducible → S.width = 6 →
    Bridge.TimmesfeldAlt4 S.width S.Mbar

@[expose] def Claim14_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
    (c : Config), Stage S g t → c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      Concl14_7 S g t

@[expose] def Claim14_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
    (c : Config), Stage S g t → (c = .omegaMinus8 ∨ c = .omegaPlus10 ∨ c = .sp8) →
      c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) → IsSimpleGroup (Mbar0 S) →
      Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype → FCt S t = Nbar S g t →
      Bridge.MainFor (Mbar0 S) → False

@[expose] def Claim14_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
    (c : Config), Stage S g t → (c = .omegaMinus6 ∨ c = .omegaPlus6) → c.Occurs S g t →
      IsExtraspecialPGroup 2 (Nbar S g t) → IsSimpleGroup (Mbar0 S) → Concl14_7 S g t →
      Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype → FCt S t = Nbar S g t →
      Nonempty (Mbar0 S ≃* timmesfeldPSU 6) ∨ Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))

@[expose] def Claim14_12U : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
    (c : Config), Stage S g t → (c = .omegaMinus6 ∨ c = .omegaPlus6) → c.Occurs S g t →
      IsExtraspecialPGroup 2 (Nbar S g t) → IsSimpleGroup (Mbar0 S) → Concl14_7 S g t →
      Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype → FCt S t = Nbar S g t →
      Nonempty (Mbar0 S ≃* timmesfeldPSU 6) → ¬ 3 ∣ (Mbar0 S).index

@[expose] def Claim14_13A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
    (c : Config), Stage S g t → c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      IsSimpleGroup (Mbar0 S) → Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype →
      FCt S t = Nbar S g t →
      (c = .sp6 → ∃ ht : t ∈ S.Mbar, CFSG.Sporadic.Co2Smith.TimmesfeldCo2Hyp S.Mbar ⟨t, ht⟩) ∧
        (c = .omegaPlus8a → ∃ ht : t ∈ S.Mbar, PattersonCo1Hyp S.Mbar ⟨t, ht⟩) ∧
        (c = .omegaPlus12 → Bridge.TimmesfeldAlt8 S.width S.Mbar)

@[expose] def Claim14_13B1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t → Config.omegaPlus8b.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      IsSimpleGroup (Mbar0 S) → Concl14_7 S g t → Rbar S g t ≤ (Mbar0 S).map S.Mbar.subtype →
      FCt S t = Nbar S g t → Bridge.MainFor (Mbar0 S) → Bridge.TimmesfeldAlt8 S.width S.Mbar

end CFSG.LargeExtraspecial.S14
