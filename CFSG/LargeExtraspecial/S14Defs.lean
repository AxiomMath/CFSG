module

public import CFSG.LargeExtraspecial.S4FiveMain
public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G]

noncomputable abbrev Mbar0 (S : Setting G) : Subgroup S.Mbar := timmesfeldFStar S.Mbar

noncomputable abbrev Ct (S : Setting G) (t : S.O) : Subgroup S.O :=
  S.Mbar ⊓ centralizer ({t} : Set S.O)

noncomputable abbrev FCt (S : Setting G) (t : S.O) : Subgroup S.O :=
  (timmesfeldFStar (Ct S t)).map (Ct S t).subtype

@[expose] def RNOmega (S : Setting G) (g : G) (t : S.O) (d : ℕ) : Prop :=
  ∃ (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g), OmegaCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = d

@[expose] def RNPlus (S : Setting G) (g : G) (t : S.O) : Prop :=
  ∃ (ht : t ∈ S.Lbar g) (W : Submodule (ZMod 2) (Vt S g t)),
    2 * finrank (ZMod 2) W = finrank (ZMod 2) (Vt S g t) ∧
      ∀ w ∈ W, w ≠ 0 → w ∈ orbitOf (RmodN S g t) (aV ht)

@[expose] def RNSp (S : Setting G) (g : G) (t : S.O) (d : ℕ) : Prop :=
  ∃ (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g), SpCase H C ht ht1 hVQ ∧ finrank (ZMod 2) (Vt S g t) = d

inductive Config where
  | omegaMinus8
  | omegaMinus6
  | omegaPlus12
  | omegaPlus10
  | omegaPlus8a
  | omegaPlus8b
  | omegaPlus6
  | sp6
  | sp8

namespace Config

@[expose] def width : Config → ℕ
  | omegaMinus8 => 16 | omegaMinus6 => 10 | omegaPlus12 => 28 | omegaPlus10 => 18
  | omegaPlus8a => 12 | omegaPlus8b => 16 | omegaPlus6 => 10 | sp6 => 11 | sp8 => 17

@[expose] def cardExp : Config → ℕ
  | omegaMinus8 => 17 | omegaMinus6 => 9 | omegaPlus12 => 33 | omegaPlus10 => 17
  | omegaPlus8a => 9 | omegaPlus8b => 17 | omegaPlus6 => 9 | sp6 => 9 | sp8 => 17

@[expose] def Holds (S : Setting G) (g : G) (t : S.O) : Config → Prop
  | omegaMinus8 => RNOmega S g t 8 ∧ ¬ RNPlus S g t
  | omegaMinus6 => RNOmega S g t 6 ∧ ¬ RNPlus S g t
  | omegaPlus12 => RNOmega S g t 12 ∧ RNPlus S g t
  | omegaPlus10 => RNOmega S g t 10 ∧ RNPlus S g t
  | omegaPlus8a => RNOmega S g t 8 ∧ RNPlus S g t
  | omegaPlus8b => RNOmega S g t 8 ∧ RNPlus S g t
  | omegaPlus6 => RNOmega S g t 6 ∧ RNPlus S g t
  | sp6 => RNSp S g t 6
  | sp8 => RNSp S g t 8

@[expose] def Occurs (c : Config) (S : Setting G) (g : G) (t : S.O) : Prop :=
  c.Holds S g t ∧ S.width = c.width ∧ Nat.card (Nbar S g t) = 2 ^ c.cardExp

end Config

structure Stage (S : Setting G) (g : G) (t : S.O) : Prop where
  six_le_width : 6 ≤ S.width
  hyp4 : Hyp4 S g
  noA2 : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → ¬ S.HasTypeAInL g'
  cons : Cons311 S g
  irr : ¬ S.IsReducible
  mem : t ∈ S.Lbar g
  ne_one : t ≠ 1
  rbar_ne : Rbar S g t ≠ S.Lbar g
  abar_ne : S.Lbar g ⊓ Nbar S g t ≠ zpowers t

@[expose] def Hyp89 (S : Setting G) (g : G) (t : S.O) : Prop :=
  ∃ (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g),
    (OmegaCase H C ht ht1 hVQ ∧ ¬ (finrank (ZMod 2) (Vt S g t) = 4 ∧ RNPlus S g t)) ∨
      SpCase H C ht ht1 hVQ ∨ A6Case H C ht ht1 hVQ ∨ PGL25Case H C ht ht1 hVQ

@[expose] def Concl14_7 (S : Setting G) (g : G) (t : S.O) : Prop :=
  (∀ x ∈ S.Mbar, (∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t) → x ∈ Nbar S g t) ∧
    IsPGroup 2 (timmesfeldFStar (Ct S t))

end CFSG.LargeExtraspecial.S14
