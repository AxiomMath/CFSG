module

public import CFSG.LargeExtraspecial.S4FiveMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup CFSG.Open

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def Mbar0 (S : Setting G) (g : G) : Subgroup S.O :=
  ⨆ h : S.M, S.Lbar ((h : G) * g)

@[expose] def Irr (S : Setting G) : Prop :=
  ∀ U : Submodule (ZMod 2) S.Qt,
    (∀ x ∈ S.Mbar, ∀ u ∈ U, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U) → U = ⊥ ∨ U = ⊤

variable {S : Setting G} {g : G}

@[expose] def NonabelianSylowTwo {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ P : Subgroup (V ≃ₗ[ZMod 2] V), P ≤ X → IsPGroup 2 P → ¬ 2 ∣ P.relIndex X →
    ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x

structure Hyp45Q (H : S4.Hyp4 S g) (C : S4.Cons311 S g) : Prop where
  lin_two : ∀ {t : S.O} (ht : t ∈ S.Lbar g), S4.LinCase S g ht →
    Module.finrank (ZMod 2) (S4.Vt S g t) = 2 → Group.IsSolvable (S4.RmodN S g t)
  lin : ∀ {t : S.O} (ht : t ∈ S.Lbar g), S4.LinCase S g ht →
    3 ≤ Module.finrank (ZMod 2) (S4.Vt S g t) →
    IsSimpleGroup (S4.RmodN S g t) ∧ NonabelianSylowTwo (S4.RmodN S g t)
  sp : ∀ {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ S4.V S g t ≤ S.Qa g),
    S4.SpCase H C ht ht1 hVQ → 6 ≤ Module.finrank (ZMod 2) (S4.Vt S g t) →
    IsSimpleGroup (S4.RmodN S g t) ∧ NonabelianSylowTwo (S4.RmodN S g t)
  sp_four : ∀ {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ S4.V S g t ≤ S.Qa g),
    S4.SpCase H C ht ht1 hVQ → Module.finrank (ZMod 2) (S4.Vt S g t) = 4 →
    ∃ M₀ ≤ S4.RmodN S g t, (M₀.subgroupOf (S4.RmodN S g t)).Normal ∧ IsSimpleGroup M₀ ∧
      M₀.relIndex (S4.RmodN S g t) = 2 ∧ NonabelianSylowTwo M₀
  a6 : ∀ {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ S4.V S g t ≤ S.Qa g),
    S4.A6Case H C ht ht1 hVQ → IsSimpleGroup (S4.RmodN S g t)
  omega : ∀ {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ S4.V S g t ≤ S.Qa g),
    S4.OmegaCase H C ht ht1 hVQ → 6 ≤ Module.finrank (ZMod 2) (S4.Vt S g t) →
    IsSimpleGroup (S4.RmodN S g t) ∧ NonabelianSylowTwo (S4.RmodN S g t)
  omega_four : ∀ {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ S4.V S g t ≤ S.Qa g),
    S4.OmegaCase H C ht ht1 hVQ → Module.finrank (ZMod 2) (S4.Vt S g t) = 4 →
    IsSimpleGroup (S4.RmodN S g t) ∨ Group.IsSolvable (S4.RmodN S g t)
  pgl25 : ∀ {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ S4.V S g t ≤ S.Qa g),
    S4.PGL25Case H C ht ht1 hVQ →
    ∃ M₀ ≤ S4.RmodN S g t, (M₀.subgroupOf (S4.RmodN S g t)).Normal ∧ IsSimpleGroup M₀ ∧
      M₀.relIndex (S4.RmodN S g t) ≤ 2

end CFSG.LargeExtraspecial.S5
