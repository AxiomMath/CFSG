module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJSylInputs
public import CFSG.Monster.B.Fischer.Fi22OuterData
public import Certificates.Data.CFSGNative.Fi23.ClassesData

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Monster.B.Fischer CFSG.Sporadic.Fi23 FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_map_of_ker {Λ Q : Type*} [Group Λ] [Group Q] (π : Λ →* Q) (E : Subgroup Λ)
    (hker : Nat.card π.ker = 2) (hle : π.ker ≤ E) {n : ℕ} (hE : Nat.card E = 2 ^ (n + 1)) :
    Nat.card (E.map π) = 2 ^ n := by
  have h := Subgroup.card_ker_mul_card_range (π.comp E.subtype)
  have hrange : (π.comp E.subtype).range = E.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hk : (π.comp E.subtype).ker = π.ker.subgroupOf E := rfl
  rw [hrange, hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hker, hE] at h
  rw [pow_succ] at h
  omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81
