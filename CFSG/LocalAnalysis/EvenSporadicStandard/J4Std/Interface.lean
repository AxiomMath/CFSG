module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.LiftObstruction
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type} [Group G]

@[expose] def ebasis (e : Fin 11 → G) (c : Fin 11 → ZMod 2) : G :=
  (List.ofFn fun i => e i ^ (c i).val).prod

@[expose] def FixData (L U : Subgroup G) : Prop :=
  ∀ x ∈ U, x ≠ 1 → ∀ w ∈ U,
    (∀ h ∈ Hloc L U, h * x * h⁻¹ = x → h * w * h⁻¹ = w) → w = 1 ∨ w = x

@[expose] def TripleData (L U : Subgroup G) : Prop :=
  ∃ x ∈ U, ∃ y ∈ U, ∃ w ∈ U, x ≠ 1 ∧ x * y ≠ 1 ∧
    y ∈ hOrbit L U x ∧ w ∈ hOrbit L U x ∧ y * w ∈ hOrbit L U x ∧
    x * y ∉ hOrbit L U x ∧ x * w ∈ hOrbit L U (x * y) ∧ x * y * w ∈ hOrbit L U (x * y)

@[expose] def InvConj (L U : Subgroup G) : Prop :=
  ∀ a ∈ L, a * a = 1 → ∃ l ∈ L, l * a * l⁻¹ ∈ U

@[expose] def LiftData (L U : Subgroup G) : Prop :=
  ∃ (e : Fin 11 → G) (s t : G),
    (∀ i, e i ∈ U) ∧
    (∀ c d : Fin 11 → ZMod 2, ebasis e c = ebasis e d → c = d) ∧
    s ∈ Hloc L U ∧ t ∈ Hloc L U ∧ s * s = 1 ∧ t * t = 1 ∧ (s * t) * (s * t) = 1 ∧
    (∀ i, s * e i * s⁻¹ = ebasis e (fun j => Smat i j)) ∧
    (∀ i, t * e i * t⁻¹ = ebasis e (fun j => Tmat i j))

@[expose] def SplitData (L U : Subgroup G) : Prop :=
  ∀ (z : G) (W : Subgroup G),
    z ∈ W → z * z = 1 → z ∉ U → (∀ h ∈ Hloc L U, z * h = h * z) → (∀ u ∈ U, z * u = u * z) →
    U ≤ W → (∀ w ∈ W, ∀ u ∈ U, w * u = u * w) → (∀ w ∈ W, w * w ∈ U) →
    (∀ h ∈ Hloc L U, ∀ w ∈ W, h * w * h⁻¹ ∈ W) →
    (∀ w ∈ W, z * (w⁻¹ * z * w) ∈ U) → (∀ u ∈ U, ∃ w ∈ W, z * (w⁻¹ * z * w) = u) →
    (∀ w ∈ W, z * w = w * z → w ∈ U ⊔ zpowers z) →
    ∃ Y : Subgroup G, U ≤ Y ∧ Y ≤ W ∧ z ∉ Y ∧ (∀ h ∈ Hloc L U, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) ∧
      ∀ w ∈ W, w ∈ Y ∨ z * w ∈ Y

@[expose] def QuotData (L U : Subgroup G) : Prop :=
  ∃ f : Hloc L U →* CFSG.Blueprint.NativeSporadic.M24,
    Function.Surjective f ∧ f.ker = U.subgroupOf (Hloc L U)

structure ModData (L U : Subgroup G) : Prop where
  fix : FixData L U
  triple : TripleData L U
  invConj : InvConj L U
  lift : LiftData L U
  split : SplitData L U
  quot : QuotData L U

end CFSG.EvenSporadicStandard.J4Std
