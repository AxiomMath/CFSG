module

public import CFSG.CGT.PushingUp.Defs

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def characteristicCoreStar (T : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (omegaOneCenterIn T : Set G) ⊔
    ⨆ (B : Subgroup G) (_ : B ≠ ⊥ ∧ B ≤ pushingUpS T ∧
      (B.subgroupOf (pushingUpS T)).Characteristic), Subgroup.normalizer (B : Set G)

@[expose] def jIn (K : Subgroup G) : Subgroup G :=
  inSubgroup (fun K _ => elemThompson K 2) K

@[expose] def oTwoIn (X : Subgroup G) : Subgroup G :=
  inSubgroup (fun K _ => pCore 2 K) X

theorem conj_mem_oTwoIn {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {c : G} (hc : c ∈ oTwoIn X) : g * c * g⁻¹ ∈ oTwoIn X := by
  obtain ⟨c', hc', rfl⟩ := hc
  let φ : MulAut ↥X := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hφ : φ c' ∈ pCore 2 ↥X :=
    (Subgroup.characteristic_iff_le_comap.mp (inferInstance : (pCore 2 ↥X).Characteristic)) φ hc'
  exact ⟨φ c', hφ, Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨g, hg⟩ c'⟩

@[expose] def centralizerModCore (X : Subgroup G) : Subgroup G where
  carrier := {g : G | g ∈ Subgroup.normalizer (X : Set G) ∧
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ oTwoIn X}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨mul_mem hgN hhN, fun x hx => ?_⟩
    have e : g * h * x * (g * h)⁻¹ * x⁻¹ =
        g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem_oTwoIn hgN (hh x hx)) (hg x hx)
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨inv_mem hgN, fun x hx => ?_⟩
    have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_oTwoIn (inv_mem hgN) (inv_mem (hg x hx))

@[expose] def InClassXG [Finite G] (X : Subgroup G) : Prop :=
  InClassX ↥X ∧ ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore X) →
    (X ≤ Subgroup.normalizer (R : Set G) ∧
      (X.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal) ∧
    (X = ⁅jIn (Subgroup.normalizer (X : Set G)), X⁆ ∨
      (X ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
        (X.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal))

@[expose] def IsMaximalInClassXG [Finite G] (X : Subgroup G) : Prop :=
  InClassXG X ∧ ∀ Y : Subgroup G, InClassXG Y → Arrow X Y → Y = X

end CFSG.CGT.PushingUpLit
