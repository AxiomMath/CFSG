module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

def conjIntoSet {G : Type*} [Group G] (H : Subgroup G) (x : G) : Set G :=
  {g | g⁻¹ * x * g ∈ H}

theorem conjIntoSet_eq_preimage_fixedBy {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    conjIntoSet H x = QuotientGroup.mk ⁻¹' MulAction.fixedBy (G ⧸ H) x := by
  ext g
  simp only [conjIntoSet, Set.mem_setOf_eq, Set.mem_preimage, MulAction.mem_fixedBy,
    MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq, mul_inv_rev, inv_inv]
  constructor <;> intro h <;>
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using H.inv_mem h

theorem card_conjIntoSet_eq_card_fixedBy_mul {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    Nat.card (conjIntoSet H x) =
      Nat.card (MulAction.fixedBy (G ⧸ H) x) * Nat.card H := by
  rw [conjIntoSet_eq_preimage_fixedBy]
  rw [Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H
        (MulAction.fixedBy (G ⧸ H) x)), Nat.card_prod, Nat.mul_comm]

noncomputable def conjWitness {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (y : {y : H // IsConj x (y : G)}) : G :=
  Classical.choose (isConj_iff.mp y.2)

theorem conjWitness_spec {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (y : {y : H // IsConj x (y : G)}) :
    conjWitness y * x * (conjWitness y)⁻¹ = (y.1 : G) :=
  Classical.choose_spec (isConj_iff.mp y.2)

noncomputable def conjPreimage {G : Type*} [Group G] (H : Subgroup G) (x : G)
    (y : {y : H // IsConj x (y : G)}) : conjIntoSet H x :=
  ⟨(conjWitness y)⁻¹, by
    show ((conjWitness y)⁻¹)⁻¹ * x * (conjWitness y)⁻¹ ∈ H
    rw [inv_inv, conjWitness_spec]
    exact y.1.2⟩

theorem conjPreimage_spec {G : Type*} [Group G] (H : Subgroup G) (x : G)
    (y : {y : H // IsConj x (y : G)}) :
    (conjPreimage H x y).1⁻¹ * x * (conjPreimage H x y).1 = (y.1 : G) := by
  change ((conjWitness y)⁻¹)⁻¹ * x * (conjWitness y)⁻¹ = (y.1 : G)
  rw [inv_inv, conjWitness_spec]

def conjMap {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    conjIntoSet H x → {y : H // IsConj x (y : G)} :=
  fun g => ⟨⟨g.1⁻¹ * x * g.1, g.2⟩, isConj_iff.mpr ⟨g.1⁻¹, by group⟩⟩

theorem conjPreimage_mul_centralizer {G : Type*} [Group G] (H : Subgroup G) (x : G)
    (y : {y : H // IsConj x (y : G)}) (c : Subgroup.centralizer ({x} : Set G)) :
    (c.1 * (conjPreimage H x y).1)⁻¹ * x * (c.1 * (conjPreimage H x y).1) = (y.1 : G) := by
  have hc : (c.1 : G) * x = x * c.1 := Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hcx : (c.1 : G)⁻¹ * x * c.1 = x := by
    calc (c.1 : G)⁻¹ * x * c.1 = (c.1 : G)⁻¹ * (x * c.1) := by group
      _ = (c.1 : G)⁻¹ * (c.1 * x) := by rw [← hc]
      _ = x := by group
  calc (c.1 * (conjPreimage H x y).1)⁻¹ * x * (c.1 * (conjPreimage H x y).1)
      = (conjPreimage H x y).1⁻¹ * ((c.1 : G)⁻¹ * x * c.1) *
          (conjPreimage H x y).1 := by group
    _ = (conjPreimage H x y).1⁻¹ * x * (conjPreimage H x y).1 := by rw [hcx]
    _ = (y.1 : G) := conjPreimage_spec H x y

noncomputable def fiberConjMapEquivCentralizer {G : Type*} [Group G] (H : Subgroup G) (x : G)
    (y : {y : H // IsConj x (y : G)}) :
    {g : conjIntoSet H x // conjMap H x g = y} ≃ Subgroup.centralizer ({x} : Set G) where
  toFun g :=
    ⟨g.1.1 * (conjPreimage H x y).1⁻¹, by
      have hg : g.1.1⁻¹ * x * g.1.1 = (y.1 : G) := by
        have h := congrArg (fun z : {y : H // IsConj x (y : G)} => (z.1 : G)) g.2
        simpa [conjMap] using h
      have hw : (conjPreimage H x y).1⁻¹ * x * (conjPreimage H x y).1 = (y.1 : G) :=
        conjPreimage_spec H x y
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc g.1.1 * (conjPreimage H x y).1⁻¹ * x
          = g.1.1 * ((conjPreimage H x y).1⁻¹ * x * (conjPreimage H x y).1) *
              (conjPreimage H x y).1⁻¹ := by group
        _ = g.1.1 * (y.1 : G) * (conjPreimage H x y).1⁻¹ := by rw [hw]
        _ = g.1.1 * (g.1.1⁻¹ * x * g.1.1) * (conjPreimage H x y).1⁻¹ := by rw [← hg]
        _ = x * (g.1.1 * (conjPreimage H x y).1⁻¹) := by group⟩
  invFun c :=
    ⟨⟨c.1 * (conjPreimage H x y).1, by
        show (c.1 * (conjPreimage H x y).1)⁻¹ * x * (c.1 * (conjPreimage H x y).1) ∈ H
        rw [conjPreimage_mul_centralizer H x y c]
        exact y.1.2⟩,
      by
        simp only [conjMap]
        exact Subtype.ext (Subtype.ext (conjPreimage_mul_centralizer H x y c))⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    group
  right_inv c := by
    apply Subtype.ext
    group

theorem card_conjIntoSet_eq_card_centralizer_mul {G : Type*} [Group G]
    (H : Subgroup G) (x : G) :
    Nat.card (conjIntoSet H x) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) *
        Nat.card {y : H // IsConj x (y : G)} := by
  calc Nat.card (conjIntoSet H x)
      = Nat.card (Σ y : {y : H // IsConj x (y : G)},
          {g : conjIntoSet H x // conjMap H x g = y}) :=
        Nat.card_congr (Equiv.sigmaFiberEquiv (conjMap H x)).symm
    _ = Nat.card (Σ _y : {y : H // IsConj x (y : G)},
          Subgroup.centralizer ({x} : Set G)) :=
        Nat.card_congr (Equiv.sigmaCongrRight (fiberConjMapEquivCentralizer H x))
    _ = Nat.card ({y : H // IsConj x (y : G)} ×
          Subgroup.centralizer ({x} : Set G)) :=
        Nat.card_congr (Equiv.sigmaEquivProd _ _)
    _ = Nat.card {y : H // IsConj x (y : G)} *
          Nat.card (Subgroup.centralizer ({x} : Set G)) :=
        Nat.card_prod _ _
    _ = Nat.card (Subgroup.centralizer ({x} : Set G)) *
          Nat.card {y : H // IsConj x (y : G)} :=
        Nat.mul_comm _ _

theorem card_fixedBy_quotient_mul {G : Type*} [Group G] [Finite G] (H : Subgroup G) (x : G) :
    Nat.card (MulAction.fixedBy (G ⧸ H) x) * Nat.card H =
      Nat.card (Subgroup.centralizer ({x} : Set G)) * Nat.card {y : H // IsConj x (y : G)} := by
  rw [← card_conjIntoSet_eq_card_fixedBy_mul H x, card_conjIntoSet_eq_card_centralizer_mul H x]

end CFSG.EvenSporadicStandard.M12Std.Yosh
