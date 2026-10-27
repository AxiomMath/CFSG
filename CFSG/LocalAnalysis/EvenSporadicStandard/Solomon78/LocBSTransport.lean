module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSFuse

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

section Equiv

variable {C C' Y : Type*} [Group C] [Group C'] [Group Y]

theorem Quot2Data.comp_equiv {φ : C →* Y} {D : Subgroup Y} (h : Quot2Data φ D) (ζ : C' ≃* C) :
    Quot2Data (φ.comp ζ.toMonoidHom) D := by
  have hrange : (φ.comp ζ.toMonoidHom).range = φ.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ζ x, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨ζ.symm c, by simp⟩
  have hker : Nat.card (φ.comp ζ.toMonoidHom).ker = Nat.card φ.ker :=
    Nat.card_congr
      { toFun := fun x => ⟨ζ x.1, x.2⟩
        invFun := fun c => ⟨ζ.symm c.1, by
          have := c.2
          rw [MonoidHom.mem_ker] at this ⊢
          simpa using this⟩
        left_inv := fun x => Subtype.ext (ζ.symm_apply_apply _)
        right_inv := fun c => Subtype.ext (ζ.apply_symm_apply _) }
  refine ⟨?_, ?_, h.simple, h.noncomm, ?_, ?_, ?_⟩
  · rw [hrange]; exact h.D_le
  · rw [hrange]; exact h.range_le
  · rw [hrange]; exact h.index_two
  · rw [hker]; exact h.ker_two
  · rw [hker]; exact h.big

end Equiv

section Cards

variable {G Y : Type*} [Group G] [Group Y]

theorem card_inf_centralizer_eq (K : Subgroup G) {z : G} (hz : z ∈ K) :
    Nat.card ↥(K ⊓ centralizer ({z} : Set G)) =
      Nat.card ↥(centralizer ({(⟨z, hz⟩ : ↥K)} : Set ↥K)) :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
        (mem_centralizer_singleton_iff.1 x.2.2))⟩
      invFun := fun y => ⟨y.1.1, y.1.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 y.2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_centralizer_eq_of_mulEquiv {X : Type*} [Group X] (e : X ≃* Y) (a : X) :
    Nat.card ↥(centralizer ({a} : Set X)) = Nat.card ↥(centralizer ({e a} : Set Y)) :=
  Nat.card_congr
    { toFun := fun x => ⟨e x.1, mem_centralizer_singleton_iff.2 (by
        have := congrArg e (mem_centralizer_singleton_iff.1 x.2)
        simpa using this)⟩
      invFun := fun y => ⟨e.symm y.1, mem_centralizer_singleton_iff.2 (by
        have := congrArg e.symm (mem_centralizer_singleton_iff.1 y.2)
        simpa using this)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply _)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply _) }

theorem card_inf_centralizer_eq_of_equiv {K : Subgroup G} {D : Subgroup Y} (e : ↥K ≃* ↥D)
    {z : G} (hz : z ∈ K) :
    Nat.card ↥(K ⊓ centralizer ({z} : Set G)) =
      Nat.card ↥(D ⊓ centralizer ({(e ⟨z, hz⟩ : Y)} : Set Y)) := by
  rw [card_inf_centralizer_eq K hz, card_centralizer_eq_of_mulEquiv e ⟨z, hz⟩]
  exact (card_inf_centralizer_eq D (e ⟨z, hz⟩).2).symm

theorem card_centralizer_mul_card_class {H : Type*} [Group H] [Finite H] (g : H) :
    Nat.card ↥(centralizer ({g} : Set H)) * Nat.card (ConjClasses.mk g).carrier = Nat.card H := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAction.stabilizer (ConjAct H) g)
  have h2 : Nat.card (MulAction.orbit (ConjAct H) g) =
      Nat.card (ConjAct H ⧸ MulAction.stabilizer (ConjAct H) g) :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct H) g)
  have h3 : Nat.card (ConjAct H) = Nat.card H := Nat.card_congr ConjAct.ofConjAct.toEquiv
  have h4 : Nat.card ↥(centralizer ({g} : Set H)) =
      Nat.card ↥(MulAction.stabilizer (ConjAct H) g) :=
    Nat.card_congr
      { toFun := fun x => ⟨ConjAct.toConjAct x.1, by
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def]
          simp only [ConjAct.ofConjAct_toConjAct]
          exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_singleton_iff.1 x.2)⟩
        invFun := fun y => ⟨ConjAct.ofConjAct y.1, by
          have := y.2
          rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def] at this
          exact mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 this)⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  rw [h4, ← ConjAct.orbit_eq_carrier_conjClasses, h2, mul_comm, ← h1, h3]

end Cards

section Cards0

variable {G Y : Type} [Group G] [Group Y]

theorem twoAdic_eq_of_equiv {K : Subgroup G} {D : Subgroup Y} (e : ↥K ≃* ↥D) :
    twoAdic K = twoAdic D := by
  unfold twoAdic
  rw [Nat.card_congr e.toEquiv]

theorem twoCentralFused_of_equiv {K : Subgroup G} {D : Subgroup Y} (e : ↥K ≃* ↥D)
    (hD : TwoCentralFused D) : TwoCentralFused K := by
  intro x hx y hy hx2 hy2 hx1 hy1 hxm hym
  have key : ∀ {a : G} (ha : a ∈ K), a * a = 1 → a ≠ 1 →
      (e ⟨a, ha⟩ : Y) * (e ⟨a, ha⟩ : Y) = 1 ∧ (e ⟨a, ha⟩ : Y) ≠ 1 := by
    intro a ha ha2 ha1
    refine ⟨?_, fun h => ha1 ?_⟩
    · have : e (⟨a, ha⟩ * ⟨a, ha⟩) = e 1 := congrArg e (Subtype.ext ha2)
      rw [map_mul, map_one] at this
      exact congrArg Subtype.val this
    · have h1 : e ⟨a, ha⟩ = 1 := Subtype.ext h
      have := e.injective (h1.trans (map_one e).symm)
      exact congrArg Subtype.val this
  obtain ⟨hxx, hx1'⟩ := key hx hx2 hx1
  obtain ⟨hyy, hy1'⟩ := key hy hy2 hy1
  have hxm' : twoAdic D ≤ twoAdic (D ⊓ centralizer ({(e ⟨x, hx⟩ : Y)} : Set Y)) := by
    unfold twoAdic at hxm ⊢
    rw [card_inf_centralizer_eq_of_equiv e hx, Nat.card_congr e.toEquiv] at *
    exact hxm
  have hym' : twoAdic D ≤ twoAdic (D ⊓ centralizer ({(e ⟨y, hy⟩ : Y)} : Set Y)) := by
    unfold twoAdic at hym ⊢
    rw [card_inf_centralizer_eq_of_equiv e hy, Nat.card_congr e.toEquiv] at *
    exact hym
  obtain ⟨c, hcD, hc⟩ := hD _ (e ⟨x, hx⟩).2 _ (e ⟨y, hy⟩).2 hxx hyy hx1' hy1' hxm' hym'
  refine ⟨((e.symm ⟨c, hcD⟩ : ↥K) : G), (e.symm ⟨c, hcD⟩).2, ?_⟩
  have h1 : e (e.symm ⟨c, hcD⟩ * ⟨x, hx⟩ * (e.symm ⟨c, hcD⟩)⁻¹) = e ⟨y, hy⟩ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subtype.ext hc
  have := e.injective h1
  exact congrArg Subtype.val this

end Cards0

theorem factorization_two_pow_mul {m : ℕ} (k : ℕ) (hm0 : m ≠ 0) (hm : ¬ 2 ∣ m) :
    (2 ^ k * m).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem isPerfect_subgroupOf_of_le {X : Type*} [Group X] {A C : Subgroup X} (h : A ≤ C)
    (hA : Group.IsPerfect A) : Group.IsPerfect (A.subgroupOf C) := by
  have := hA
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h).symm.surjective

end CFSG.EvenSporadicStandard.Solomon78
