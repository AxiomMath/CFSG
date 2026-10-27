module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Field
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Polynomial

variable {F : Type*} [Field F]

theorem charP_two (hF : Nat.card F = 16) : CharP F 2 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  let _ := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have h16 : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card]; exact hF
  rw [h16] at hcard
  have hdvd : ringChar F ∣ 2 ^ 4 := by
    have : ringChar F ∣ 16 := hcard ▸ dvd_pow_self _ (by exact PNat.ne_zero n)
    simpa using this
  have h2 : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F _) Nat.prime_two).mp
      ((CharP.char_is_prime F _).dvd_of_dvd_pow hdvd)
  exact h2 ▸ ringChar.charP F

theorem exists_pow_eq (hF : Nat.card F = 16) {ζ : F} (hζ : orderOf ζ = 15) {a : F} (ha : a ≠ 0) :
    ∃ k : ℕ, ζ ^ k = a := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hz : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  let u : Fˣ := Units.mk0 ζ hz
  have hu : orderOf u = Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have : orderOf u = orderOf ζ := (orderOf_units (y := u)).symm
    rw [this, hζ]
  have hmem : Units.mk0 a ha ∈ Submonoid.powers u := by
    have h1 : Units.mk0 a ha ∈ Subgroup.zpowers u := by
      have : Subgroup.zpowers u = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers, hu]
      rw [this]; trivial
    exact (mem_powers_iff_mem_zpowers).2 h1
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  have := congrArg Units.val hk
  simpa [u] using this

theorem zeta_ne_zero {ζ : F} (hζ : ζ ^ 4 = ζ + 1) : ζ ≠ 0 := by
  rintro rfl
  have : (0 : F) ^ 4 = 0 + 1 := hζ
  simp at this

@[expose] noncomputable def g1 : (ZMod 2)[X] := X ^ 4 + X + 1

theorem g1_monic : g1.Monic := by
  unfold g1
  monicity!

theorem g1_natDegree : g1.natDegree = 4 := by
  unfold g1
  compute_degree!

theorem natCard_adjoinRoot : Nat.card (AdjoinRoot g1) = 16 := by
  have hfin : Module.Finite (ZMod 2) (AdjoinRoot g1) := g1_monic.finite_adjoinRoot
  have hr : Module.finrank (ZMod 2) (AdjoinRoot g1) = 4 := by
    rw [(AdjoinRoot.powerBasis' g1_monic).finrank]
    simp [g1_natDegree]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hr]
  simp

theorem two_eq_zero_of_algebra {A : Type*} [Ring A] [Algebra (ZMod 2) A] : (2 : A) = 0 := by
  calc (2 : A) = algebraMap (ZMod 2) A 2 := (map_ofNat _ 2).symm
    _ = algebraMap (ZMod 2) A 0 := by congr 1
    _ = 0 := map_zero _

theorem aeval_g1 {A : Type*} [Ring A] [Algebra (ZMod 2) A] (S : A) (hS : S ^ 4 = S + 1) :
    aeval S g1 = 0 := by
  have h2 : ∀ a : A, a + a = 0 := fun a => by rw [← two_mul, two_eq_zero_of_algebra, zero_mul]
  simp only [g1, map_add, map_pow, aeval_X, map_one]
  rw [hS]
  calc S + 1 + S + 1 = (S + S) + (1 + 1) := by abel
    _ = 0 := by rw [h2, h2, add_zero]

noncomputable def liftRoot {A : Type*} [Ring A] [Algebra (ZMod 2) A] (S : A)
    (hS : S ^ 4 = S + 1) : AdjoinRoot g1 →+* A :=
  Ideal.Quotient.lift (Ideal.span {g1}) (aeval S : (ZMod 2)[X] →ₐ[ZMod 2] A).toRingHom (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1 hp
    simp [aeval_g1 S hS])

theorem liftRoot_root {A : Type*} [Ring A] [Algebra (ZMod 2) A] (S : A) (hS : S ^ 4 = S + 1) :
    liftRoot S hS (AdjoinRoot.root g1) = S := by
  have : AdjoinRoot.root g1 = AdjoinRoot.mk g1 X := AdjoinRoot.mk_X.symm
  rw [this]
  show (aeval S : (ZMod 2)[X] →ₐ[ZMod 2] A) X = S
  simp

section Zeta

variable (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)

include hF hζ

theorem exists_ringHom_zeta {A : Type*} [Ring A] [Algebra (ZMod 2) A] {S : A}
    (hS : S ^ 4 = S + 1) : ∃ ψ : F →+* A, ψ ζ = S := by
  have := charP_two hF
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfin : Finite (AdjoinRoot g1) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_adjoinRoot]; omega)
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  let ev : AdjoinRoot g1 →+* F := liftRoot ζ hζ
  have hsurj : Function.Surjective ev := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    · obtain ⟨k, hk⟩ := exists_pow_eq hF hord ha
      exact ⟨AdjoinRoot.root g1 ^ k, by simp [ev, map_pow, liftRoot_root, hk]⟩
  have hb : Function.Bijective ev :=
    hsurj.bijective_of_nat_card_le (by rw [natCard_adjoinRoot, hF])
  let e := RingEquiv.ofBijective ev hb
  refine ⟨(liftRoot S hS).comp e.symm.toRingHom, ?_⟩
  have : e.symm ζ = AdjoinRoot.root g1 := by
    rw [RingEquiv.symm_apply_eq]
    exact (liftRoot_root ζ hζ).symm
  simp [this, liftRoot_root]

theorem ringHom_ext_zeta {A : Type*} [Semiring A] {ψ ψ' : F →+* A} (h : ψ ζ = ψ' ζ) :
    ψ = ψ' := by
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  refine RingHom.ext fun a => ?_
  by_cases ha : a = 0
  · simp [ha]
  · obtain ⟨k, hk⟩ := exists_pow_eq hF hord ha
    rw [← hk, map_pow, map_pow, h]

end Zeta

section Param

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem exists_addEquiv (hF : Nat.card F = 16) (ψ : F →+* Module.End (ZMod 2) M)
    (hM : Nat.card M = 16) : ∃ Θ : F ≃+ M, ∀ a x, Θ (a * x) = ψ a (Θ x) := by
  have hMfin : Finite M := Nat.finite_of_card_ne_zero (by omega)
  have hMne : Nontrivial M := by
    rw [← Finite.one_lt_card_iff_nontrivial, hM]; omega
  obtain ⟨e, he⟩ := exists_ne (0 : M)
  let Θ₀ : F →+ M :=
    { toFun := fun x => ψ x e
      map_zero' := by simp
      map_add' := fun x y => by simp [map_add, LinearMap.add_apply] }
  have hinj : Function.Injective Θ₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    apply he
    have h1 : ψ x⁻¹ (ψ x e) = e := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hx0, map_one]; rfl
    rw [← h1]
    have : ψ x e = 0 := hx
    rw [this, map_zero]
  have hb : Function.Bijective Θ₀ := hinj.bijective_of_nat_card_le (by rw [hM, hF])
  refine ⟨AddEquiv.ofBijective Θ₀ hb, fun a x => ?_⟩
  show ψ (a * x) e = ψ a (ψ x e)
  rw [map_mul]; rfl

end Param

section Fixed

variable {G : Type*} [AddCommGroup G] {M : Type*} [AddCommGroup M]

theorem exists_fixed_ne_zero [Finite G] (hG : Nat.card G = 16) [Finite M]
    (hM : Even (Nat.card M)) (U : G → (M →+ M)) (h0 : ∀ m, U 0 m = m)
    (hadd : ∀ c c' m, U (c + c') m = U c (U c' m)) : ∃ m : M, m ≠ 0 ∧ ∀ c, U c m = m := by
  let perm : G → Equiv.Perm M := fun c =>
    { toFun := U c
      invFun := U (-c)
      left_inv := fun m => by rw [← hadd, neg_add_cancel, h0]
      right_inv := fun m => by rw [← hadd, add_neg_cancel, h0] }
  let f : Multiplicative G →* Equiv.Perm M :=
    { toFun := fun g => perm (Multiplicative.toAdd g)
      map_one' := by
        ext m
        exact h0 m
      map_mul' := fun g g' => by
        ext m
        exact hadd _ _ m }
  let _ : MulAction (Multiplicative G) M := MulAction.compHom M f
  have hp : IsPGroup 2 (Multiplicative G) := by
    have : Nat.card (Multiplicative G) = 2 ^ 4 := by
      rw [Nat.card_congr Multiplicative.toAdd, hG]; norm_num
    exact IsPGroup.of_card this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hp.card_modEq_card_fixedPoints M
  have hev : Even (Nat.card (MulAction.fixedPoints (Multiplicative G) M)) := by
    have : Nat.card M % 2 = Nat.card (MulAction.fixedPoints (Multiplicative G) M) % 2 := hmod
    rcases hM with ⟨k, hk⟩
    rw [Nat.even_iff]
    omega
  have h0fix : (0 : M) ∈ MulAction.fixedPoints (Multiplicative G) M := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact map_zero (U (Multiplicative.toAdd g))
  have hpos : 0 < Nat.card (MulAction.fixedPoints (Multiplicative G) M) :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, h0fix⟩⟩, inferInstance⟩
  have hgt : 1 < Nat.card (MulAction.fixedPoints (Multiplicative G) M) := by
    rcases hev with ⟨k, hk⟩
    omega
  have hnt := Finite.one_lt_card_iff_nontrivial.1 hgt
  obtain ⟨⟨m, hm⟩, hne⟩ := exists_ne (⟨0, h0fix⟩ : MulAction.fixedPoints (Multiplicative G) M)
  refine ⟨m, fun h => hne (Subtype.ext h), fun c => ?_⟩
  exact (MulAction.mem_fixedPoints.1 hm) (Multiplicative.ofAdd c)

end Fixed

end Nat16

end CFSG.OddStandard.Seitz77
