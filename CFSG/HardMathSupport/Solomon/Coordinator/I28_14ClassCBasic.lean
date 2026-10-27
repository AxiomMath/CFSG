module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Defs
public import CFSG.GroupTheory.HyperplaneGeneration

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module

section Basic

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def fixSub (E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) :
    Submodule (ZMod 2) U where
  carrier := {x | ∀ e ∈ E, (e : U →ₗ[ZMod 2] U) x = x}
  add_mem' {x y} hx hy e he := by rw [map_add, hx e he, hy e he]
  zero_mem' e _ := map_zero _
  smul_mem' c x hx e he := by rw [map_smul, hx e he]

theorem mem_fixSub {E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} {x : U} :
    x ∈ fixSub E ↔ ∀ e ∈ E, (e : U →ₗ[ZMod 2] U) x = x := Iff.rfl

theorem i28_14_C_close {p : ℕ} {G A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)}
    {t : LinearMap.GeneralLinearGroup (ZMod 2) U} {y : LinearMap.GeneralLinearGroup (ZMod 2) U}
    (hy : y ∈ G) {E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hEA : E ≤ A)
    (hcard : Nat.card A ≤ p * Nat.card E)
    (hcomm : ∀ e ∈ E, e * (y⁻¹ * t * y) = (y⁻¹ * t * y) * e) : HasCentralizedConj p G A t :=
  ⟨y, hy, E, hEA, hcard, hcomm⟩

theorem i28_14_C_cyclic {p : ℕ} (hp : p.Prime)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} [Finite A] (hA : IsElemAbelian p A)
    (hc : IsCyclic A) : Nat.card A ≤ p := by
  have hexp : Monoid.exponent A ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    have := hA.2 x.1 x.2
    exact Subtype.ext (by simpa using this)
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd hp.pos hexp

theorem i28_14_C_of_cyclic {p : ℕ} (hp : p.Prime) {G A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)}
    [Finite A] (hA : IsElemAbelian p A) (hc : IsCyclic A)
    (t : LinearMap.GeneralLinearGroup (ZMod 2) U) : HasCentralizedConj p G A t := by
  refine i28_14_C_close (y := 1) G.one_mem (E := ⊥) bot_le ?_ ?_
  · simpa using i28_14_C_cyclic hp hA hc
  · intro e he
    rw [Subgroup.mem_bot] at he
    subst he
    simp

end Basic

section Hyper

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]

instance i28_14_C_finiteGL : Finite (LinearMap.GeneralLinearGroup (ZMod 2) U) := by
  have : Finite (U →ₗ[ZMod 2] U) :=
    Finite.of_injective (fun f : U →ₗ[ZMod 2] U => (f : U → U)) DFunLike.coe_injective
  infer_instance

@[expose, instance_reducible] def i28_14_C_act (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) :
    MulDistribMulAction A (Multiplicative U) where
  smul a x := Multiplicative.ofAdd
    (((a : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) (Multiplicative.toAdd x))
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := congrArg Multiplicative.ofAdd (map_add _ _ _)
  smul_one _ := congrArg Multiplicative.ofAdd (map_zero _)

theorem i28_14_C_natCard_not_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Multiplicative U) := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  have h : Nat.card (Multiplicative U) = 2 ^ Module.finrank (ZMod 2) U := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [Nat.card_zmod] at this
    exact this
  rw [h]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

theorem i28_14_C_exists_hyperplane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hA : IsElemAbelian p A)
    (hnc : ¬ IsCyclic A) :
    ∃ E ≤ A, Nat.card A = p * Nat.card E ∧
      ∃ c ∈ fixSub E, ∃ d ∈ fixSub E, c ≠ 0 ∧ d ≠ 0 ∧ c ≠ d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnc inferInstance
  have : IsElementaryAbelian p A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
        have := hA.2 x.1 x.2
        exact Subtype.ext (by simpa using this) }
  let _ := i28_14_C_act A
  have hgen := CFSG.SolvableHall.abelian_hyperplane_generation (p := p) (A := A)
    (H := Multiplicative U) (i28_14_C_natCard_not_dvd hp hp2)
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  by_contra hcon
  push Not at hcon
  have hle : ∀ B : Subgroup A, B.index = p →
      CFSG.fixedPointSubgroup B (Multiplicative U) ≤
        CFSG.fixedPointSubgroup A (Multiplicative U) := by
    intro B hB x hx a
    have hEcard : Nat.card A = p * Nat.card (B.map A.subtype) := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, ← hB, mul_comm]
      exact (B.card_mul_index).symm
    have hxE : Multiplicative.toAdd x ∈ fixSub (B.map A.subtype) := by
      rintro _ ⟨b, hb, rfl⟩
      have h := congrArg Multiplicative.toAdd (hx ⟨b, hb⟩)
      exact h
    have haE : Multiplicative.toAdd (a • x) ∈ fixSub (B.map A.subtype) := by
      rintro _ ⟨b, hb, rfl⟩
      have h1 := hxE _ ⟨b, hb, rfl⟩
      have h2 : ((b : A) * a : A) = a * b := hcomm _ _
      have h2' : ((b : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) *
          ((a : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) =
          ((a : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) *
            ((b : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) := congrArg Subtype.val h2
      have key := congrArg (fun z : LinearMap.GeneralLinearGroup (ZMod 2) U =>
        (z : U →ₗ[ZMod 2] U) (Multiplicative.toAdd x)) h2'
      change (((b : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U)
        ((((a : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U)
          (Multiplicative.toAdd x)) = (((a : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) :
              U →ₗ[ZMod 2] U)
            ((((b : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U)
              (Multiplicative.toAdd x)) at key
      exact key.trans (congrArg _ h1)
    by_cases hx0 : Multiplicative.toAdd x = 0
    · have : x = 1 := hx0
      rw [this]
      exact smul_one a
    · have hne : (((a : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U))
          (Multiplicative.toAdd x) ≠ 0 := by
        intro h0
        apply hx0
        have := congrArg ((((a⁻¹ : A) : LinearMap.GeneralLinearGroup (ZMod 2) U) :
          U →ₗ[ZMod 2] U)) h0
        simpa [← Module.End.mul_apply, ← Units.val_mul] using this
      exact congrArg Multiplicative.ofAdd
        (hcon _ (Subgroup.map_subtype_le B) hEcard _ haE _ hxE hne hx0)
  have hall : ∀ x : Multiplicative U, ∀ a : A, a • x = x := by
    intro x
    have hx : x ∈ (⊤ : Subgroup (Multiplicative U)) := Subgroup.mem_top x
    rw [← hgen] at hx
    have hsup : (⨆ (B : Subgroup A) (_ : B.index = p), CFSG.fixedPointSubgroup B (Multiplicative U))
        ≤ CFSG.fixedPointSubgroup A (Multiplicative U) :=
      iSup₂_le fun B hB => hle B hB
    exact (FixedPoints.mem_subgroup A (Multiplicative U) x).mp (hsup hx)
  have : Subsingleton A := ⟨fun a b => by
    have key : ∀ c : A, (c : LinearMap.GeneralLinearGroup (ZMod 2) U) = 1 := fun c =>
      Units.ext (LinearMap.ext fun v => congrArg Multiplicative.toAdd (hall (Multiplicative.ofAdd v) c))
    exact Subtype.ext ((key a).trans (key b).symm)⟩
  exact hnc inferInstance

end Hyper

section Avg

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

theorem i28_14_C_nsmul_odd {n : ℕ} (hn : Odd n) (x : U) : n • x = x := by
  have h : (n : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).mpr hn
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), h, one_smul]

theorem i28_14_C_odd_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} [Finite A] (hA : IsElemAbelian p A)
    {E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)} (hEA : E ≤ A) :
    Odd (Nat.card E) := by
  have hpg : IsPGroup p A := fun x => ⟨1, by
    have := hA.2 x.1 x.2
    exact Subtype.ext (by simpa using this)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
  have hodd : Odd (Nat.card A) := by
    rw [hn]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le hEA)

variable (E : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) U)) [Fintype E]

@[expose] def avgOp : U →ₗ[ZMod 2] U :=
  ∑ e : E, ((e : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U)

theorem avgOp_apply (x : U) :
    avgOp E x = ∑ e : E, ((e : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x := by
  simp [avgOp, LinearMap.sum_apply]

theorem avgOp_mem_fixSub (x : U) : avgOp E x ∈ fixSub E := by
  intro e' he'
  rw [avgOp_apply, map_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨e', he'⟩ : E)) _ _ (fun e => rfl)

theorem avgOp_of_mem_fixSub (hE : Odd (Fintype.card E)) {x : U} (hx : x ∈ fixSub E) :
    avgOp E x = x := by
  rw [avgOp_apply]
  have : ∀ e : E, ((e : LinearMap.GeneralLinearGroup (ZMod 2) U) : U →ₗ[ZMod 2] U) x = x :=
    fun e => hx e e.2
  simp only [this, Finset.sum_const, Finset.card_univ]
  exact i28_14_C_nsmul_odd hE x

theorem avgOp_comp {e' : LinearMap.GeneralLinearGroup (ZMod 2) U} (he' : e' ∈ E) (x : U) :
    avgOp E ((e' : U →ₗ[ZMod 2] U) x) = avgOp E x := by
  rw [avgOp_apply, avgOp_apply]
  exact Fintype.sum_equiv (Equiv.mulRight (⟨e', he'⟩ : E)) _ _ (fun e => rfl)

end Avg

end CFSG.HardMathSupport.Solomon.Coordinator
