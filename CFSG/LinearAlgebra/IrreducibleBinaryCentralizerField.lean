module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.LinearAlgebra

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem prod_pow_sub_pow_eq_two_pow_mul_odd {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∃ r, Odd r ∧ ∏ i : Fin m, ((2 ^ d) ^ m - (2 ^ d) ^ (i : ℕ)) = 2 ^ (d * (m * (m - 1) / 2)) * r
    := by
  have hfac : ∀ i : Fin m, (2 ^ d) ^ m - (2 ^ d) ^ (i : ℕ) =
      2 ^ (d * i) * ((2 ^ d) ^ (m - i) - 1) := by
    intro i
    have hi : (i : ℕ) ≤ m := i.2.le
    rw [Nat.mul_sub, mul_one, pow_mul, ← pow_add, Nat.add_sub_cancel' hi]
  refine ⟨∏ i : Fin m, ((2 ^ d) ^ (m - i) - 1), ?_, ?_⟩
  · refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i _ => ?_
    have hpos : 0 < m - (i : ℕ) := Nat.sub_pos_of_lt i.2
    have heven : Even ((2 ^ d) ^ (m - i)) := by
      rw [← pow_mul]
      exact (Nat.even_pow.2 ⟨even_two, (Nat.mul_pos hd hpos).ne'⟩)
    have h1 : 1 ≤ (2 ^ d) ^ (m - i) := Nat.one_le_pow _ _ (by positivity)
    exact Nat.Even.sub_odd h1 heven odd_one
  · rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    congr 2
    rw [← Finset.mul_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun i => i) m, ← Finset.sum_range_id_mul_two,
      Nat.mul_div_cancel _ two_pos]

theorem adjoin_singleton_mul_comm (a : Module.End (ZMod 2) V)
    (x y : Algebra.adjoin (ZMod 2) {a}) : x * y = y * x :=
  (Algebra.isMulCommutative_adjoin (ZMod 2) (Set.pairwise_singleton _ _)).is_comm.comm x y

theorem adjoin_singleton_le_centralizer (a : Module.End (ZMod 2) V)
    {S : Set (Module.End (ZMod 2) V)} (ha : ∀ s ∈ S, s * a = a * s) :
    Algebra.adjoin (ZMod 2) {a} ≤ Subalgebra.centralizer (ZMod 2) S := by
  rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
    Subalgebra.mem_centralizer_iff]
  exact ha

theorem irreducible_binary_linear_centralizer_field_degree_bound [FiniteDimensional (ZMod 2) V]
    {n : ℕ} (hn : 1 ≤ n) (hV : Module.finrank (ZMod 2) V = n)
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ h ∈ H, ∀ w ∈ W, (h : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (a : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (ha : a ∈ Subgroup.centralizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) :
    ∃ hR : IsField (Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) V)}),
      ∃ d : ℕ, 0 < d ∧ d ∣ n ∧
        Nat.card (Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) V)}) = 2 ^ d ∧
        orderOf a ∣ 2 ^ d - 1 ∧
        (letI := hR.toField
          ∃ φ : H →* GL (Fin (n / d)) (Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) V)}),
            Function.Injective φ) ∧
        2 ^ (Nat.card H).factorization 2 ∣ 2 ^ (d * (n / d * (n / d - 1) / 2)) := by
  classical
  set R := Algebra.adjoin (ZMod 2) {(a : Module.End (ZMod 2) V)} with hRdef
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hcomm : ∀ x ∈ R, ∀ h ∈ H,
      (h : Module.End (ZMod 2) V) * x = x * (h : Module.End (ZMod 2) V) := by
    have hle := adjoin_singleton_le_centralizer (a : Module.End (ZMod 2) V)
      (S := {f | ∃ h ∈ H, (h : Module.End (ZMod 2) V) = f}) (by
        rintro _ ⟨h, hh, rfl⟩
        have := Subgroup.mem_centralizer_iff.1 ha h hh
        rw [← Units.val_mul, ← Units.val_mul, this])
    intro x hx h hh
    exact (Subalgebra.mem_centralizer_iff _).1 (hle hx) _ ⟨h, hh, rfl⟩
  have hinj : ∀ x ∈ R, x ≠ 0 → Function.Injective x := by
    intro x hx hx0
    have hker := hirr (LinearMap.ker x) fun h hh w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      rw [← Module.End.mul_apply, ← hcomm x hx h hh, Module.End.mul_apply, hw, map_zero]
    rcases hker with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hx0
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[ZMod 2] V))
  have : Finite R := Subtype.finite
  have hR : IsField R := by
    refine ⟨⟨0, 1, fun h => ?_⟩, fun x y => adjoin_singleton_mul_comm _ x y, fun {x} hx => ?_⟩
    · have h' := congrArg (fun y : R => (y : Module.End (ZMod 2) V)) h
      exact zero_ne_one h'
    · have hxi := hinj x x.2 fun h => hx (Subtype.ext h)
      have hmul : Function.Injective fun y : R => x * y := by
        intro y y' hyy'
        apply Subtype.ext
        refine LinearMap.ext fun v => hxi ?_
        exact congrArg (fun z : R => (z : Module.End (ZMod 2) V) v) hyy'
      obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hmul) 1
      exact ⟨y, hy⟩
  let _i := hR.toField
  have : Fintype R := Fintype.ofFinite R
  have : Module.Finite (ZMod 2) R := Module.Finite.of_finite
  have : Module.Finite R V := Module.Finite.of_restrictScalars_finite (ZMod 2) R V
  set d := Module.finrank (ZMod 2) R with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hcardR : Nat.card R = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hdm : d * Module.finrank R V = n := by
    rw [hd, Module.finrank_mul_finrank (ZMod 2) R V, hV]
  have hm : Module.finrank R V = n / d := by
    rw [← hdm, Nat.mul_div_cancel_left _ hdpos]
  refine ⟨hR, d, hdpos, Dvd.intro _ hdm, hcardR, ?_, ?_⟩
  ·
    let x : R := ⟨(a : Module.End (ZMod 2) V), Algebra.subset_adjoin rfl⟩
    have hx0 : x ≠ 0 := by
      intro h
      have h' : (a : Module.End (ZMod 2) V) = 0 := congrArg Subtype.val h
      have h1 := a.inv_mul
      rw [h', mul_zero] at h1
      exact zero_ne_one h1
    have hpow := FiniteField.pow_card_sub_one_eq_one x hx0
    rw [Fintype.card_eq_nat_card, hcardR] at hpow
    refine orderOf_dvd_of_pow_eq_one (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact congrArg Subtype.val hpow
  let lin : H → (V →ₗ[R] V) := fun h =>
    { toFun := ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      map_add' := map_add _
      map_smul' := fun r v => by
        change ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V)
            ((r : Module.End (ZMod 2) V) v) =
          (r : Module.End (ZMod 2) V)
            (((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) v)
        rw [← Module.End.mul_apply, hcomm r r.2 h h.2, Module.End.mul_apply] }
  have hlin : ∀ (h : H) (v : V),
      lin h v = ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v :=
    fun _ _ => rfl
  have hinv : ∀ (h : H) (v : V), lin h (lin h⁻¹ v) = v := by
    intro h v
    rw [hlin, hlin, ← Module.End.mul_apply, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply]
  have hinv' : ∀ (h : H) (v : V), lin h⁻¹ (lin h v) = v := by
    intro h v
    rw [hlin, hlin, ← Module.End.mul_apply, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply]
  let ψ : H →* LinearMap.GeneralLinearGroup R V :=
    { toFun := fun h => ⟨lin h, lin h⁻¹, LinearMap.ext (hinv h), LinearMap.ext (hinv' h)⟩
      map_one' := Units.ext (LinearMap.ext fun v => rfl)
      map_mul' := fun h h' => Units.ext (LinearMap.ext fun v => rfl) }
  have hψ : Function.Injective ψ := by
    intro h h' hh
    have := congrArg (fun g : LinearMap.GeneralLinearGroup R V => ⇑(g : V →ₗ[R] V)) hh
    exact Subtype.ext (Units.ext (LinearMap.ext fun v => congrFun this v))
  let b := Module.finBasisOfFinrankEq R V hm
  let φ : H →* GL (Fin (n / d)) R :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom).comp ψ
  have hφ : Function.Injective φ :=
    (Units.map_injective (LinearMap.toMatrixAlgEquiv b).injective).comp hψ
  refine ⟨⟨φ, hφ⟩, ?_⟩
  obtain ⟨r, hr, hprod⟩ := prod_pow_sub_pow_eq_two_pow_mul_odd hdpos (n / d)
  have hGL : Nat.card (GL (Fin (n / d)) R) = 2 ^ (d * (n / d * (n / d - 1) / 2)) * r := by
    rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hcardR, hprod]
  have hdvd : Nat.card H ∣ 2 ^ (d * (n / d * (n / d - 1) / 2)) * r := by
    rw [← hGL]
    exact Subgroup.card_dvd_of_injective φ hφ
  exact ((Nat.coprime_two_left.2 hr).pow_left _).dvd_of_dvd_mul_right
    ((Nat.ordProj_dvd _ 2).trans hdvd)

end CFSG.LinearAlgebra
