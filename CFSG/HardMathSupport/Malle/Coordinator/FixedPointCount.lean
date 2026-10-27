module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

namespace FixedPointCount

variable {G Y : Type*} [Group G] [MulAction G Y]

theorem eq_of_smul_eq_smul (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) {g h : G} {y : Y}
    (hgh : g • y = h • y) : g = h :=
  (inv_mul_eq_one.mp (hfree (h⁻¹ * g) y (by rw [mul_smul, hgh, inv_smul_smul]))).symm

open scoped IsMulCommutative in
theorem iterate_apply_eq [IsMulCommutative G] (β : G →* G) (f : Y → Y)
    (hf : ∀ (g : G) (y : Y), f (g • y) = β g • f y) {p c : G} {x : Y} (hx : f x = p • x)
    (hβp : β p = p * c) (hβc : β c = c) (n : ℕ) :
    f^[n] x = (p ^ n * c ^ (∑ i ∈ Finset.range n, i)) • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hf, hx, smul_smul, map_mul, map_pow, map_pow, hβp, hβc,
      Finset.sum_range_succ, mul_pow, pow_succ, pow_add]
    ac_rfl

theorem exists_inv_mul_eq [Finite G] [IsMulCommutative G] (β : G →* G) (Z : Subgroup G)
    (hZ : ∀ g, g ∈ Z ↔ β g = g) (hz : ∀ g, g⁻¹ * β g ∈ Z)
    (hcard : Nat.card G = Nat.card Z * Nat.card Z) {w : G} (hw : w ∈ Z) :
    ∃ g : G, g⁻¹ * β g = w := by
  let φ : G →* G := MonoidHom.mk' (fun g => g⁻¹ * β g) fun a b => by
    simp only [map_mul, mul_inv_rev]
    ac_rfl
  have hker : φ.ker = Z := by
    ext g
    rw [MonoidHom.mem_ker, hZ]
    exact inv_mul_eq_one.trans eq_comm
  have hle : φ.range ≤ Z := by
    rintro _ ⟨g, rfl⟩
    exact hz g
  have hcr : Nat.card φ.range = Nat.card Z := by
    have h := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hw' : w ∈ φ.range := by
    rw [Subgroup.eq_of_le_of_card_ge hle hcr.ge]
    exact hw
  exact MonoidHom.mem_range.mp hw'

theorem exists_apply_smul_eq [Finite G] [IsMulCommutative G] (β : G →* G) (f : Y → Y)
    (hf : ∀ (g : G) (y : Y), f (g • y) = β g • f y) (hf5 : f^[5] = id) (Z : Subgroup G)
    (hZ : ∀ g, g ∈ Z ↔ β g = g) (hΩ : ∀ g : G, g ^ 5 = 1 → g ∈ Z) (hz : ∀ g, g⁻¹ * β g ∈ Z)
    (hZ5 : ∀ z ∈ Z, z ^ 5 = 1) (hcard : Nat.card G = Nat.card Z * Nat.card Z)
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) {x : Y} {p : G} (hx : f x = p • x) :
    ∃ q : G, f (q • x) = q • x := by
  have hc : p⁻¹ * β p ∈ Z := hz p
  have h5 := iterate_apply_eq β f hf hx (mul_inv_cancel_left p (β p)).symm ((hZ _).mp hc) 5
  rw [hf5, show ∑ i ∈ Finset.range 5, i = 5 * 2 by decide, pow_mul, hZ5 _ hc, one_pow,
    mul_one] at h5
  obtain ⟨q, hq⟩ := exists_inv_mul_eq β Z hZ hz hcard (inv_mem (hΩ p (hfree _ x h5.symm)))
  refine ⟨q, ?_⟩
  rw [hf, hx, smul_smul, inv_mul_eq_iff_eq_mul.mp hq, inv_mul_cancel_right]

theorem card_modEq_of_free [Finite Y] (β : G →* G) (f : Y → Y)
    (hf : ∀ (g : G) (y : Y), f (g • y) = β g • f y) (hf5 : f^[5] = id)
    (hab : ∀ a b : G, a * b = b * a) (Z : Subgroup G) (hZ : ∀ g, g ∈ Z ↔ β g = g)
    (hΩ : ∀ g : G, g ^ 5 = 1 → g ∈ Z) (hz : ∀ g, g⁻¹ * β g ∈ Z)
    (hZ5 : ∀ z ∈ Z, z ^ 5 = 1) (hcard : Nat.card G = Nat.card Z * Nat.card Z)
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) :
    Nat.card Y ≡ Nat.card Z * Nat.card {y // f y = y} [MOD 5 * Nat.card G] ∧
      Nat.card Z ∣ Nat.card {y // f y = y} := by
  classical
  have : IsMulCommutative G := .of_comm hab
  rcases isEmpty_or_nonempty Y with hY | ⟨⟨y₀⟩⟩
  · simpa using Nat.ModEq.refl 0
  have : Finite G := Finite.of_injective (fun g : G => g • y₀) fun g h hgh =>
    eq_of_smul_eq_smul hfree hgh
  obtain ⟨π, F, hπs, hπ, hF⟩ : ∃ (π : Y → MulAction.orbitRel.Quotient G Y)
      (F : MulAction.orbitRel.Quotient G Y → MulAction.orbitRel.Quotient G Y),
      Function.Surjective π ∧ (∀ a b, π a = π b ↔ ∃ g : G, g • b = a) ∧
        ∀ y, F (π y) = π (f y) :=
    ⟨Quotient.mk _, Quotient.lift (fun y => Quotient.mk _ (f y)) (fun a b hab' => by
        obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hab'
        exact Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨β g, (hf g b).symm⟩)),
      Quotient.mk_surjective, fun a b => Quotient.eq.trans MulAction.mem_orbit_iff,
      fun _ => rfl⟩
  have hYc : Nat.card Y = Nat.card (MulAction.orbitRel.Quotient G Y) * Nat.card G := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd fun y =>
      (Subgroup.eq_bot_iff_forall _).mpr fun g hg => hfree g y hg)
  have hΩc : Nat.card (MulAction.orbitRel.Quotient G Y) ≡ Nat.card {o // F o = o} [MOD 5] := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)
    have h := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1)
      (f := (F : Function.End (MulAction.orbitRel.Quotient G Y))) (by
        show F^[5 ^ 1] = id
        funext o
        obtain ⟨y, rfl⟩ := hπs o
        rw [pow_one, ← (Function.Semiconj.iterate_right (fun y => (hF y).symm) 5 y), hf5]
        rfl)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
    exact h
  have hD : ∀ o : {o // F o = o}, ∃ y : Y, f y = y ∧ π y = o.1 := by
    rintro ⟨o, ho⟩
    obtain ⟨x, rfl⟩ := hπs o
    obtain ⟨p, hp⟩ := (hπ _ _).mp ((hF x).symm.trans ho)
    obtain ⟨q, hq⟩ := exists_apply_smul_eq β f hf hf5 Z hZ hΩ hz hZ5 hcard hfree hp.symm
    exact ⟨q • x, hq, (hπ _ _).mpr ⟨q, rfl⟩⟩
  choose b hb using hD
  have hFix : Nat.card {y // f y = y} = Nat.card {o // F o = o} * Nat.card Z := by
    rw [← Nat.card_prod]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun oz => ⟨(oz.2 : G) • b oz.1, ?_⟩) ⟨?_, ?_⟩)
    · rw [hf, (hZ _).mp oz.2.2, (hb oz.1).1]
    · rintro ⟨o, z⟩ ⟨o', z'⟩ h
      have h' : (z : G) • b o = (z' : G) • b o' := congrArg Subtype.val h
      obtain rfl : o = o' := Subtype.ext <|
        calc o.1 = π (b o) := (hb o).2.symm
          _ = π ((z : G) • b o) := ((hπ _ _).mpr ⟨z, rfl⟩).symm
          _ = π ((z' : G) • b o') := by rw [h']
          _ = π (b o') := (hπ _ _).mpr ⟨z', rfl⟩
          _ = o'.1 := (hb o').2
      rw [Subtype.ext (eq_of_smul_eq_smul hfree h')]
    · rintro ⟨y, hy⟩
      set o : {o // F o = o} := ⟨π y, by rw [hF, hy]⟩
      obtain ⟨g, hg⟩ := (hπ _ _).mp (hb o).2.symm
      have hgZ : g ∈ Z := (hZ g).mpr <| eq_of_smul_eq_smul hfree <|
        calc β g • b o = β g • f (b o) := by rw [(hb o).1]
          _ = f (g • b o) := (hf g (b o)).symm
          _ = g • b o := by rw [hg, hy]
      exact ⟨(o, ⟨g, hgZ⟩), Subtype.ext hg⟩
  refine ⟨?_, ⟨_, by rw [hFix, mul_comm]⟩⟩
  rw [hYc, hFix, hcard]
  convert hΩc.mul_left' (Nat.card Z * Nat.card Z) using 1 <;> ring

end FixedPointCount

variable {H X : Type*} [Group H] [MulAction H X]

def FixedPointCount.complFixedPoint (P : Subgroup H) (x₀ : X) (hx₀ : ∀ p ∈ P, p • x₀ = x₀) :
    SubMulAction P X where
  carrier := {x | x ≠ x₀}
  smul_mem' p x hx h := hx <| by
    rw [← inv_smul_smul p x, h]
    exact hx₀ _ (p⁻¹).2

variable [Finite X]

open FixedPointCount in
theorem card_modEq_fixedPoints_of_free
    (α : H ≃* H) (f : Equiv.Perm X) (hf : ∀ (h : H) (x : X), f (h • x) = α h • f x)
    (hf5 : f ^ 5 = 1)
    (P Z : Subgroup H) (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hαP : ∀ p ∈ P, α p ∈ P)
    (hZ : ∀ p, p ∈ Z ↔ p ∈ P ∧ α p = p)
    (hΩ : ∀ p ∈ P, p ^ 5 = 1 → p ∈ Z)
    (hz : ∀ p ∈ P, p⁻¹ * α p ∈ Z)
    (hZ5 : ∀ z ∈ Z, z ^ 5 = 1)
    (hcard : Nat.card P = Nat.card Z * Nat.card Z)
    (x₀ : X) (hx₀ : ∀ p ∈ P, p • x₀ = x₀) (hfx₀ : f x₀ = x₀)
    (hfree : ∀ p ∈ P, ∀ x, x ≠ x₀ → p • x = x → p = 1) :
    Nat.card X ≡ 1 + Nat.card Z * (Nat.card {x // f x = x} - 1) [MOD 5 * Nat.card P] ∧
      Nat.card {x // f x = x} ≡ 1 [MOD Nat.card Z] := by
  classical
  set S := complFixedPoint P x₀ hx₀
  obtain ⟨f', hf'⟩ : ∃ f' : S → S, ∀ y, (f' y : X) = f y :=
    ⟨fun y => ⟨f y, fun h => y.2 (f.injective (h.trans hfx₀.symm))⟩, fun _ => rfl⟩
  let β : P →* P := (α.toMonoidHom.comp P.subtype).codRestrict P fun p => hαP p p.2
  have hZc : Nat.card (Z.subgroupOf P) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fun p hp => ((hZ p).mp hp).1).toEquiv
  have key := card_modEq_of_free β f'
    (fun g y => Subtype.ext <| by
      rw [hf', SubMulAction.val_smul, SubMulAction.val_smul, hf']
      exact hf g y)
    (by
      funext y
      apply Subtype.ext
      rw [Function.Semiconj.iterate_right (f := Subtype.val) hf' 5 y, ← Equiv.Perm.coe_pow, hf5]
      rfl)
    (fun a b => Subtype.ext (hPab a a.2 b b.2)) (Z.subgroupOf P)
    (fun g => by
      rw [Subgroup.mem_subgroupOf, hZ, Subtype.ext_iff]
      exact and_iff_right g.2)
    (fun g hg => Subgroup.mem_subgroupOf.mpr (hΩ g g.2 (by simpa using congrArg Subtype.val hg)))
    (fun g => Subgroup.mem_subgroupOf.mpr (hz g g.2))
    (fun z hz' => Subtype.ext (by simpa using hZ5 _ (Subgroup.mem_subgroupOf.mp hz')))
    (by rw [hZc, hcard])
    (fun g y h => Subtype.ext (hfree g g.2 y y.2 (congrArg Subtype.val h)))
  rw [hZc] at key
  have hS : Nat.card X = Nat.card S + 1 := by
    rw [← Nat.card_congr (Equiv.optionSubtypeNe x₀), Finite.card_option]
    rfl
  have e : {t : {x // f x = x} // t ≠ ⟨x₀, hfx₀⟩} ≃ {y : S // f' y = y} :=
    { toFun := fun t => ⟨⟨t.1.1, fun h => t.2 (Subtype.ext h)⟩, Subtype.ext ((hf' _).trans t.1.2)⟩
      invFun := fun y => ⟨⟨y.1.1, (hf' y.1).symm.trans (congrArg Subtype.val y.2)⟩,
        fun h => y.1.2 (congrArg Subtype.val h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hFix : Nat.card {x // f x = x} = Nat.card {y : S // f' y = y} + 1 := by
    rw [← Nat.card_congr e, ← Finite.card_option]
    exact (Nat.card_congr (Equiv.optionSubtypeNe _)).symm
  rw [hS, hFix, Nat.add_sub_cancel, add_comm 1]
  exact ⟨key.1.add_right 1, by simpa using (Nat.modEq_zero_iff_dvd.mpr key.2).add_right 1⟩

end CFSG.HardMathSupport.Malle.Coordinator
