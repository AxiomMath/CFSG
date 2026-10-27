module

public import CFSG.CharacterTheory.Wreathed.BaseReduction
public import CFSG.GroupTheory.KleinFourAutomorphism

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem twice_half_two_pow (n : ℕ) (hn : 1 ≤ n) :
    2 * 2 ^ (n - 1) = 2 ^ n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have heq : n = k + 1 := by omega
  rw [heq]
  simp [pow_succ, Nat.mul_comm]

@[expose] def baseOmega (m : ℕ) : Subgroup (baseSubgroup m) where
  carrier := {b | b ^ 2 = 1}
  one_mem' := one_pow 2
  mul_mem' := by
    intro a b ha hb
    change a ^ 2 = 1 at ha
    change b ^ 2 = 1 at hb
    change (a * b) ^ 2 = 1
    have hc : Commute a b := (base_is_abelian m).1.1 a b
    rw [hc.mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro b hb
    change b ^ 2 = 1 at hb
    change b⁻¹ ^ 2 = 1
    rw [inv_pow, hb, inv_one]

@[simp] theorem mem_baseOmega (m : ℕ) (b : baseSubgroup m) :
    b ∈ baseOmega m ↔ b ^ 2 = 1 := Iff.rfl

theorem base_pow_modulus (m : ℕ) (b : baseSubgroup m) : b ^ m = 1 := by
  apply (baseHomocyclicEquiv m).injective
  rw [map_pow, map_one]
  have he := CFSG.standardHomocyclicCover_exponent (Multiplicative (ZMod 2)) m
  simpa only [he] using Monoid.pow_exponent_eq_one (baseHomocyclicEquiv m b)

@[expose] def baseHalfPower (n : ℕ) :
    baseSubgroup (2 ^ n) →* baseSubgroup (2 ^ n) where
  toFun b := b ^ (2 ^ (n - 1))
  map_one' := one_pow _
  map_mul' a b := by
    have hc : Commute a b := (base_is_abelian (2 ^ n)).1.1 a b
    exact hc.mul_pow _

@[simp] theorem baseHalfPower_apply (n : ℕ) (b : baseSubgroup (2 ^ n)) :
    baseHalfPower n b = b ^ (2 ^ (n - 1)) := rfl

theorem baseHalfPower_mem_omega (n : ℕ) (hn : 1 ≤ n)
    (b : baseSubgroup (2 ^ n)) : baseHalfPower n b ∈ baseOmega (2 ^ n) := by
  change (b ^ (2 ^ (n - 1))) ^ 2 = 1
  rw [← pow_mul, Nat.mul_comm _ 2, twice_half_two_pow n hn]
  exact base_pow_modulus _ b

theorem half_two_power_smul_eq_zero_iff (n : ℕ) (hn : 1 ≤ n) (c : ZMod (2 ^ n)) :
    (2 ^ (n - 1)) • c = 0 ↔
      ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt hn)) (ZMod 2) c = 0 := by
  let : NeZero (2 ^ n) := ⟨pow_ne_zero _ (by decide)⟩
  have heq : (2 ^ (n - 1)) • c =
      ((2 ^ (n - 1) * c.val : ℕ) : ZMod (2 ^ n)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  have hdiv (r : ℕ) : 2 ^ n ∣ 2 ^ (n - 1) * r ↔ 2 ∣ r := by
    rw [← twice_half_two_pow n hn, Nat.mul_comm 2 (2 ^ (n - 1)),
      Nat.mul_dvd_mul_iff_left (pow_pos (by decide) _)]
  rw [heq, ZMod.natCast_eq_zero_iff, hdiv, ZMod.castHom_apply,
    ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

theorem baseHalfPower_eq_one_iff_reduction_eq_one (n : ℕ) (hn : 1 ≤ n)
    (b : baseSubgroup (2 ^ n)) :
    baseHalfPower n b = 1 ↔
      CFSG.standardHomocyclicCoverReduction (Multiplicative (ZMod 2)) 2 n hn
        (baseHomocyclicEquiv (2 ^ n) b) = 1 := by
  rw [← (baseHomocyclicEquiv (2 ^ n)).injective.eq_iff]
  rw [baseHalfPower_apply, map_pow, map_one]
  change (2 ^ (n - 1)) • Multiplicative.toAdd (baseHomocyclicEquiv (2 ^ n) b) = 0 ↔
    CFSG.standardHomocyclicCoverAddReduction (Multiplicative (ZMod 2)) 2 n hn
      (Multiplicative.toAdd (baseHomocyclicEquiv (2 ^ n) b)) = 0
  constructor
  · intro h
    funext i
    exact (half_two_power_smul_eq_zero_iff n hn _).mp (congrFun h i)
  · intro h
    funext i
    exact (half_two_power_smul_eq_zero_iff n hn _).mpr (congrFun h i)

theorem baseHalfPower_ker (n : ℕ) (hn : 1 ≤ n) :
    (baseHalfPower n).ker = frattini (baseSubgroup (2 ^ n)) := by
  ext b
  rw [MonoidHom.mem_ker, baseHalfPower_eq_one_iff_reduction_eq_one n hn,
    ← baseFrattiniQuotientEquiv_mk n hn b]
  rw [← (baseFrattiniQuotientEquiv n hn).map_one,
    (baseFrattiniQuotientEquiv n hn).injective.eq_iff]
  exact QuotientGroup.eq_one_iff b

theorem exists_half_two_power_smul_of_two_smul_eq_zero
    (n : ℕ) (hn : 1 ≤ n) (c : ZMod (2 ^ n)) (hc : 2 • c = 0) :
    ∃ d : ZMod (2 ^ n), (2 ^ (n - 1)) • d = c := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases (two_smul_eq_zero_iff k c).mp hc with rfl | rfl
  · exact ⟨0, nsmul_zero _⟩
  · refine ⟨1, ?_⟩
    simp [nsmul_eq_mul]

theorem baseHalfPower_range (n : ℕ) (hn : 1 ≤ n) :
    (baseHalfPower n).range = baseOmega (2 ^ n) := by
  apply le_antisymm
  · rintro b ⟨a, rfl⟩
    exact baseHalfPower_mem_omega n hn a
  · intro b hb
    have hsq := congrArg (baseHomocyclicEquiv (2 ^ n)) hb
    rw [map_pow, map_one] at hsq
    change 2 • Multiplicative.toAdd (baseHomocyclicEquiv (2 ^ n) b) = 0 at hsq
    have hcoord : ∀ i : Multiplicative (ZMod 2), ∃ d : ZMod (2 ^ n),
        (2 ^ (n - 1)) • d = Multiplicative.toAdd (baseHomocyclicEquiv (2 ^ n) b) i := by
      intro i
      exact exists_half_two_power_smul_of_two_smul_eq_zero n hn _ (congrFun hsq i)
    choose d hd using hcoord
    refine ⟨(baseHomocyclicEquiv (2 ^ n)).symm (Multiplicative.ofAdd d), ?_⟩
    apply (baseHomocyclicEquiv (2 ^ n)).injective
    rw [baseHalfPower_apply, map_pow, MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    funext i
    exact hd i

@[expose] def baseHalfPowerToOmega (n : ℕ) (hn : 1 ≤ n) :
    baseSubgroup (2 ^ n) →* baseOmega (2 ^ n) :=
  (baseHalfPower n).codRestrict (baseOmega (2 ^ n)) (baseHalfPower_mem_omega n hn)

@[simp] theorem baseHalfPowerToOmega_coe (n : ℕ) (hn : 1 ≤ n)
    (b : baseSubgroup (2 ^ n)) :
    (baseHalfPowerToOmega n hn b : baseSubgroup (2 ^ n)) = b ^ (2 ^ (n - 1)) := rfl

theorem baseHalfPowerToOmega_ker (n : ℕ) (hn : 1 ≤ n) :
    (baseHalfPowerToOmega n hn).ker = frattini (baseSubgroup (2 ^ n)) := by
  rw [← baseHalfPower_ker n hn]
  ext b
  change (⟨baseHalfPower n b, baseHalfPower_mem_omega n hn b⟩ : baseOmega (2 ^ n)) = 1 ↔
    baseHalfPower n b = 1
  exact Subtype.ext_iff

theorem baseHalfPowerToOmega_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (baseHalfPowerToOmega n hn) := by
  intro b
  have hb : b.val ∈ (baseHalfPower n).range := by
    rw [baseHalfPower_range n hn]
    exact b.property
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, Subtype.ext ha⟩

@[expose] def baseFrattiniOmegaEquiv (n : ℕ) (hn : 1 ≤ n) :
    baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n)) ≃* baseOmega (2 ^ n) :=
  QuotientGroup.liftEquiv (frattini (baseSubgroup (2 ^ n)))
    (baseHalfPowerToOmega_surjective n hn) (baseHalfPowerToOmega_ker n hn).symm

@[simp] theorem baseFrattiniOmegaEquiv_mk (n : ℕ) (hn : 1 ≤ n)
    (b : baseSubgroup (2 ^ n)) :
    (baseFrattiniOmegaEquiv n hn
      ((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n)))) b) : baseSubgroup (2 ^ n)) =
        b ^ (2 ^ (n - 1)) := rfl

instance baseOmega_characteristic (m : ℕ) : (baseOmega m).Characteristic := by
  apply Subgroup.characteristic_iff_comap_eq.mpr
  intro a
  ext b
  change a b ^ 2 = 1 ↔ b ^ 2 = 1
  constructor
  · intro hb
    apply a.injective
    rw [map_pow, map_one]
    exact hb
  · intro hb
    rw [← map_pow, hb, map_one]

@[expose] def baseOmegaAutAction (m : ℕ) :
    MulAut (baseSubgroup m) →* MulAut (baseOmega m) :=
  MulAut.characteristic (baseOmega m)

@[simp] theorem baseOmegaAutAction_coe (m : ℕ) (a : MulAut (baseSubgroup m))
    (b : baseOmega m) :
    (baseOmegaAutAction m a b : baseSubgroup m) = a b.val :=
  MulAut.characteristic_apply_apply_coe _ a b

theorem baseFrattiniOmegaEquiv_intertwines (n : ℕ) (hn : 1 ≤ n)
    (a : MulAut (baseSubgroup (2 ^ n)))
    (q : baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n))) :
    baseFrattiniOmegaEquiv n hn
      (CFSG.LargeEvenClassification.Helpers.frattiniAutAction (baseSubgroup (2 ^ n)) a q) =
        baseOmegaAutAction (2 ^ n) a (baseFrattiniOmegaEquiv n hn q) := by
  induction q using QuotientGroup.induction_on with
  | H b =>
    apply Subtype.ext
    change (a b) ^ (2 ^ (n - 1)) = a (b ^ (2 ^ (n - 1)))
    exact (map_pow a b _).symm

theorem baseOmegaAutAction_eq_congr_frattini (n : ℕ) (hn : 1 ≤ n) :
    baseOmegaAutAction (2 ^ n) =
      (MulAut.congr (baseFrattiniOmegaEquiv n hn)).toMonoidHom.comp
        (CFSG.LargeEvenClassification.Helpers.frattiniAutAction (baseSubgroup (2 ^ n))) := by
  apply MonoidHom.ext
  intro a
  apply MulEquiv.ext
  intro b
  change baseOmegaAutAction (2 ^ n) a b =
    baseFrattiniOmegaEquiv n hn
      (CFSG.LargeEvenClassification.Helpers.frattiniAutAction (baseSubgroup (2 ^ n)) a
        ((baseFrattiniOmegaEquiv n hn).symm b))
  rw [baseFrattiniOmegaEquiv_intertwines, MulEquiv.apply_symm_apply]

theorem baseOmega_card (n : ℕ) (hn : 1 ≤ n) : Nat.card (baseOmega (2 ^ n)) = 4 := by
  rw [← Nat.card_congr (baseFrattiniOmegaEquiv n hn).toEquiv]
  exact base_frattini_quotient_card n hn

theorem baseOmega_isKleinFour (n : ℕ) (hn : 1 ≤ n) : IsKleinFour (baseOmega (2 ^ n)) := by
  refine ⟨baseOmega_card n hn, ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv
    ((baseFrattiniOmegaEquiv n hn).symm.trans (baseFrattiniQuotientEquiv n hn))]
  exact CFSG.standardHomocyclicCover_exponent (Multiplicative (ZMod 2)) 2

theorem baseOmega_nonidentity_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {b : baseOmega (2 ^ n) // b ≠ 1} = 3 := by
  let := baseOmega_isKleinFour n hn
  exact CFSG.kleinFour_nonidentity_card _

theorem baseOmegaAutAction_image_card (n : ℕ) (hn : 1 ≤ n)
    (H : Subgroup (MulAut (baseSubgroup (2 ^ n)))) :
    Nat.card (H.map (baseOmegaAutAction (2 ^ n))) =
      Nat.card (H.map (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
        (baseSubgroup (2 ^ n)))) := by
  rw [baseOmegaAutAction_eq_congr_frattini n hn, ← Subgroup.map_map]
  exact Nat.card_congr ((MulAut.congr (baseFrattiniOmegaEquiv n hn)).subgroupMap
    (H.map (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n))))).toEquiv.symm

theorem baseOmega_transitive_of_frattini_image_card_six (n : ℕ) (hn : 1 ≤ n)
    (H : Subgroup (MulAut (baseSubgroup (2 ^ n))))
    (hcard : Nat.card (H.map (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n)))) = 6)
    (x y : baseOmega (2 ^ n)) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : H, a.val x.val = y.val := by
  let := baseOmega_isKleinFour n hn
  have hcardOmega : Nat.card (H.map (baseOmegaAutAction (2 ^ n))) = 6 := by
    rw [baseOmegaAutAction_image_card n hn H, hcard]
  obtain ⟨a, ha⟩ := CFSG.kleinFour_automorphism_subgroup_transitive (baseOmega (2 ^ n))
    (H.map (baseOmegaAutAction (2 ^ n))) hcardOmega x y hx hy
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp a.property
  refine ⟨⟨b, hb⟩, ?_⟩
  have h := congrArg (fun z : baseOmega (2 ^ n) => z.val) ha
  rw [← hba, baseOmegaAutAction_coe] at h
  exact h

theorem base_involutions_transitive_of_frattini_image_card_six (n : ℕ) (hn : 1 ≤ n)
    (H : Subgroup (MulAut (baseSubgroup (2 ^ n))))
    (hcard : Nat.card (H.map (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n)))) = 6)
    (x y : baseSubgroup (2 ^ n)) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ a : H, a.val x = y := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hxpow, hxne⟩ := orderOf_eq_prime_iff.mp hx
  obtain ⟨hypow, hyne⟩ := orderOf_eq_prime_iff.mp hy
  exact baseOmega_transitive_of_frattini_image_card_six n hn H hcard
    ⟨x, hxpow⟩ ⟨y, hypow⟩
    (by intro h; exact hxne (congrArg Subtype.val h))
    (by intro h; exact hyne (congrArg Subtype.val h))

end CFSG.Wreathed
