module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Representations.OddNormalizerPrimeTorsionDiagonal
import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix Subgroup MatrixGroups

section Group

variable {X : Type*} [Group X] {G R : Subgroup X} {r a : ℕ}

private theorem one_le_of_natCard_eq_pow (hR1 : R ≠ ⊥) (hRcard : Nat.card R = r ^ a) : 1 ≤ a := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hRcard)) hR1
  · exact h

theorem exists_le_normal_isMulCommutative_orderOf_eq (hr : r.Prime) (hRG : R ≤ G)
    (hRnorm : (R.subgroupOf G).Normal) (hR1 : R ≠ ⊥) (hRcard : Nat.card R = r ^ a) :
    ∃ K : Subgroup X, K ≤ R ∧ (K.subgroupOf G).Normal ∧ K ≠ ⊥ ∧ IsMulCommutative K ∧
      ∀ y ∈ K, y ≠ 1 → orderOf y = r := by
  have := hRnorm
  have ha : 1 ≤ a := one_le_of_natCard_eq_pow hR1 hRcard
  have hcard' : Nat.card ↥(R.subgroupOf G) = r ^ a := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRG).toEquiv, hRcard]
  refine ⟨((centerTorsionBy ↥(R.subgroupOf G) r).map (R.subgroupOf G).subtype).map G.subtype,
    ?_, ?_, ?_, ?_, ?_⟩
  · calc ((centerTorsionBy ↥(R.subgroupOf G) r).map (R.subgroupOf G).subtype).map G.subtype
        ≤ (R.subgroupOf G).map G.subtype := Subgroup.map_mono (Subgroup.map_subtype_le _)
      _ = R ⊓ G := R.subgroupOf_map_subtype G
      _ ≤ R := inf_le_left
  ·
    have hchar : (((centerTorsionBy ↥(R.subgroupOf G) r).map
        (R.subgroupOf G).subtype).subgroupOf (R.subgroupOf G)).Characteristic := by
      change (((centerTorsionBy ↥(R.subgroupOf G) r).map
        (R.subgroupOf G).subtype).comap (R.subgroupOf G).subtype).Characteristic
      rw [Subgroup.comap_map_eq_self_of_injective (R.subgroupOf G).subtype_injective]
      infer_instance
    have := hchar
    have h : ((centerTorsionBy ↥(R.subgroupOf G) r).map (R.subgroupOf G).subtype).Normal :=
      normal_of_characteristic_subgroupOf_of_normal (Subgroup.map_subtype_le _)
    change ((((centerTorsionBy ↥(R.subgroupOf G) r).map (R.subgroupOf G).subtype).map
      G.subtype).comap G.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
    exact h
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ G.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ (R.subgroupOf G).subtype_injective]
    exact centerTorsionBy_ne_bot hr hcard' ha
  · infer_instance
  · intro y hy hy1
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hw
    have hz1 : z ≠ 1 := by
      intro h; rw [h] at hy1; simp at hy1
    rw [orderOf_injective G.subtype G.subtype_injective,
      orderOf_injective (R.subgroupOf G).subtype (R.subgroupOf G).subtype_injective]
    exact orderOf_eq_of_mem_centerTorsionBy hr hz hz1

theorem natCard_dvd_natCard_of_le (hRG : R ≤ G) : Nat.card R ∣ Nat.card G := by
  have h := natCard_eq_natCard_range_leftCoset_mul_natCard (R.subgroupOf G)
  rw [Nat.card_congr (subgroupOfEquivOfLe hRG).toEquiv] at h
  exact Dvd.intro_left _ h.symm

theorem odd_of_natCard_eq_pow_of_odd_natCard (hRG : R ≤ G) (hR1 : R ≠ ⊥)
    (hRcard : Nat.card R = r ^ a) (hGodd : Odd (Nat.card G)) : Odd r := by
  have ha : 1 ≤ a := one_le_of_natCard_eq_pow hR1 hRcard
  refine hGodd.of_dvd_nat (dvd_trans ?_ (natCard_dvd_natCard_of_le hRG))
  rw [hRcard]
  exact dvd_pow_self r (by omega)

end Group

section Main

variable {k : Type*} [Field k] [Finite k] {p r a f q : ℕ}

theorem isMulCommutative_and_not_dvd_of_normal_prime_kernel [CharP k p] (hp : p.Prime)
    (hr : r.Prime) (hrp : r ≠ p) {G R : Subgroup (GL (Fin 2) k)}
    (hGodd : Odd (Nat.card G)) (hRG : R ≤ G) (hRnorm : (R.subgroupOf G).Normal) (hR1 : R ≠ ⊥)
    (hRcard : Nat.card R = r ^ a)
    (hRSL : R ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range) :
    IsMulCommutative G ∧ ¬ p ∣ Nat.card G := by
  obtain ⟨K, hKR, hKnorm, hK1, hKab, hKr⟩ :=
    exists_le_normal_isMulCommutative_orderOf_eq hr hRG hRnorm hR1 hRcard
  exact isMulCommutative_and_not_dvd_of_normal_abelian_prime_action hp hr
    (odd_of_natCard_eq_pow_of_odd_natCard hRG hR1 hRcard hGodd) hrp hGodd (hKR.trans hRG) hKnorm
    hK1 hKab (hKR.trans hRSL) hKr

theorem isMulCommutative_and_not_dvd_of_normal_prime_kernel_isPGroup [CharP k p] (hp : p.Prime)
    (hr : r.Prime) (hrp : r ≠ p) {G R : Subgroup (GL (Fin 2) k)}
    (hGodd : Odd (Nat.card G)) (hRG : R ≤ G) (hRnorm : (R.subgroupOf G).Normal) (hR1 : R ≠ ⊥)
    (hRp : IsPGroup r R)
    (hRSL : R ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range) :
    IsMulCommutative G ∧ ¬ p ∣ Nat.card G :=
  have : Fact r.Prime := ⟨hr⟩
  have ⟨_, hcard⟩ := hRp.exists_card_eq
  isMulCommutative_and_not_dvd_of_normal_prime_kernel hp hr hrp hGodd hRG hRnorm hR1 hcard hRSL

theorem isMulCommutative_and_not_dvd_of_normal_prime_kernel_card
    (hp : p.Prime) (_hf : 1 ≤ f) (hq : q = p ^ f) (hcard : Nat.card k = q)
    (hr : r.Prime) (hrp : r ≠ p) {G R : Subgroup (GL (Fin 2) k)}
    (hGodd : Odd (Nat.card G)) (hRG : R ≤ G) (hRnorm : (R.subgroupOf G).Normal) (hR1 : R ≠ ⊥)
    (hRcard : Nat.card R = r ^ a)
    (hRSL : R ≤ (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range) :
    IsMulCommutative G ∧ ¬ p ∣ Nat.card G :=
  have : CharP k p := charP_of_natCard_eq_prime_pow hp (by rw [hcard, hq])
  isMulCommutative_and_not_dvd_of_normal_prime_kernel hp hr hrp hGodd hRG hRnorm hR1 hRcard hRSL

end Main

end

end CFSG.FeitThompson
