module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility
public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

open scoped Classical

namespace CFSG.Semidihedral.UnitaryBranch

theorem exists_int_of_isIntegral_rat {z : ℂ} (hz : IsIntegral ℤ z) {r : ℚ} (hr : z = r) :
    ∃ n : ℤ, z = n := by
  have hrat : IsIntegral ℤ r := IsIntegral.tower_bot_of_field (B := ℂ) (by
    simpa only [← hr, eq_ratCast] using hz)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrat
  refine ⟨n, ?_⟩
  rw [hr, ← hn]
  simp

theorem card_conjClass_eq_index {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer {g}).index := by
  have e : (ConjClasses.mk g).carrier ≃ G ⧸ Subgroup.centralizer {g} :=
    (Set.equivOfEq (ConjAct.orbit_eq_carrier_conjClasses g).symm).trans
      ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
        (Subgroup.quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g)))
  rw [Nat.card_congr e]
  rfl

theorem card_centralizer_mul_dvd_of_character_eq_one {G : Type} [Group G] [Finite G]
    {ψ : G → ℂ} (hψ : ψ ∈ CFSG.BlocksIrr G) {d : ℕ} (hd : ψ 1 = (d : ℂ)) {g : G}
    (hg : ψ g = 1) : Nat.card (Subgroup.centralizer {g}) * d ∣ Nat.card G := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hψ
  have : Representation.IsIrreducible ρ := hirr
  set c := ConjClasses.mk g
  have hgc : g ∈ c.carrier := ConjClasses.mem_carrier_mk
  have hint := CFSG.Theory.Character.classSumScalar_isIntegral (ρ := ρ) c
  rw [CFSG.Theory.Character.classSumScalar_eq_card_mul_character_div (ρ := ρ) c hgc, hg, hd,
    mul_one, card_conjClass_eq_index] at hint
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hd
    have := CFSG.Theory.Character.irreducible_nontrivial (ρ := ρ)
    have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
    rw [Representation.char_one] at hd
    exact hpos.ne' (by exact_mod_cast hd)
  obtain ⟨m, hm⟩ := exists_int_of_isIntegral_rat hint
    (r := ((Subgroup.centralizer {g}).index : ℚ) / d)
    (by rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast])
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hm' : ((Subgroup.centralizer {g}).index : ℂ) = (m : ℂ) * d := by
    rw [← hm]
    field_simp
  have hm'' : ((Subgroup.centralizer {g}).index : ℤ) = m * d := by
    have h3 : (((Subgroup.centralizer {g}).index : ℤ) : ℂ) = ((m * d : ℤ) : ℂ) := by
      push_cast
      exact hm'
    exact_mod_cast h3
  have hmnn : 0 ≤ m := by
    by_contra hneg
    push Not at hneg
    have : m * (d : ℤ) < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast Nat.pos_of_ne_zero hd0)
    omega
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hmnn
  have hidx : (Subgroup.centralizer {g}).index = k * d := by exact_mod_cast hm''
  refine ⟨k, ?_⟩
  rw [← Subgroup.card_mul_index (Subgroup.centralizer {g}), hidx]
  ring

end CFSG.Semidihedral.UnitaryBranch
