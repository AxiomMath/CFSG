module

public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YH01
public import CFSG.LieType.Steinberg.CentralExt.SymplecticPerfect
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Q3.Q3T6

theorem hom_trivial3 {B : Type} [Group B] (e : B ≃* SL(2, ZMod 3)) {E : Type} [Group E]
    (φ : B →* E) (hE : ∀ x ∈ φ.range, x * x = 1) : ∀ r, φ r = 1 := by
  have hP : IsPGroup 2 φ.range := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have := hE x.1 x.2
    simpa [pow_two] using this
  have : Finite B := Finite.of_equiv _ e.toEquiv.symm
  have : Finite φ.range := Finite.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hB : Nat.card B = 24 := by
    rw [Nat.card_congr e.toEquiv, Aut.sl2Three_natCard]
  have hmul := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, hn, hB] at hmul
  have h3 : ¬ 3 ∣ 2 ^ n := fun h =>
    absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hker : φ.ker = ⊤ := by
    rcases normal_cases_of_equiv_sl2Three e φ.ker inferInstance with h | h | h | h
    · rw [h, Subgroup.card_bot] at hmul
      exact absurd ⟨8, by omega⟩ h3
    · have hc : Nat.card (Subgroup.center B) = 2 := by
        have h1 : Nat.card ((Subgroup.center B).map (e : B →* SL(2, ZMod 3))) =
            Nat.card (Subgroup.center B) := Subgroup.card_map_of_injective e.injective
        rw [Subgroup.map_center_eq e, Aut.natCard_center_sl2Three] at h1
        exact h1.symm
      rw [h, hc] at hmul
      exact absurd ⟨4, by omega⟩ h3
    · rw [h, natCard_commutator_of_equiv_sl2Three e] at hmul
      exact absurd ⟨1, by omega⟩ h3
    · exact h
  intro r
  have : r ∈ φ.ker := by rw [hker]; trivial
  exact this

theorem eq_of_central_ratio3 {S : Type} [Group S] (B : Subgroup S) (e : B ≃* SL(2, ZMod 3))
    (hZ : ∀ z ∈ Subgroup.center S, z * z = 1) (α : S →* S)
    (hcen : ∀ r ∈ B, α r * r⁻¹ ∈ Subgroup.center S) : ∀ r ∈ B, α r = r := by
  let κ : B →* S := MonoidHom.mk' (fun r => α r * (r : S)⁻¹) fun r r' => by
    have h := Subgroup.mem_center_iff.mp (hcen r' r'.2) (r : S)⁻¹
    have e' : α (↑(r * r')) * (↑(r * r') : S)⁻¹ = α r * ((α r' * (r' : S)⁻¹) * (r : S)⁻¹) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    rw [e', ← h]
    group
  have hκ := hom_trivial3 e κ (by
    rintro _ ⟨r, rfl⟩
    exact hZ _ (hcen r r.2))
  intro r hr
  have h2 : α r * r⁻¹ = 1 := hκ ⟨r, hr⟩
  rwa [mul_inv_eq_one] at h2

theorem nonempty_mulEquiv_sl2Three_of_card {F : Type} [Field F] (h3 : Nat.card F = 3) :
    Nonempty (SL(2, F) ≃* SL(2, ZMod 3)) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨r⟩ : Nonempty (ZMod 3 ≃+* F) :=
    ⟨FiniteField.ringEquivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, h3])⟩
  exact ⟨(slMapEquivThree r).symm⟩

theorem eq_of_central_ratio3_card {S : Type} [Group S] (B : Subgroup S) {F : Type} [Field F]
    (h3 : Nat.card F = 3) (e : B ≃* SL(2, F)) (hZ : ∀ z ∈ Subgroup.center S, z * z = 1)
    (α : S →* S) (hcen : ∀ r ∈ B, α r * r⁻¹ ∈ Subgroup.center S) : ∀ r ∈ B, α r = r := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_sl2Three_of_card h3
  exact eq_of_central_ratio3 B (e.trans e') hZ α hcen

open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (spScalars)

theorem mul_self_of_mem_spScalars {F : Type} [Field F] [Finite F] {z : StatedSp 2 F}
    (hz : z ∈ spScalars 2 F) : z * z = 1 := by
  have hcard := CFSG.LieType.Steinberg.card_statedScalars_subgroupOf_statedSp_le_two 2 F
  have hd : orderOf (⟨z, hz⟩ : ↥(spScalars 2 F)) ∣ 2 := by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(spScalars 2 F))
    have h2 : Nat.card ↥(spScalars 2 F) ∣ 2 := by
      have hpos : 0 < Nat.card ↥(spScalars 2 F) := Nat.card_pos
      interval_cases hc : Nat.card ↥(spScalars 2 F) <;> simp
    exact h1.trans h2
  have h3 : (⟨z, hz⟩ : ↥(spScalars 2 F)) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  have h4 := congrArg Subtype.val h3
  simpa [pow_two] using h4

end CFSG.ClassicalInvolution.Q3.Q3T7P25
