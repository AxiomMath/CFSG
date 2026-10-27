module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CharacterTheory.Semidihedral.SemilinearOddExtensions

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.GorensteinWalter

namespace PrimeTorusAlignment

theorem card_fixed_eq_mod_of_prime_order {F : Type} [Field F] [Finite F] {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) {σ : Equiv.Perm (Omega F)} (hσG : σ ∈ coordinateG F)
    (hσ1 : σ ≠ 1) (hσℓ : σ ^ ℓ = 1) :
    Nat.card {x : Omega F // σ x = x} = (Nat.card F + 1) % ℓ := by
  have hle : Nat.card {x : Omega F // σ x = x} ≤ 2 := by
    rw [← coordinatePSLAction_range_eq_G] at hσG
    obtain ⟨g, rfl⟩ := hσG
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hσ1 (map_one _)
    let cE : Omega F ≃ PSL2ProjectiveLine F :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F
    have he : {x : Omega F // coordinatePSLAction F g x = x} ≃
        {y : PSL2ProjectiveLine F // g • y = y} :=
      cE.subtypeEquiv (fun x => by
        rw [← coordinatePSLAction_point]
        exact cE.injective.eq_iff.symm)
    rw [Nat.card_congr he]
    exact psl2_fixedPoint_card_le_two F g hg1
  have hp : IsPGroup ℓ (Subgroup.zpowers σ) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hσℓ hσ1
  have hmod := hp.card_modEq_card_fixedPoints (Omega F)
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) (Omega F)) =
      Nat.card {x : Omega F // σ x = x} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · rintro h ⟨τ, hτ⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k
  rw [hfix, Finite.card_option] at hmod
  have hmod' : (Nat.card F + 1) % ℓ = Nat.card {x : Omega F // σ x = x} % ℓ := hmod
  rw [hmod', Nat.mod_eq_of_lt (by omega)]

theorem card_fixed_layer_element_eq_mod {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    {F : Type} [Field F] [Finite F] (ρ : Γ →* coordinateE F) (hρ : Function.Injective ρ)
    (hL : L.map ρ = specialLayer F) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) {γ : Γ} (hγL : γ ∈ L)
    (hγ1 : γ ≠ 1) (hγℓ : γ ^ ℓ = 1) :
    Nat.card {x : Omega F // ((ρ γ : coordinateE F) : Equiv.Perm (Omega F)) x = x} =
      (Nat.card F + 1) % ℓ := by
  have hmem : ρ γ ∈ specialLayer F := hL ▸ Subgroup.mem_map_of_mem ρ hγL
  have hG : ((ρ γ : coordinateE F) : Equiv.Perm (Omega F)) ∈ coordinateG F := hmem
  refine card_fixed_eq_mod_of_prime_order hℓ3 hG ?_ ?_
  · intro h
    apply hγ1
    apply hρ
    rw [map_one]
    exact Subtype.ext h
  · rw [← Subgroup.coe_pow, ← map_pow, hγℓ, map_one, Subgroup.coe_one]

theorem succ_mod_eq_one_sub {q ℓ : ℕ} {e : ℤ} (he : e = 1 ∨ e = -1) (hℓ3 : 3 ≤ ℓ)
    (h : 2 * (ℓ : ℤ) = q + e) : (((q + 1) % ℓ : ℕ) : ℤ) = 1 - e := by
  rcases he with rfl | rfl
  · have hq : q + 1 = ℓ * 2 := by omega
    rw [hq, Nat.mul_mod_right]
    norm_num
  · have hq : q + 1 = 2 + ℓ * 2 := by omega
    rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    norm_num

end PrimeTorusAlignment

end CFSG.Semidihedral.Principal
