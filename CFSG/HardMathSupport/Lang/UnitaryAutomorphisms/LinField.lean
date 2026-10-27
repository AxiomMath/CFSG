module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinNil
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinGlue
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

theorem pi_single_map_fixed (σ : K ≃+* K) (i : Fin n) :
    (fun k => σ ((Pi.single i (1 : K) : Fin n → K) k)) = Pi.single i (1 : K) := by
  funext k
  by_cases hk : k = i <;> simp [hk]

theorem hasFixedThreePair_fieldAut {ℓ : ℕ} [Finite K] [hℓ : Fact ℓ.Prime] [CharP K ℓ]
    (hℓ3 : ℓ ≠ 3) (hn : 3 ≤ n) (σ : K ≃+* K) : HasFixedThreePair (fieldAut n K σ) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := fun h1 => by simpa [i, j] using congrArg Fin.val h1
  have h1 : (Pi.single j (1 : K) : Fin n → K) ⬝ᵥ Pi.single i 1 = 0 := by
    simp [hij.symm]
  have h2 : (Pi.single i (1 : K) : Fin n → K) ⬝ᵥ Pi.single j 1 = 0 := by
    simp [hij]
  have h3 : (Pi.single j (1 : K) : Fin n → K) ⬝ᵥ Pi.single j 1 = 1 := by
    simp
  have h4 : (Pi.single i (1 : K) : Fin n → K) ⬝ᵥ Pi.single i 1 = 1 := by
    simp
  have h3K : (3 : K) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K ℓ] at this
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_three).1 this)
  have hab : (1 : K) * -3 = -3 := one_mul _
  have hcube := rk1_pair_cube h1 h2 h3 h4 hab
  have hns := rk1_pair_not_scalar h1 h2 h3 h4 hab h3K hn
  refine hasFixedThreePair_of_sl_pair (fieldAut n K σ) (rk1SL h1 1) (rk1SL h2 (-3)) ℓ hℓ.out hℓ3
    ?_ ?_ ?_ ?_ ?_ ?_
  · refine fixed_fieldAut_of_map_eq σ _ ?_
    rw [coe_rk1SL]
    refine (map_rk1 (σ : K →+* K) _ _ _).trans ?_
    have e1 := pi_single_map_fixed σ i
    have e2 := pi_single_map_fixed σ j
    simp only [RingEquiv.coe_toRingHom, e1, e2, map_one]
  · refine fixed_fieldAut_of_map_eq σ _ ?_
    rw [coe_rk1SL]
    refine (map_rk1 (σ : K →+* K) _ _ _).trans ?_
    have e1 := pi_single_map_fixed σ i
    have e2 := pi_single_map_fixed σ j
    simp only [RingEquiv.coe_toRingHom, e1, e2, map_neg, map_ofNat]
  · exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, coe_rk1SL, rk1_pow_char h1]; rfl)
  · exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, coe_rk1SL, rk1_pow_char h2]; rfl)
  · exact Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul]
      exact hcube)
  · intro s
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact hns s

theorem hasFixedThreePair_conjAut_fieldAut {ℓ f : ℕ} [Finite K] [hℓ : Fact ℓ.Prime] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (h3 : 3 ∣ Nat.card K - 1) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (β : MulAut (projectiveSL n K)) (hβ : β = conjAut n K A * fieldAut n K σ)
    (hβ3 : β ^ 3 = 1) : HasFixedThreePair β := by
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    rw [hK] at h3
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have hpos : 0 < 3 ^ f := by positivity
    have h4 := Nat.dvd_sub h1 h3
    rw [show 3 ^ f - (3 ^ f - 1) = 1 by omega] at h4
    omega
  obtain ⟨-, hinj, -, hinter, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent (K := K) (n := n)
      hℓ.out hf hn hK
  have hmem : β ∈ semilinearAutGroup n K := mem_semilinearAutGroup_iff.mpr ⟨A, σ, hβ⟩
  have hnot : β ∉ linearAutGroup n K := by
    intro hB
    obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.mp hB
    have hf1 : fieldAut n K σ ∈ linearAutGroup n K ⊓ (fieldAut n K).range := by
      refine ⟨?_, σ, rfl⟩
      have : fieldAut n K σ = (conjAut n K A)⁻¹ * conjAut n K B := by
        rw [hB, hβ]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_linearAutGroup_iff.mpr ⟨A, rfl⟩))
        (mem_linearAutGroup_iff.mpr ⟨B, rfl⟩)
    rw [hinter, Subgroup.mem_bot] at hf1
    exact hσ (hinj (by rw [hf1, map_one]))
  have hβ1 : β ≠ 1 := fun h1 => hnot (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨-, σ', -, ⟨h, hh, hβh⟩, -⟩ :=
    hdesc 3 Nat.prime_three (Ne.symm hℓ3) β hmem hnot hord
  obtain ⟨B, hB⟩ := mem_linearAutGroup_iff.mp hh
  refine HasFixedThreePair.of_conj h ?_
  have : h⁻¹ * β * h = fieldAut n K σ' := by rw [hβh]; group
  rw [this]
  exact hasFixedThreePair_fieldAut hℓ3 hn σ'

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
