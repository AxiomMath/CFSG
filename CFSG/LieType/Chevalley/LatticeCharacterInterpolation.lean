module

public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley

theorem exists_zpow_eq_of_isAlgClosed {k : Type*} [Field k] [IsAlgClosed k] {n : ℤ} (hn : n ≠ 0)
    (y : kˣ) : ∃ x : kˣ, x ^ n = y := by
  have hm : 0 < n.natAbs := Int.natAbs_pos.2 hn
  have key : ∀ z : kˣ, ∃ x : kˣ, x ^ n.natAbs = z := fun z => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : k) hm
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hw
      exact z.ne_zero hw.symm
    exact ⟨Units.mk0 w hw0, Units.ext (by simpa using hw)⟩
  rcases Int.natAbs_eq n with h | h
  · obtain ⟨x, hx⟩ := key y
    exact ⟨x, by rw [h, zpow_natCast, hx]⟩
  · obtain ⟨x, hx⟩ := key y⁻¹
    exact ⟨x, by rw [h, zpow_neg, zpow_natCast, hx, inv_inv]⟩

theorem algebraically_closed_lattice_character_interpolation (k : Type*) [Field k]
    [IsAlgClosed k] (r s : ℕ) (β : Fin s → Fin r → ℤ)
    (hβ : LinearIndependent ℚ fun i j => (β i j : ℚ)) (b : Fin s → kˣ) :
    ∃ a : Fin r → kˣ, ∀ i, ∏ j, a j ^ β i j = b i := by
  let _ : DivisibleBy (Additive kˣ) ℤ := divisibleByOfSMulRightSurj _ _ fun {n} hn y => by
    obtain ⟨x, hx⟩ := exists_zpow_eq_of_isAlgClosed hn (Additive.toMul y)
    refine ⟨Additive.ofMul x, ?_⟩
    change n • Additive.ofMul x = y
    rw [← ofMul_zpow, hx, ofMul_toMul]
  have hBaer : Module.Baer ℤ (Additive kˣ) := Module.Baer.of_divisible _
  have hf : Function.Injective (Fintype.linearCombination ℤ β) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h := Fintype.linearIndependent_iff.1 hβ (fun i => (c i : ℚ)) (by
      ext j
      have := congrFun hc j
      simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply] at this ⊢
      exact_mod_cast this)
    funext i
    exact_mod_cast h i
  obtain ⟨ψ, hψ⟩ := hBaer.extension_property _ hf
    (Fintype.linearCombination ℤ fun i => Additive.ofMul (b i))
  refine ⟨fun j => Additive.toMul (ψ (Pi.single j 1)), fun i => ?_⟩
  apply Additive.ofMul.injective
  rw [ofMul_prod]
  simp only [ofMul_zpow, ofMul_toMul]
  have e1 : ∑ j, β i j • ψ (Pi.single j 1) = ψ (β i) := by
    conv_rhs => rw [← Finset.univ_sum_single (β i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_zsmul, ← Pi.single_zsmul, smul_eq_mul, mul_one]
  have e2 : ψ (β i) = Additive.ofMul (b i) := by
    have := congrArg (fun φ => φ (Pi.single i 1)) hψ
    simpa [Fintype.linearCombination_apply, Pi.single_apply] using this
  rw [e1, e2]

end CFSG.LieType.Chevalley
