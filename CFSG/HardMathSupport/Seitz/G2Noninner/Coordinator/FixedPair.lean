module

public import CFSG.LieType.SeitzGeneration.OuterRank2

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator

open CFSG.LieType.SeitzGeneration

variable {P : Type*} [Group P] {p : ℕ}

theorem false_of_fixed_pair_sup [Finite P] (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) {E : Subgroup (MulAut P)}
    (hs : NarrowScope p E) {f : MulAut P}
    (hfX : f ∈ (MulAut.conj : P →* MulAut P).range ⊔ E) (hf : f ^ p = 1)
    (hfout : ∀ x, f ≠ MulAut.conj x) {α β : P} (hcomm : Commute α β) (hα : α ^ p = 1)
    (hβ : β ^ p = 1) (hind : ∀ i j : ℤ, α ^ i * β ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j)
    (hfα : f α = α) (hfβ : f β = β) : False := by
  rcases hs.2 with h1 | h2
  · exact false_of_two_independent hp h1 hcomm hα hβ hind
  · have := finite_mulAut (P := P)
    set X : Subgroup (MulAut P) := (MulAut.conj : P →* MulAut P).range ⊔ E with hX
    have hαX : MulAut.conj α ∈ X := Subgroup.mem_sup_left ⟨α, rfl⟩
    have hβX : MulAut.conj β ∈ X := Subgroup.mem_sup_left ⟨β, rfl⟩
    let e₁ : X := ⟨MulAut.conj α, hαX⟩
    let e₂ : X := ⟨MulAut.conj β, hβX⟩
    let e₃ : X := ⟨f, hfX⟩
    have hcf : ∀ x : P, f x = x → Commute (MulAut.conj x) f := fun x hx => by
      have := mulAut_mul_conj_mul_inv f x
      rw [hx] at this
      exact ((mul_inv_eq_iff_eq_mul.mp this).symm : MulAut.conj x * f = f * MulAut.conj x)
    refine false_of_three_independent (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) hp h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact Subtype.ext (by
        change MulAut.conj α * MulAut.conj β = MulAut.conj β * MulAut.conj α
        rw [← map_mul, ← map_mul, hcomm.eq])
    · exact Subtype.ext (hcf α hfα).eq
    · exact Subtype.ext (hcf β hfβ).eq
    · exact Subtype.ext (by
        change MulAut.conj α ^ p = 1
        rw [← map_pow, hα, map_one])
    · exact Subtype.ext (by
        change MulAut.conj β ^ p = 1
        rw [← map_pow, hβ, map_one])
    · exact Subtype.ext hf
    · intro i j l hijl
      have h3 : MulAut.conj α ^ i * MulAut.conj β ^ j * f ^ l = 1 := by
        have := congrArg Subtype.val hijl
        simpa [e₁, e₂, e₃] using this
      have hfl : f ^ l = (MulAut.conj (α ^ i * β ^ j))⁻¹ := by
        rw [map_mul, map_zpow, map_zpow]
        exact eq_inv_of_mul_eq_one_right h3
      have hpl : (p : ℤ) ∣ l := by
        by_contra hl
        refine hfout _ (mem_range_conj_of_pow_mem hp hf hl ?_).choose_spec.symm
        rw [hfl]
        exact inv_mem ⟨_, rfl⟩
      have hfl1 : f ^ l = 1 := by
        obtain ⟨m, rfl⟩ := hpl
        rw [_root_.zpow_mul, zpow_natCast, hf, one_zpow]
      rw [hfl1, mul_one, ← map_zpow, ← map_zpow, ← map_mul] at h3
      have := hind i j (hinj (by rw [h3, map_one]))
      exact ⟨this.1, this.2, hpl⟩

end CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator
