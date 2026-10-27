module

public import CFSG.CGT.Timmesfeld75.Sec5NineLift
public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n : ℕ}

theorem sec6Ctx_of_natural (h214 : Lemma214) (hInv : InvolutionClassInput)
    (hIso : Section3IsoInput) (hy : StepHyp T T₁)
    (hq : Nat.card T / Nat.card (normIn T T₁) = 2 ^ 1) (hT : Nat.card T = (2 ^ 1) ^ n)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) : Sec6Ctx T T₁ n 1 := by
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hy.pair.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  exact ⟨hy, hS, hI, hq, hT, Or.inr (Or.inl hnat)⟩

theorem normIn_le_normalizer : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) :=
  fun _ hz => (mem_normIn.1 hz).2

theorem hSub_data (T T₁ : Subgroup G) :
    T ≤ hSub T (normIn T₁ T) ∧ hSub T (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) ∧
      ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ h ∈ hSub T (normIn T₁ T),
        g * h * g⁻¹ ∈ hSub T (normIn T₁ T) :=
  ⟨left_le_hSub, hSub_le_normalizer normIn_le_normalizer, fun _ hg _ hh =>
    mul_mul_inv_mem_hSub hg hh⟩

end CFSG.CGT.T75P
