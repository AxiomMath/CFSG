module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallM2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.TA3
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped MatrixGroups commutatorElement

@[expose] def TwoBlockShape (F : Type) [Group F] : Prop :=
  ∀ z : F, orderOf z = 2 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁)
    (_ : Finite F₂) (B₁ B₂ I₁ I₂ : Subgroup F), Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧
      4 ≤ Nat.card F₁ ∧ 4 ≤ Nat.card F₂ ∧
      CFSG.Open.IsComponentOf B₁ (Subgroup.centralizer ({z} : Set F)) ∧
      CFSG.Open.IsComponentOf B₂ (Subgroup.centralizer ({z} : Set F)) ∧ I₁ ≤ B₁ ∧ I₂ ≤ B₂ ∧
      (∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) ∧ Nonempty (↥I₁ ≃* SL(2, F₁)) ∧
      Nonempty (↥I₂ ≃* SL(2, F₂))

theorem not_twinPair_of_twoBlockShape {F : Type} [Group F] [Finite F] (hsh : TwoBlockShape F)
    (hsmall : TwoSubgroupsFourGenerated F) : ¬ TwinPair F := by
  rintro ⟨z, X₁, X₂, u₁, u₂, hz, hX₁, hX₂, hs₁, hs₂, hu₁, hu₂, ho₁, ho₂, hsq₁, hsq₂, hne⟩
  obtain ⟨F₁, F₂, _, _, _, _, B₁, B₂, I₁, I₂, hF₁, hF₂, h4₁, h4₂, hB₁, hB₂, hI₁, hI₂, hcomm,
    ⟨e₁⟩, ⟨e₂⟩⟩ := hsh z hz
  have hc₁ : ∀ a ∈ I₁, a * u₁ = u₁ * a := fun a ha =>
    commute_of_solvable_subnormal hB₁.2.1 (isQuasisimple_of_open hB₁.2.2) hs₁ hX₁ a (hI₁ ha) u₁
      hu₁
  have hc₂ : ∀ b ∈ I₂, b * u₁ = u₁ * b := fun b hb =>
    commute_of_solvable_subnormal hB₂.2.1 (isQuasisimple_of_open hB₂.2.2) hs₁ hX₁ b (hI₂ hb) u₁
      hu₁
  obtain ⟨φ₁, hi₁, hr₁, -⟩ := exists_q8_of_mulEquiv_sl2 hF₁ I₁ e₁
  obtain ⟨φ₂, hi₂, hr₂, -⟩ := exists_q8_of_mulEquiv_sl2 hF₂ I₂ e₂
  have hu4 : u₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one u₁
    rwa [ho₁] at this
  let χ := LocalAnalysis.ComponentInitial.zmodHom 4 u₁ hu4
  have hχi : Function.Injective χ := Q5Cube.zmodHom_injective hu4 ho₁
  have hχc : ∀ (v : F), Commute v u₁ → ∀ m, Commute v (χ m) := by
    intro v hv m
    rcases Q5Cube.z4_cases m with rfl | rfl | rfl | rfl <;>
      simp only [map_one, map_pow, LocalAnalysis.ComponentInitial.zmodHom_ofAdd_one, χ]
    · exact Commute.one_right v
    · exact hv
    · exact hv.pow_right 2
    · exact hv.pow_right 3
  exact Q5Cube.not_gen4_of_q8_q8_z4 φ₁ φ₂ χ hi₁ hi₂ hχi
    (fun x y => hcomm _ (hr₁ x) _ (hr₂ y))
    (fun x m => hχc _ (hc₁ _ (hr₁ x)) m) (fun y m => hχc _ (hc₂ _ (hr₂ y)) m) hsmall

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
