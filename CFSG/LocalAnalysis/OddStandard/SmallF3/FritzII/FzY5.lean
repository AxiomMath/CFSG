module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzShape
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY7
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups

abbrev FzZ4422 : Type := Multiplicative (ZMod 4 × ZMod 4 × ZMod 2 × ZMod 2)

@[expose] def Fz35b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 →
    ∃ f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4, Function.Surjective f ∧
      f.ker = (ctxW t x₁ x₂).subgroupOf (fzN2 t x₁ x₂)

@[expose] def Fz37R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ →
    Nat.card (fzR t x₁ x₂) = 2 ^ 8 ∧ Nat.card T₂ = 2 ^ 9

@[expose] def Fz316 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → ¬ FzSylow T₂ →
    (IsMulCommutative (fzP t x₁ x₂ rho) → Nonempty (↥(fzP t x₁ x₂ rho) ≃* FzZ4422)) ∧
      (¬ IsMulCommutative (fzP t x₁ x₂ rho) → Nonempty (↥(fzP t x₁ x₂ rho) ≃* SylSL3_4))

@[expose] def Fz410 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → ¬ FzSylow T₂ →
    Nonempty (↥(fzP t x₁ x₂ rho) ≃* FzZ4422) →
    ∃ M : Subgroup G, fzR t x₁ x₂ ≤ M ∧ M ≤ normalizer ((fzR t x₁ x₂ : Subgroup G) : Set G) ∧
      M.relIndex (normalizer ((fzR t x₁ x₂ : Subgroup G) : Set G)) ≤ 2 ∧
      ∃ f : ↥M →* FzSigma4, Function.Surjective f ∧ f.ker = (fzR t x₁ x₂).subgroupOf M

@[expose] def Fz319 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → ¬ FzSylow T₂ →
    Nonempty (↥(fzP t x₁ x₂ rho) ≃* SylSL3_4) →
    ∃ a₁₂ a₂₂ a₃₂ : G, FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂

@[expose] def Fz59 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G) (a₁₂ a₂₂ a₃₂ : G), FzAssumptionII G →
    Ctx t L S x₁ x₂ lam rho tau → Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ →
    ¬ FzSylow T₂ → FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ → ¬ 2 ^ 11 ∣ Nat.card G → False

theorem fzY7_of_split (h316 : Fz316) (h37 : Fz37R) (h410 : Fz410) : FzY7 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns hab
  have hP := (h316 G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns).1 hab
  obtain ⟨hR, -⟩ := h37 G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  obtain ⟨M, hRM, -, -, f, hf, hker⟩ := h410 G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns hP
  have hcard : Nat.card (fzR t x₁ x₂) * 24 = Nat.card M := by
    have h1 := Subgroup.card_ker_mul_card_of_surjective hf
    have h2 : Nat.card (fzR t x₁ x₂ |>.subgroupOf M) = Nat.card (fzR t x₁ x₂) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv
    have h3 : Nat.card FzSigma4 = 24 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [hker, h2, h3] at h1
    exact h1
  have hdvd : Nat.card M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
  rw [← hcard, hR] at hdvd
  exact (Dvd.intro (3 : ℕ) (by norm_num)).trans hdvd

theorem fzY8_of_split (h316 : Fz316) (h319 : Fz319) (h59 : Fz59) : FzY8 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns hnab hbd
  have hP := (h316 G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns).2 hnab
  obtain ⟨a₁₂, a₂₂, a₃₂, hsh⟩ := h319 G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns hP
  exact h59 G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hr4 hctx hK hT hns hsh hbd

end CFSG.OddStandard.SmallF3.FritzII
