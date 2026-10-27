module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY5

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

@[expose] def fz59N3 (t x₁ x₂ : G) : Subgroup G :=
  normalizer ((fzR t x₁ x₂ : Subgroup G) : Set G)

@[expose] def fz59B (x₁ x₂ s : G) : Subgroup G := fourGrp x₁ x₂ ⊔ zpowers s

@[expose] def fz59F (t x₁ x₂ s : G) : Subgroup G := fz59B x₁ x₂ s ⊔ zpowers t

structure Fz59Grid (t s lam rho : G) (b : Fin 3 → Fin 2 → G) : Prop where
  quat : ∀ i, IsQ8Pair (b i 0) (b i 1)
  sq_eq : b 2 0 ^ 2 = b 0 0 ^ 2 * b 1 0 ^ 2
  comm : ∀ i j, i ≠ j → ∀ k l, Commute (b i k) (b j l)
  t_eq : t = b 0 0 * b 1 0 * b 2 0
  s_eq : s = b 0 1 * b 1 1 * b 2 1
  lam_sq : lam ^ 2 = 1
  lam_01 : ∀ k, lam * b 0 k * lam⁻¹ = b 1 k
  lam_2 : ∀ k, lam * b 2 k * lam⁻¹ = b 2 k
  rho_ord : rho ^ 3 = 1
  rho_b : ∀ i k, rho * b i k * rho⁻¹ = b (i + 1) k
  lam_rho : lam * rho * lam⁻¹ = rho⁻¹

structure Fz59UGood (t s lam rho u : G) (b : Fin 3 → Fin 2 → G) : Prop where
  sq : u ^ 2 = 1
  rho_comm : u * rho = rho * u
  b1 : ∀ i, u * b i 1 * u⁻¹ = (b i 1)⁻¹
  b0 : ∀ i, u * b i 0 * u⁻¹ = b i 0 * b i 1 * b (i - 1) 0 ^ 2
  t_conj : u * t * u⁻¹ = t * s
  lam_u : lam * u * lam⁻¹ * u⁻¹ = s

structure Fz59UBad (t s lam rho u : G) (b : Fin 3 → Fin 2 → G) : Prop where
  sq : u ^ 2 = 1
  rho_comm : u * rho = rho * u
  b1 : ∀ i, u * b i 1 * u⁻¹ = (b i 1)⁻¹
  b0 : ∀ i, u * b i 0 * u⁻¹ = b i 0 * b i 1
  t_conj : u * t * u⁻¹ = t * s
  lam_u : lam * u = u * lam

structure Fz59T3Set {G : Type} [Group G] [Finite G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau s u : G) (b : Fin 3 → Fin 2 → G) (T₃ : Subgroup G) : Prop where
  assump : FzAssumptionII G
  ctx : Ctx t L S x₁ x₂ lam rho tau
  card_two : Nat.card (twoCore t) = 2
  isT2 : IsFzT2 t x₁ x₂ S T₂
  not_sylow : ¬ FzSylow T₂
  grid : Fz59Grid t s lam rho b
  s_cases : s = tau ∨ s = t * tau
  u_cases : Fz59UGood t s lam rho u b ∨ Fz59UBad t s lam rho u b
  hR : fzR t x₁ x₂ = closure (Set.range fun p : Fin 3 × Fin 2 => b p.1 p.2)
  hZ : fourGrp x₁ x₂ = closure {b 0 0 ^ 2, b 1 0 ^ 2}
  z3 : b 2 0 ^ 2 = (x₁ * x₂) ^ 2
  hW : ctxW t x₁ x₂ = closure (Set.range fun i => b i 0)
  hE : baseGrp x₁ x₂ = closure (Set.range fun i => b i 0 * t)
  hT₂ : T₂ = fzR t x₁ x₂ ⊔ zpowers lam
  hT₃ : T₃ = T₂ ⊔ zpowers u
  card_T₃ : Nat.card T₃ = 2 ^ 10
  sylow : FzSylow T₃
  card_N3 : Nat.card (fz59N3 t x₁ x₂) = 3 * 2 ^ 10

@[expose] def Fz59A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G) (a₁₂ a₂₂ a₃₂ : G), FzAssumptionII G →
    Ctx t L S x₁ x₂ lam rho tau → Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ →
    ¬ FzSylow T₂ → FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ → ¬ 2 ^ 11 ∣ Nat.card G →
    ∃ (s u : G) (b : Fin 3 → Fin 2 → G) (T₃ : Subgroup G),
      Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃

@[expose] def Fz59B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau s u : G) (b : Fin 3 → Fin 2 → G) (T₃ : Subgroup G),
    Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃ → False

@[expose] def Fz59Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G) (a₁₂ a₂₂ a₃₂ : G), FzAssumptionII G →
    Ctx t L S x₁ x₂ lam rho tau → Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ →
    ¬ FzSylow T₂ → FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ →
    2 ^ 10 ∣ Nat.card (fz59N3 t x₁ x₂)

theorem fz59_of_halves (hA : Fz59A) (hB : Fz59B) : Fz59 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hr4 hctx hK hT hns hsh hbd
  obtain ⟨s, u, b, T₃, h⟩ :=
    hA G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hr4 hctx hK hT hns hsh hbd
  exact hB G t L S T₂ x₁ x₂ lam rho tau s u b T₃ h

end CFSG.OddStandard.SmallF3.FritzII
