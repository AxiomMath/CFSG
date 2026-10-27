module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Stmt

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G]

abbrev Fz59Cell : Type := Fin 3 × Fin 3

@[expose] def fz59R (b : Fin 3 → Fin 2 → G) : Subgroup G :=
  closure (Set.range fun p : Fin 3 × Fin 2 => b p.1 p.2)

@[expose] def fz59Z (b : Fin 3 → Fin 2 → G) : Subgroup G := closure {b 0 0 ^ 2, b 1 0 ^ 2}

@[expose] def fz59CellElt (b : Fin 3 → Fin 2 → G) (c : Fz59Cell) : G :=
  ![b c.1 0, b c.1 1, b c.1 0 * b c.1 1] c.2

@[expose] def fz59Prod (b : Fin 3 → Fin 2 → G) (ω : Fin 3 → Fin 3) : G :=
  fz59CellElt b (0, ω 0) * fz59CellElt b (1, ω 1) * fz59CellElt b (2, ω 2)

@[expose] def fz59Tr (ω : Fin 3 → Fin 3) : Finset Fz59Cell :=
  Finset.univ.image fun i => (i, ω i)

@[expose] def fz59RowRot : Equiv.Perm Fz59Cell :=
  Equiv.prodCongr (Equiv.addRight (1 : Fin 3)) (Equiv.refl _)

@[expose] def fz59RowSwap : Equiv.Perm Fz59Cell :=
  Equiv.prodCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.refl _)

@[expose] def fz59ColPerm (σ : Equiv.Perm (Fin 3)) : Equiv.Perm Fz59Cell :=
  Equiv.prodCongr (Equiv.refl _) σ

@[expose] def fz59FusPairs : List ((Fin 3 → Fin 3) × (Fin 3 → Fin 3)) :=
  [(![1, 1, 1], ![1, 2, 2]), (![1, 1, 1], ![2, 1, 2]), (![1, 1, 1], ![2, 2, 1]),
   (![2, 2, 2], ![2, 1, 1]), (![2, 2, 2], ![1, 2, 1]), (![2, 2, 2], ![1, 1, 2])]

abbrev Fz59Q8 : Type := QuaternionGroup 2

abbrev Fz59Mod : Type := Fz59Q8 × Fz59Q8 × Fz59Q8

@[expose] def fz59Gen : Fin 3 → Fin 2 → Fz59Mod :=
  ![![(QuaternionGroup.a 1, 1, 1), (QuaternionGroup.xa 0, 1, 1)],
    ![(1, QuaternionGroup.a 1, 1), (1, QuaternionGroup.xa 0, 1)],
    ![(1, 1, QuaternionGroup.a 1), (1, 1, QuaternionGroup.xa 0)]]

@[expose] def fz59Zeta : Fz59Mod :=
  (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2)

structure Fz59Rows (b : Fin 3 → Fin 2 → G) : Prop where
  quat : ∀ i, IsQ8Pair (b i 0) (b i 1)
  sq_eq : b 2 0 ^ 2 = b 0 0 ^ 2 * b 1 0 ^ 2
  comm : ∀ i j, i ≠ j → ∀ k l, Commute (b i k) (b j l)

theorem Fz59Grid.rows {t s lam rho : G} {b : Fin 3 → Fin 2 → G} (h : Fz59Grid t s lam rho b) :
    Fz59Rows b :=
  ⟨h.quat, h.sq_eq, h.comm⟩

@[expose] def Fz59CellAction (b : Fin 3 → Fin 2 → G)
    (Φ : normalizer ((fz59R b : Subgroup G) : Set G) →* Equiv.Perm Fz59Cell) : Prop :=
  (∀ (n : normalizer ((fz59R b : Subgroup G) : Set G)) (c : Fz59Cell), ∃ z ∈ fz59Z b,
      (n : G) * fz59CellElt b c * (n : G)⁻¹ = fz59CellElt b (Φ n c) * z) ∧
    ∀ (n : normalizer ((fz59R b : Subgroup G) : Set G)) (i k k' : Fin 3),
      (Φ n (i, k)).1 = (Φ n (i, k')).1

structure Fz59Frame (t tau lam rho x₁ x₂ s : G) (b : Fin 3 → Fin 2 → G) : Prop where
  grid : Fz59Grid t s lam rho b
  s_cases : s = tau ∨ s = t * tau
  hR : fzR t x₁ x₂ = fz59R b
  hZ : fourGrp x₁ x₂ = fz59Z b
  z3 : b 2 0 ^ 2 = (x₁ * x₂) ^ 2
  hW : ctxW t x₁ x₂ = closure (Set.range fun i => b i 0)
  hE : baseGrp x₁ x₂ = closure (Set.range fun i => b i 0 * t)

structure Fz59Out {G : Type} [Group G] [Finite G] (t : G) (T₂ : Subgroup G)
    (x₁ x₂ lam rho tau s u : G) (b : Fin 3 → Fin 2 → G) (T₃ : Subgroup G) : Prop where
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

theorem Fz59Out.toT3Set {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
    {x₁ x₂ lam rho tau s u : G} {b : Fin 3 → Fin 2 → G} {T₃ : Subgroup G}
    (h : Fz59Out t T₂ x₁ x₂ lam rho tau s u b T₃) (hr4 : FzAssumptionII G)
    (hctx : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    (hT : IsFzT2 t x₁ x₂ S T₂) (hns : ¬ FzSylow T₂) :
    Fz59T3Set t L S T₂ x₁ x₂ lam rho tau s u b T₃ :=
  ⟨hr4, hctx, hK, hT, hns, h.grid, h.s_cases, h.u_cases, h.hR, h.hZ, h.z3, h.hW, h.hE, h.hT₂,
    h.hT₃, h.card_T₃, h.sylow, h.card_N3⟩

structure Fz59Base {G : Type} [Group G] [Finite G] (t tau lam rho x₁ x₂ a₁₂ a₂₂ a₃₂ : G)
    (T₂ : Subgroup G) : Prop where
  str : FzStr t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂)
    (fzQ t x₁ x₂ rho) (fzR t x₁ x₂) T₂
  shape : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂
  T2_le : T₂ ≤ fzN2 t x₁ x₂
  T2_p : IsPGroup 2 T₂
  rho_N2 : rho ∈ fzN2 t x₁ x₂
  N2_nrm_R : ∀ n ∈ fzN2 t x₁ x₂, ∀ r ∈ fzR t x₁ x₂, n * r * n⁻¹ ∈ fzR t x₁ x₂
  cz : ∀ n ∈ fzN2 t x₁ x₂, (∀ z ∈ fourGrp x₁ x₂, n * z * n⁻¹ = z) → n ∈ fzR t x₁ x₂
  cent2 : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({t} : Set G) → Nat.card P ≤ 2 ^ 7
  fus : tau ^ 2 = 1 → ∀ e ∈ baseGrp x₁ x₂,
    IsConj tau (e * tau) ∧ IsConj (t * tau) (e * (t * tau))
  bound : ¬ 2 ^ 11 ∣ Nat.card G
  even : 2 ^ 10 ∣ Nat.card (fz59N3 t x₁ x₂)

end CFSG.OddStandard.SmallF3.FritzII
