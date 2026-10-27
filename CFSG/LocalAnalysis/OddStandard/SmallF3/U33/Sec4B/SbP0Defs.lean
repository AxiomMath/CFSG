module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx8 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx10 t L S x₁ x₂ lam rho tau where
  tM : conjIn (ctxM t tau x₁ x₂) t =
    t • (fourGrp x₁ x₂ : Set G) ∪ (t * tau) • (fourGrp x₁ x₂ : Set G)

structure Ctx8a (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx8 t L S x₁ x₂ lam rho tau where
  card_M : Nat.card (ctxM t tau x₁ x₂) = 3 * 2 ^ 10
  normal_N : NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂)
  normal_V : NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂)

structure Ctx8b (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx8a t L S x₁ x₂ lam rho tau where
  O_eq_C : ctxO t tau x₁ x₂ =
    ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  card_O : Nat.card (ctxO t tau x₁ x₂) = 2 ^ 9
  lam_not_mem_O : lam ∉ ctxO t tau x₁ x₂

structure Ctx8c (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx8b t L S x₁ x₂ lam rho tau where
  M_eq : ctxM t tau x₁ x₂ = ctxO t tau x₁ x₂ ⊔ closure {rho, lam}
  S_le_U : S ≤ ctxU t tau x₁ x₂ lam
  U_sylow : IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (ctxM t tau x₁ x₂)

structure Ctx8d (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx8c t L S x₁ x₂ lam rho tau where
  X_le_R : ctxX t tau x₁ x₂ ≤ ctxR t tau x₁ x₂
  R_le_O : ctxR t tau x₁ x₂ ≤ ctxO t tau x₁ x₂
  card_R : Nat.card (ctxR t tau x₁ x₂) = 2 ^ 8
  normal_R : NormalIn (ctxR t tau x₁ x₂) (ctxM t tau x₁ x₂)
  R_quot : (∀ a ∈ ctxR t tau x₁ x₂, a ^ 2 ∈ ctxX t tau x₁ x₂) ∧
    ∀ a ∈ ctxR t tau x₁ x₂, ∀ b ∈ ctxR t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ ctxX t tau x₁ x₂
  coset : ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a ∉ ctxR t tau x₁ x₂ →
    b ∉ ctxR t tau x₁ x₂ → a⁻¹ * b ∈ ctxR t tau x₁ x₂

structure Ctx8e (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx8d t L S x₁ x₂ lam rho tau where
  CR_rho : ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = closure {t, tau}
  tR : conjIn (ctxR t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G)
  ttauR : conjIn (ctxR t tau x₁ x₂) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G)
  tauR : conjIn (ctxR t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G)
  tM_O : conjIn (ctxO t tau x₁ x₂) t = conjIn (ctxM t tau x₁ x₂) t
  tauM : conjIn (ctxM t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G)
  tauO : conjIn (ctxO t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G)

end CFSG.OddStandard.SmallF3.HarrisU33

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem p0_O_le_M (t tau x₁ x₂ : G) : ctxO t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 (ctxM t tau x₁ x₂)

theorem p0_normal_O (t tau x₁ x₂ : G) : NormalIn (ctxO t tau x₁ x₂) (ctxM t tau x₁ x₂) :=
  ⟨p0_O_le_M t tau x₁ x₂, fun _ hg _ hk =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (ctxM t tau x₁ x₂) hg) _).mp hk⟩

theorem p0_isPGroup_O (t tau x₁ x₂ : G) : IsPGroup 2 (ctxO t tau x₁ x₂) :=
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (ctxM t tau x₁ x₂)

theorem p0_le_O_of_normal (t tau x₁ x₂ : G) {N : Subgroup G}
    (hN : NormalIn N (ctxM t tau x₁ x₂)) (h2 : IsPGroup 2 N) : N ≤ ctxO t tau x₁ x₂ := by
  have hnorm : ctxM t tau x₁ x₂ ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hN.2 g hg n hn
    · intro hn
      have h := hN.2 g⁻¹ (inv_mem hg) (g * n * g⁻¹) hn
      have heq : g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n := by group
      rwa [heq] at h
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN.1 hnorm h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
