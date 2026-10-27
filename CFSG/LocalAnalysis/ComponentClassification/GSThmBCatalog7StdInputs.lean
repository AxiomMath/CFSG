module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdRows

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def HeL2Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    Blueprint.NativeSporadic.IsSporadic ↥(generalizedFitting H) .He →
    ∀ b : H, orderOf b = 2 → ∀ K : Subgroup H, K ≤ centralizer ({b} : Set H) →
      IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))) →
      ¬ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 7 2

@[expose] def SuzL2Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    Blueprint.NativeSporadic.IsSporadic ↥(generalizedFitting H) .Suz →
    ∀ b : H, orderOf b = 2 → ∀ K : Subgroup H, K ≤ centralizer ({b} : Set H) →
      IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))) →
      ¬ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 5 2

@[expose] def OmegaMinus8Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    ∀ r e : ℕ, r.Prime → r ≠ 2 → 1 ≤ e →
    Blueprint.LieModel ↥(generalizedFitting H) .POmegaMinus 4 r e →
    ∀ a b : H, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
    ∀ J K : Subgroup H, J ≤ centralizer ({a} : Set H) →
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))) →
      K ≤ centralizer ({b} : Set H) → IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))) →
      (∀ M : Subgroup H, M ≤ centralizer ({b} : Set H) →
        IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set H))) → M = K) →
      b ∈ coreActionKernel J →
      ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
        Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f →
        ¬ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p (2 * f)

theorem rowOmegaMinus8 (hO : OmegaMinus8Input) : RowOmegaMinus8 := by
  intro H _ _ c r e hr hr2 he hm
  exact hO H c.simple c.centralizer_eq_bot r e hr hr2 he hm c.a c.b c.orderOf_a c.orderOf_b
    c.mul_comm_ab c.J c.K c.J_le c.isPComponent_J c.K_le c.isPComponent_K c.layer c.b_mem_kernel
    c.p c.f c.prime c.ne_two c.one_le c.five_le c.type_J c.type_K

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
