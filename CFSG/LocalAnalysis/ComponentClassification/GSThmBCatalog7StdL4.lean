module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdRows

public section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L4EpsInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup ↥(generalizedFitting H) →
    centralizer (generalizedFitting H : Set H) = ⊥ →
    ∀ r e : ℕ, r.Prime → r ≠ 2 → 1 ≤ e →
    (Blueprint.LieModel ↥(generalizedFitting H) .PSL 4 r e ∨
      Blueprint.LieModel ↥(generalizedFitting H) .PSU 4 r e) →
    ∀ a b : H, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
    ∀ J K : Subgroup H, J ≤ generalizedFitting H → K ≤ generalizedFitting H →
      J ≤ centralizer ({a} : Set H) →
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))) →
      K ≤ centralizer ({b} : Set H) → IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))) →
      (∀ M : Subgroup H, M ≤ centralizer ({b} : Set H) →
        IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set H))) → M = K) →
      (∀ T : Subgroup H, IsPGroup 2 T →
        T ≤ centralizer ({b} : Set H) ⊓ coreActionKernel K → Nat.card T ≤ 2) →
      b ∈ coreActionKernel J →
      ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → 5 ≤ p ^ f →
        Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f →
        ¬ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p (2 * f)

variable {H : Type} [Group H] [Finite H]

theorem StdConf.false_of_l4eps (h : L4EpsInput) (c : StdConf H) {r e : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hm : Blueprint.LieModel ↥(generalizedFitting H) .PSL 4 r e ∨
      Blueprint.LieModel ↥(generalizedFitting H) .PSU 4 r e) : False :=
  h H c.simple c.centralizer_eq_bot r e hr hr2 he hm c.a c.b c.orderOf_a c.orderOf_b
    c.mul_comm_ab c.J c.K c.J_le_G c.K_le_G c.J_le c.isPComponent_J c.K_le c.isPComponent_K
    c.layer c.sylow c.b_mem_kernel c.p c.f c.prime c.ne_two c.one_le c.five_le c.type_J c.type_K

theorem rowL4 (h : L4EpsInput) : RowL4 := fun _ _ _ c _ _ hp hp2 hf hm =>
  c.false_of_l4eps h hp hp2 hf (Or.inl hm)

theorem rowU4 (h : L4EpsInput) : RowU4 := fun _ _ _ c _ _ hp hp2 hf hm =>
  c.false_of_l4eps h hp hp2 hf (Or.inr hm)

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
