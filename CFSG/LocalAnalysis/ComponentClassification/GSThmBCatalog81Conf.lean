module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4q

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Cat8

variable (K₀ : Type) [Group K₀]

abbrev innA (α : MulAut K₀) : Subgroup (MulAut K₀) := Inn K₀ ⊔ zpowers α

structure QConf (q : ℕ) where
  a : MulAut K₀
  Q : Subgroup (MulAut K₀)
  g : MulAut K₀
  z : MulAut K₀
  adm : IsAdmQ K₀ q a
  Q_le : Q ≤ innA K₀ a ⊓ centralizer ({a} : Set (MulAut K₀))
  Q_sylow : ∃ T : Sylow 2 ↥(innA K₀ a ⊓ centralizer ({a} : Set (MulAut K₀))),
    (T : Subgroup _) = Q.subgroupOf (innA K₀ a ⊓ centralizer ({a} : Set (MulAut K₀)))
  g_inn : g ∈ Inn K₀
  g_norm : g ∈ normalizer (Q : Set (MulAut K₀))
  g_not_mem : g ∉ Q
  g_sq : g * g ∈ Q
  tau_inn : a * (g⁻¹ * a * g) ∈ Inn K₀
  z_mem : z ∈ Q ⊓ L0 K₀ a
  z_comm : ∀ w ∈ Q ⊓ L0 K₀ a, z * w = w * z
  z_sq : z * z = 1
  z_ne : z ≠ 1

namespace QConf

variable {K₀} {q : ℕ}

abbrev tau (c : QConf K₀ q) : MulAut K₀ := c.a * (c.g⁻¹ * c.a * c.g)

abbrev D (c : QConf K₀ q) : Subgroup (MulAut K₀) := c.Q ⊓ L0 K₀ c.a

structure Props (c : QConf K₀ q) : Prop where
  Q_eq : c.Q = c.D ⊔ zpowers c.tau ⊔ zpowers c.a
  card_Q : Nat.card c.Q = 4 * Nat.card c.D
  eight_le : 8 ≤ Nat.card c.D
  tau_comm : ∀ w ∈ c.Q, c.tau * w = w * c.tau
  g_z : c.g⁻¹ * c.z * c.g = c.z
  z_tau : ∃ k ∈ Inn K₀, k⁻¹ * c.z * k = c.tau

end QConf

end Cat8

@[expose] def CF81Conf : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ c : Cat8.QConf K₀ (p ^ f), c.Props

@[expose] def CF81L0 : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    IsSec8Socle K₀ p f → ∀ α : MulAut K₀, Cat8.IsAdmQ K₀ (p ^ f) α →
      Nat.card (Cat8.L0 K₀ α) = Cat8.ordL2 ((p ^ f) ^ 2)

end CFSG.ComponentClassification.GSThmB
