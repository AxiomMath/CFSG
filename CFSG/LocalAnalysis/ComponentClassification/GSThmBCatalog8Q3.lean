module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Local
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Cat8

variable (K₀ : Type) [Group K₀]

abbrev Inn : Subgroup (MulAut K₀) := (MulAut.conj : K₀ →* MulAut K₀).range

abbrev innFix (α : MulAut K₀) : Subgroup (MulAut K₀) :=
  Inn K₀ ⊓ centralizer ({α} : Set (MulAut K₀))

abbrev L0 (α : MulAut K₀) : Subgroup (MulAut K₀) := ⁅innFix K₀ α, innFix K₀ α⁆

@[expose] def IsElemAb2 {G : Type*} [Group G] (A : Subgroup G) : Prop := ∀ x ∈ A, x * x = 1

@[expose] def conjOrbit {G : Type*} [Group G] (N : Subgroup G) (w : G) : Set G :=
  {y | ∃ n ∈ N, n⁻¹ * w * n = y}

structure IsAdm (α : MulAut K₀) : Prop where
  sq : α * α = 1
  out : α ∉ Inn K₀
  dvd : 360 ∣ Nat.card (Eight.fixSubgroup α)

structure Q3Conf where
  a : MulAut K₀
  Q : Subgroup (MulAut K₀)
  g : MulAut K₀
  R : Subgroup (MulAut K₀)
  z : MulAut K₀
  adm : IsAdm K₀ a
  Q_le : Q ≤ centralizer ({a} : Set (MulAut K₀))
  Q_sylow : ∃ T : Sylow 2 ↥(centralizer ({a} : Set (MulAut K₀))),
    (T : Subgroup _) = Q.subgroupOf (centralizer ({a} : Set (MulAut K₀)))
  g_inn : g ∈ Inn K₀
  g_norm : g ∈ normalizer (Q : Set (MulAut K₀))
  g_not_mem : g ∉ Q
  g_sq : g * g ∈ Q
  tau_inn : a * (g⁻¹ * a * g) ∈ Inn K₀
  Q_le_R : Q ≤ R
  g_mem_R : g ∈ R
  R_sylow : ∃ T : Sylow 2 (MulAut K₀), (T : Subgroup _) = R
  z_mem : z ∈ Q ⊓ L0 K₀ a
  z_comm : ∀ w ∈ Q ⊓ L0 K₀ a, z * w = w * z
  z_sq : z * z = 1
  z_ne : z ≠ 1

namespace Q3Conf

variable {K₀}

abbrev tau (c : Q3Conf K₀) : MulAut K₀ := c.a * (c.g⁻¹ * c.a * c.g)

abbrev D (c : Q3Conf K₀) : Subgroup (MulAut K₀) := c.Q ⊓ L0 K₀ c.a

abbrev R0 (c : Q3Conf K₀) : Subgroup (MulAut K₀) := c.R ⊓ centralizer ({c.z} : Set (MulAut K₀))

structure Props (c : Q3Conf K₀) : Prop where
  card_D : Nat.card c.D = 8 ∧ Nat.card c.Q = 32 ∧ Nat.card c.R = 128
  Q_eq : c.Q = c.D ⊔ zpowers c.tau ⊔ zpowers c.a
  tau_comm : ∀ w ∈ c.Q, c.tau * w = w * c.tau
  card_fix_tau : Nat.card ↥(L0 K₀ c.a ⊓ centralizer ({c.tau} : Set (MulAut K₀))) = 24
  g_z : c.g⁻¹ * c.z * c.g = c.z
  tz_central : ∃ T : Sylow 2 (MulAut K₀),
    (T : Subgroup _) ≤ centralizer ({c.tau * c.z} : Set (MulAut K₀))
  tz_comm : ∀ T : Sylow 2 (MulAut K₀),
    (T : Subgroup _) ≤ centralizer ({c.tau * c.z} : Set (MulAut K₀)) →
      c.tau * c.z ∈ ⁅(T : Subgroup (MulAut K₀)), (T : Subgroup (MulAut K₀))⁆
  z_tau : ∃ k ∈ Inn K₀, k⁻¹ * c.z * k = c.tau
  R0_sylow : Nat.card c.R0 = 64 ∧ ∃ T : Sylow 2 ↥(centralizer ({c.z} : Set (MulAut K₀))),
    (T : Subgroup _) = c.R0.subgroupOf (centralizer ({c.z} : Set (MulAut K₀)))
  R0_decomp : ∃ D₁ D₂ : Subgroup (MulAut K₀), D₁ ⊔ D₂ = c.R0 ∧ D₁ ⊓ D₂ = ⊥ ∧
    D₁ ≤ centralizer (D₂ : Set (MulAut K₀)) ∧ Nonempty (D₁ ≃* DihedralGroup 4) ∧
    Nonempty (D₂ ≃* DihedralGroup 4) ∧ center D₁ = (zpowers c.z).subgroupOf D₁ ∧
    center D₂ = (zpowers c.tau).subgroupOf D₂
  R0_center : (center c.R0).map c.R0.subtype = zpowers c.z ⊔ zpowers c.tau ∧
    closure {y | ∃ x ∈ c.R0, y = x * x} = zpowers c.z ⊔ zpowers c.tau
  R0_gen : closure {y | ∃ A : Subgroup (MulAut K₀), A ≤ c.R0 ∧ IsElemAb2 A ∧
    Nat.card A = 16 ∧ y ∈ A} = c.R0
  E0 : ∃ E₀ : Subgroup (MulAut K₀), E₀ ≤ c.R ⊓ Inn K₀ ∧ IsElemAb2 E₀ ∧ Nat.card E₀ = 16 ∧
    (∀ E' : Subgroup (MulAut K₀), E' ≤ c.R ⊓ Inn K₀ → IsElemAb2 E' → Nat.card E' = 16 →
      E' = E₀) ∧ c.z ∈ E₀ ∧ c.tau ∈ E₀ ∧ centralizer (E₀ : Set (MulAut K₀)) = E₀ ∧
    (∀ w ∈ E₀, w = 1 ∨ w ∈ conjOrbit (normalizer (E₀ : Set (MulAut K₀))) c.z ∨
      w ∈ conjOrbit (normalizer (E₀ : Set (MulAut K₀))) (c.z * c.tau)) ∧
    ((Nat.card (normalizer (E₀ : Set (MulAut K₀))) = 1920 ∧
        Nat.card (conjOrbit (normalizer (E₀ : Set (MulAut K₀))) c.z) = 10 ∧
        Nat.card (conjOrbit (normalizer (E₀ : Set (MulAut K₀))) (c.z * c.tau)) = 5 ∧
        closure (conjOrbit (normalizer (E₀ : Set (MulAut K₀))) (c.z * c.tau)) = E₀) ∨
      (Nat.card (normalizer (E₀ : Set (MulAut K₀))) = 1152 ∧
        Nat.card (conjOrbit (normalizer (E₀ : Set (MulAut K₀))) c.z) = 6 ∧
        Nat.card (conjOrbit (normalizer (E₀ : Set (MulAut K₀))) (c.z * c.tau)) = 9 ∧
        closure {y | ∃ u ∈ conjOrbit (normalizer (E₀ : Set (MulAut K₀))) c.z,
          ∃ v ∈ conjOrbit (normalizer (E₀ : Set (MulAut K₀))) c.z, y = u * v} = E₀)) ∧
    (∀ A : Subgroup (MulAut K₀), A ≤ c.R → IsElemAb2 A → Nat.card A = 16 →
      (A.subgroupOf c.R).Normal → A = E₀ ∨ ∃ w ∈ A, ∃ y : MulAut K₀, y⁻¹ * c.a * y = w) ∧
    Nat.card ↥(⁅E₀, zpowers c.a⁆ : Subgroup (MulAut K₀)) = 2 ∧
    ∃ e ∈ c.R ⊓ Inn K₀, e ∈ ⁅normalizer (E₀ : Set (MulAut K₀)),
      normalizer (E₀ : Set (MulAut K₀))⁆ ∧
      e * e = 1 ∧ e ∉ centralizer (E₀ : Set (MulAut K₀))
  Z_R : (center c.R).map c.R.subtype = zpowers (c.tau * c.z)
  no_E32 : ∀ A : Subgroup (MulAut K₀), A ≤ c.R → IsElemAb2 A → Nat.card A ≠ 32
  outer_classes : ∀ y : MulAut K₀, y * y = 1 → y ∉ Inn K₀ →
    (∃ k : MulAut K₀, k⁻¹ * c.a * k = y) ∨ ∃ k : MulAut K₀, k⁻¹ * (c.a * c.z * c.tau) * k = y
  inner_classes : ∀ y ∈ Inn K₀, y * y = 1 → y ≠ 1 →
    (∃ k ∈ Inn K₀, k⁻¹ * c.z * k = y) ∨ ∃ k ∈ Inn K₀, k⁻¹ * (c.z * c.tau) * k = y

end Q3Conf

end Cat8

@[expose] def CFQ3Out : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀], IsSec8Socle K₀ 3 1 → ∀ α : MulAut K₀,
    Cat8.IsAdm K₀ α → Cat8.Inn K₀ ⊔ zpowers α = ⊤

@[expose] def CFQ3L0 : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀], IsSec8Socle K₀ 3 1 → ∀ α : MulAut K₀,
    Cat8.IsAdm K₀ α → Nat.card (Cat8.L0 K₀ α) = 360 ∧
      ∀ N : Subgroup (MulAut K₀), N ≤ Cat8.L0 K₀ α → (N.subgroupOf (Cat8.L0 K₀ α)).Normal →
        Odd (Nat.card N) → N = ⊥

@[expose] def CFQ3F2 : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀], IsSec8Socle K₀ 3 1 → ∀ α : MulAut K₀,
    Cat8.IsAdm K₀ α → ∀ Q : Subgroup (MulAut K₀), Q ≤ centralizer ({α} : Set (MulAut K₀)) →
      (∃ T : Sylow 2 ↥(centralizer ({α} : Set (MulAut K₀))),
        (T : Subgroup _) = Q.subgroupOf (centralizer ({α} : Set (MulAut K₀)))) →
      ∃ g : MulAut K₀, g ∈ Cat8.Inn K₀ ∧ g ∈ normalizer (Q : Set (MulAut K₀)) ∧ g ∉ Q ∧
        g * g ∈ Q ∧ α * (g⁻¹ * α * g) ∈ Cat8.Inn K₀

@[expose] def CFQ3Conf : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀], IsSec8Socle K₀ 3 1 → ∀ c : Cat8.Q3Conf K₀, c.Props

@[expose] def CFQ3NoNilp : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀], IsSec8Socle K₀ 3 1 → ∀ α : MulAut K₀, α * α = 1 →
    ¬ ∃ N : Subgroup K₀, N ≤ Eight.fixSubgroup α ∧
      (N.subgroupOf (Eight.fixSubgroup α)).Normal ∧ Odd (Nat.card N) ∧
      ∀ y ∈ Eight.fixSubgroup α, ∃ k : ℕ, y ^ 2 ^ k ∈ N

end CFSG.ComponentClassification.GSThmB
