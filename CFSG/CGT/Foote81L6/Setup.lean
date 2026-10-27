module

public import CFSG.Open.Catalog

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

structure FooteCore (G : Type*) [Group G] (T : Subgroup G) (m n : ℕ) where
  A : Subgroup G
  B : Subgroup G
  B₀ : Subgroup G
  B₁ : Subgroup G
  t : G
  s : G
  a : G
  b₀ : G
  b₁ : G
  T_eq : T = A ⊔ B ⊔ zpowers t
  A_inf_B : A ⊓ B = ⊥
  A_comm_B : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x
  conj_t_A : ∀ x ∈ A, t * x * t⁻¹ ∈ A
  conj_t_B : ∀ x ∈ B, t * x * t⁻¹ ∈ B
  t_sq : t ^ 2 = 1
  two_le_m : 2 ≤ m
  A_iso : Nonempty (↥A ≃* DihedralGroup (2 ^ (m - 1)))
  At_iso : Nonempty (↥(A ⊔ zpowers t) ≃* DihedralGroup (2 ^ m))
  B_eq : B = B₀ ⊔ B₁ ⊔ zpowers s
  B₀_inf_B₁ : B₀ ⊓ B₁ = ⊥
  B₀_comm_B₁ : ∀ x ∈ B₀, ∀ y ∈ B₁, x * y = y * x
  m_lt_n : m < n
  B₀_iso : Nonempty (↥B₀ ≃* DihedralGroup (2 ^ (n - 1)))
  B₁_iso : Nonempty (↥B₁ ≃* DihedralGroup (2 ^ (n - 1)))
  s_sq : s ^ 2 = 1
  conj_s_B₀ : B₀.map (MulAut.conj s).toMonoidHom = B₁
  Bt_conj : ∀ x ∈ B, (x * t) ^ 2 = 1 → ∃ y ∈ B, y * (x * t) * y⁻¹ = t
  CBt_iso : Nonempty (↥(B ⊓ centralizer ({t} : Set G)) ≃* CFSG.Open.SemidihedralGroup (n + 1))
  a_mem : a ∈ A
  a_order : orderOf a = 2
  a_comm : ∀ x ∈ A ⊔ zpowers t, x * a = a * x
  b₀_mem : b₀ ∈ B₀
  b₀_order : orderOf b₀ = 2
  b₀_comm : ∀ x ∈ B₀, x * b₀ = b₀ * x
  b₁_mem : b₁ ∈ B₁
  b₁_order : orderOf b₁ = 2
  b₁_comm : ∀ x ∈ B₁, x * b₁ = b₁ * x

structure FooteData (G : Type*) [Group G] (T : Subgroup G) (m n : ℕ) extends
    FooteCore G T m n where
  fusion_i : ∀ x ∈ A, orderOf x = 2 → x ≠ a → ∀ r ∈ B₀, orderOf r = 2 → ¬ IsConj a (x * r)
  fusion_ii : ∀ r ∈ B₀, orderOf r = 2 → ¬ IsConj a (r * b₁)
  fusion_iii : ∀ x ∈ A, orderOf x = 2 → x ≠ a → ∀ y ∈ A, orderOf y = 2 → y ≠ a →
    ∀ r ∈ B₀, orderOf r = 2 → ¬ IsConj (x * r) y
  fusion_iv : ∀ x ∈ A, orderOf x = 2 → x ≠ a → ∀ r ∈ B₀, orderOf r = 2 →
    ¬ IsConj (x * r * b₁) (x * b₀)
  fusion_v : ∀ r ∈ B₀, orderOf r = 2 → ¬ IsConj a (r * (t * r * t⁻¹))

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

@[expose] def b : G := D.b₀ * D.b₁

@[expose] def T₀ : Subgroup G := D.A ⊔ D.B

@[expose] def T₁ : Subgroup G := D.A ⊔ (D.B₀ ⊔ D.B₁)

@[expose] def Astar : Subgroup G :=
  closure {g | ∃ x ∈ D.A, orderOf x = 2 ∧ x ≠ D.a ∧ g = x * D.b}

end FooteCore

@[expose] def StronglyInvolutionClosed {G : Type*} [Group G] (K H : Subgroup G) : Prop :=
  ∀ k ∈ K, orderOf k = 2 → ∀ g : G, g * k * g⁻¹ ∈ H → g * k * g⁻¹ ∈ K

@[expose] def FooteTheorem1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (D : FooteData G T m n),
    StronglyInvolutionClosed D.A T ∨ StronglyInvolutionClosed D.Astar T

section Quotient

variable {H : Type*} [Group H]

@[expose] def zCent (z : H) : centralizer ({z} : Set H) :=
  ⟨z, mem_centralizer_singleton_iff.2 rfl⟩

instance zpowers_zCent_normal (z : H) : (zpowers (zCent z)).Normal :=
  normal_of_le_center <| zpowers_le.2 <| mem_center_iff.2 fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)

abbrev centralizerQuot (z : H) : Type _ :=
  centralizer ({z} : Set H) ⧸ zpowers (zCent z)

@[expose] def sylowQuot (S : Subgroup H) (z : H) : Subgroup (centralizerQuot z) :=
  (S.subgroupOf (centralizer ({z} : Set H))).map (QuotientGroup.mk' (zpowers (zCent z)))

@[expose] def LiftsSquareToZ (S : Subgroup H) (z : H) {m n : ℕ}
    (D : FooteCore (centralizerQuot z) (sylowQuot S z) m n) : Prop :=
  ∀ g : centralizer ({z} : Set H), (g : H) ∈ S →
    ((QuotientGroup.mk g : centralizerQuot z) ∈ D.A ∨
      (QuotientGroup.mk g : centralizerQuot z) ∈ D.Astar) →
    orderOf (QuotientGroup.mk g : centralizerQuot z) = 2 → (g : H) ^ 2 = z

end Quotient

end CFSG.CGT.Foote81L6
