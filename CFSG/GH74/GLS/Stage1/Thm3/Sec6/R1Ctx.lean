module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Basic
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

variable {G : Type} [Group G]

@[expose] def HasE8 (S : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ S ∧ (∀ a ∈ E, a * a = 1) ∧ 8 ≤ Nat.card E

@[expose] def Four (U : Subgroup G) : Prop := (∀ a ∈ U, a * a = 1) ∧ Nat.card U = 4

@[expose] def Is47b (S P F : Subgroup G) (y : G) : Prop :=
  y ∈ S ∧ y * y = 1 ∧ y ∉ P ⊔ F ∧ S = P ⊔ F ⊔ zpowers y

structure Cfg1 (G : Type) [Group G] [Finite G] (z : G) (S P Q F : Subgroup G) (FA : G → Prop) :
    Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  S_syl : Syl2In S ⊤
  z_mem : z ∈ S
  z_cent : ∀ s ∈ S, z * s = s * z
  Z_cyc : IsCyclic ↥(Subgroup.center ↥S)
  Z_inv : ∀ x ∈ S, (∀ s ∈ S, x * s = s * x) → x * x = 1 → x = 1 ∨ x = z
  simp : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  P_le : P ≤ S
  P_norm : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P
  Q_le : Q ≤ S
  Q_norm : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q
  PQ_comm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p
  PQ_inf : ∀ x ∈ P, x ∈ Q → x = 1 ∨ x = z
  z_P : z ∈ P
  z_Q : z ∈ Q
  P_inv : ∀ p ∈ P, p * p = 1 → p = 1 ∨ p = z
  P_centr : ∀ u ∈ P, u * u = z → (∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z) →
    ∃ V : Subgroup G, V = P ⊓ centralizer ({u} : Set G) ∧ IsCyclic ↥V ∧ V.relIndex P = 2
  P_exp : ∀ p ∈ P, p ^ (Nat.card ↥P / 2) = 1
  F_le : F ≤ S
  Q_eq : Q = F ⊓ (P ⊔ Q)
  idx : (P ⊔ F).relIndex S ≤ 2
  inv_fa : ∀ s ∈ S, s * s = 1 → FA s → s ∈ P ⊔ F
  rank3 : HasE8 S

structure Cfg1K (G : Type) [Group G] [Finite G] (z : G) (S P Q F : Subgroup G) (FA : G → Prop) :
    Prop extends Cfg1 G z S P Q F FA where
  diag : ∀ s ∈ S, ∀ y ∈ S, s * s = 1 → y * y = 1 → s ∉ P ⊔ Q → y ∉ P ⊔ Q → ¬ FA s → ¬ FA y →
    s * y⁻¹ ∈ P ⊔ Q
  sd : ∀ y ∈ S, y * y = 1 → y ∉ P ⊔ Q → ¬ FA y → ∃ n, IVK.IsSemidihedralTwoGroup ↥(P ⊔ zpowers y) n
  sdf : ∀ y : G, y * y = 1 → y ∉ P → (∀ p ∈ P, y * p * y⁻¹ ∈ P) →
    (∃ n, IVK.IsSemidihedralTwoGroup ↥(P ⊔ zpowers y) n) →
      (∀ p ∈ P, y * p = p * y → p = 1 ∨ p = z) ∧
      (∀ v ∈ P, (v * y) * (v * y) = 1 → ∃ p ∈ P, p⁻¹ * y * p = v * y) ∧
      (∀ v ∈ P, (v * y) * (v * y) ≠ z)
  rn4 : Q ≠ zpowers z → ∃ U : Subgroup G, U ≤ P ⊔ Q ∧ Four U ∧ ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U
  cent_rank : ∀ U : Subgroup G, U ≤ S → Four U → (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) →
    ∃ E : Subgroup G, E ≤ S ∧ (∀ a ∈ E, a * a = 1) ∧ 8 ≤ Nat.card E ∧
      ∀ e ∈ E, ∀ v ∈ U, e * v = v * e

namespace Cfg1

variable {z : G} {S P Q F : Subgroup G} {FA : G → Prop} [Finite G]

theorem Q_le_F (h : Cfg1 G z S P Q F FA) : Q ≤ F := by
  rw [h.Q_eq]; exact inf_le_left

theorem R_le_PF (h : Cfg1 G z S P Q F FA) : P ⊔ Q ≤ P ⊔ F :=
  sup_le le_sup_left (h.Q_le_F.trans le_sup_right)

theorem PF_le (h : Cfg1 G z S P Q F FA) : P ⊔ F ≤ S := sup_le h.P_le h.F_le

theorem F_norm_P (h : Cfg1 G z S P Q F FA) : F ≤ normalizer (P : Set G) := by
  intro f hf
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := h.P_norm f (h.F_le hf) x hx
    simpa using this
  · intro hx
    have h1 := h.P_norm f⁻¹ (S.inv_mem (h.F_le hf)) _ hx
    simpa [mul_assoc] using h1

theorem mem_PF (h : Cfg1 G z S P Q F FA) {n : G} (hn : n ∈ P ⊔ F) : ∃ p ∈ P, ∃ f ∈ F, n = p * f := by
  rw [sup_comm] at hn
  obtain ⟨f, hf, p, hp, rfl⟩ := mem_sup_of_le_normalizer h.F_norm_P hn
  refine ⟨f * p * f⁻¹, ?_, f, hf, by group⟩
  exact (mem_normalizer_iff.mp (h.F_norm_P hf) p).1 hp |> fun h' => by simpa using h'

theorem P_rk (h : Cfg1 G z S P Q F FA) :
    ∀ a ∈ P, ∀ b ∈ P, a * a = 1 → b * b = 1 → a * b = b * a → a = 1 ∨ b = 1 ∨ a = b := by
  intro a ha b hb ha2 hb2 _
  rcases h.P_inv a ha ha2 with h1 | h1
  · exact Or.inl h1
  rcases h.P_inv b hb hb2 with h2 | h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (h1.trans h2.symm))

theorem card_PF_le (h : Cfg1 G z S P Q F FA) (hF : IsCyclic ↥F) {E : Subgroup G} (hE : E ≤ P ⊔ F)
    (hEx : ∀ a ∈ E, a * a = 1) : Nat.card E ≤ 4 := by
  refine B.card_le_four_of_cyclic_quot (N := P ⊔ F) (P := P) (F := F) le_sup_right ?_ ?_ hF h.P_rk hE hEx
  · intro n hn p hp
    exact h.P_norm n (h.PF_le hn) p hp
  · intro n hn
    exact h.mem_PF hn

end Cfg1

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
