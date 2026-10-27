module

public import CFSG.LocalAnalysis.OddStandard.ThmCDefs

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC

structure TData {G : Type} [Group G] (S : Subgroup G) where
  Z : Subgroup G
  A : Subgroup G
  B : Subgroup G
  Z_le_A : Z ≤ A
  Z_le_B : Z ≤ B
  A_le_S : A ≤ S
  B_le_S : B ≤ S
  card_S : Nat.card S = 64
  card_Z : Nat.card Z = 4
  card_A : Nat.card A = 16
  card_B : Nat.card B = 16
  A_ne_B : A ≠ B
  mem_Z : ∀ g : G, g ∈ Z ↔ g ∈ S ∧ ∀ s ∈ S, g * s = s * g
  Z_sq : ∀ z ∈ Z, z * z = 1
  comm_mem_Z : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z
  sq_mem_Z : ∀ x ∈ S, x * x ∈ Z
  A_abel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  B_abel : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  A_sq : ∀ x ∈ A, x * x = 1
  B_sq : ∀ x ∈ B, x * x = 1
  AB_le_Z : ∀ x, x ∈ A → x ∈ B → x ∈ Z
  A_norm : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A
  B_norm : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B
  invol : ∀ x ∈ S, x * x = 1 → x ∈ A ∨ x ∈ B
  cent_A : ∀ a ∈ A, a ∉ Z → ∀ s ∈ S, s * a = a * s → s ∈ A
  cent_B : ∀ b ∈ B, b ∉ Z → ∀ s ∈ S, s * b = b * s → s ∈ B
  cent_not_A : ∀ s ∈ S, s ∉ A → ∀ a ∈ A, a * s = s * a → a ∈ Z
  cent_not_B : ∀ s ∈ S, s ∉ B → ∀ b ∈ B, b * s = s * b → b ∈ Z
  normal_dich : ∀ N : Subgroup G, N ≤ S → (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → N ≤ Z ∨ Z ≤ N
  elemAb_le : ∀ E : Subgroup G, E ≤ S → (∀ x ∈ E, x * x = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → E ≤ A ∨ E ≤ B
  extremal : ∀ z ∈ Z, z ≠ 1 → ∀ a ∈ S, a ∉ Z → ∃ s ∈ S, ∃ t ∈ S,
    s * a * s⁻¹ * a⁻¹ ∈ zpowers z ∧ t * a * t⁻¹ * a⁻¹ ∈ zpowers z ∧
      s * t * s⁻¹ * t⁻¹ ∉ zpowers z
  diag : ∀ g : G, g ∈ normalizer (S : Set G) → (∀ z ∈ Z, g * z * g⁻¹ = z) →
    (∀ a ∈ A, g * a * g⁻¹ ∈ A) → (∀ b ∈ B, g * b * g⁻¹ ∈ B) →
    (∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Z) ∨
      ((∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Z → s ∈ Z) ∧ ∀ s ∈ S, g ^ 3 * s * (g ^ 3)⁻¹ * s⁻¹ ∈ Z)

@[expose] def Gor42 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], pPrimeCore 2 Q = ⊥ →
    ∀ R : Sylow 2 Q, Nat.card (R : Subgroup Q) = 16 → (∀ r ∈ (R : Subgroup Q), r * r = 1) →
      (∀ r ∈ (R : Subgroup Q), ∀ s ∈ (R : Subgroup Q), r * s = s * r) →
      (∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
          ((∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1) ∧
            ∀ r ∈ (R : Subgroup Q), g ^ 3 * r * (g ^ 3)⁻¹ = r)) →
      (R : Subgroup Q).Normal

@[expose] def A8Fact : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (A : Type) [Group A] [Finite A],
    (∀ a b : A, a * b = b * a) → (∀ a : A, a * a = 1) → Nat.card A = 16 →
    ∀ ρ : K →* MulAut A, Function.Injective ρ →
    pCore 2 K = ⊥ →
    ∀ V : Sylow 2 K, Nat.card (V : Subgroup K) = 4 → (∀ v ∈ (V : Subgroup K), v * v = 1) →
    ∀ Z : Subgroup A, Nat.card Z = 4 →
      (∀ v ∈ (V : Subgroup K), v ≠ 1 → ∀ a : A, ρ v a = a ↔ a ∈ Z) →
      ¬ (∀ k : K, ∀ a ∈ Z, ρ k a ∈ Z) →
      (Nonempty (K ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (K ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) ∧
      ∀ u v : A, u ≠ 1 → v ≠ 1 → ∃ k : K, ρ k u = v

@[expose] def TData.swap {G : Type} [Group G] {S : Subgroup G} (td : TData S) : TData S where
  Z := td.Z
  A := td.B
  B := td.A
  Z_le_A := td.Z_le_B
  Z_le_B := td.Z_le_A
  A_le_S := td.B_le_S
  B_le_S := td.A_le_S
  card_S := td.card_S
  card_Z := td.card_Z
  card_A := td.card_B
  card_B := td.card_A
  A_ne_B := td.A_ne_B.symm
  mem_Z := td.mem_Z
  Z_sq := td.Z_sq
  comm_mem_Z := td.comm_mem_Z
  sq_mem_Z := td.sq_mem_Z
  A_abel := td.B_abel
  B_abel := td.A_abel
  A_sq := td.B_sq
  B_sq := td.A_sq
  AB_le_Z := fun x hxa hxb => td.AB_le_Z x hxb hxa
  A_norm := td.B_norm
  B_norm := td.A_norm
  invol := fun x hx h => (td.invol x hx h).symm
  cent_A := td.cent_B
  cent_B := td.cent_A
  cent_not_A := td.cent_not_B
  cent_not_B := td.cent_not_A
  normal_dich := td.normal_dich
  elemAb_le := fun E hE hsq hc => (td.elemAb_le E hE hsq hc).symm
  extremal := td.extremal
  diag := fun g hg hz ha hb => td.diag g hg hz hb ha

end CFSG.OddStandard.ThmC.O2
