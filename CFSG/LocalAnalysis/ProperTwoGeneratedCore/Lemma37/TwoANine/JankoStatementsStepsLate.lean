module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatementsSteps

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] {z : G}

structure JankoProp11 (fr : JankoFrame G z) : Prop where
  card_N : Nat.card fr.N = 3 ^ 7
  N_pow_three : ∀ a ∈ fr.N, a ^ 3 = 1
  isSylowOf_N : IsSylowOf (normalizer (fr.P₁ : Set G)) 3 fr.N
  normalizer_N_inf : normalizer (fr.N : Set G) ⊓ normalizer (fr.P₁ : Set G) = fr.N ⊔ fr.L
  N_inf_centralizer_z : fr.N ⊓ centralizer ({z} : Set G) = fr.E
  N_inf_centralizer_t : fr.N ⊓ centralizer ({fr.t} : Set G) = fr.P₂ ⊔ fr.At
  card_ZN : Nat.card fr.ZN = 27
  ZN_le_M : fr.ZN ≤ fr.M
  card_P3bar : Nat.card fr.P3bar = 3
  card_P3bbar : Nat.card fr.P3bbar = 3
  ZN_eq : fr.ZN = fr.P₁ ⊔ fr.S
  commutator_N : ⁅fr.N, fr.N⁆ = fr.S
  card_I : Nat.card fr.I = 3 ^ 5
  I_comm : ∀ a ∈ fr.I, ∀ b ∈ fr.I, a * b = b * a
  N_le_normalizer_I : fr.N ≤ normalizer (fr.I : Set G)
  L_le_normalizer_I : fr.L ≤ normalizer (fr.I : Set G)
  N_inf_normalizer_E : fr.N ⊓ normalizer (fr.E : Set G) = fr.I
  normalizer_P₁_le : normalizer (fr.P₁ : Set G) ≤ normalizer (fr.Mbar : Set G)
  isConj_of_mem_Mbar : ∀ x ∈ fr.Mbar, x ≠ 1 → IsConj x fr.s₃
  exists_conj_ZN : ∀ x ∈ fr.ZN, ∀ y ∈ fr.ZN, x ∉ fr.P₁ → x ∉ fr.S → y ∉ fr.P₁ → y ∉ fr.S →
    ∃ l ∈ fr.L, l * x * l⁻¹ = y
  exists_conj_M : ∀ x ∈ fr.M, ∀ y ∈ fr.M, x ∉ fr.P₁ → x ∉ fr.Mbar → y ∉ fr.P₁ →
    y ∉ fr.Mbar → ∃ g ∈ normalizer (fr.P₁ : Set G), g * x * g⁻¹ = y
  M_inf_centralizer : ∀ x ∈ fr.N, x ∉ fr.M → fr.M ⊓ centralizer ({x} : Set G) = fr.ZN
  card_abelian : Nat.card {B : Subgroup G // B ≤ fr.N ∧ Nat.card B = 3 ^ 5 ∧
    ∀ a ∈ B, ∀ b ∈ B, a * b = b * a} = 10
  centralizer_E : centralizer (fr.E : Set G) = fr.I ⊔ zpowers z

structure JankoChoiceM (fr : JankoFrame G z) (m : G) : Prop where
  mem_K : m ∈ fr.K
  orderOf_m : orderOf m = 3
  mem_centralizer : m ∈ centralizer (fr.P3bar : Set G)
  t_mul_m : fr.t * m * fr.t⁻¹ = m⁻¹
  card_R : Nat.card (fr.R m) = 3 ^ 10
  center_R : fr.R m ⊓ centralizer (fr.R m : Set G) = fr.P3bar
  normalizer_P3bar : normalizer (fr.P3bar : Set G) = fr.R m ⊔ fr.V

structure JankoProp12 (fr : JankoFrame G z) : Prop where
  card_normalizer_N : Nat.card (normalizer (fr.N : Set G)) = 3 ^ 9 * 2 ^ 4
  card_U : Nat.card fr.U = 3 ^ 9
  N_le_U : fr.N ≤ fr.U
  U_inf_centralizer_z : fr.U ⊓ centralizer ({z} : Set G) = fr.E
  card_U_inf_t : Nat.card (fr.U ⊓ centralizer ({fr.t} : Set G) : Subgroup G) = 3 ^ 4
  card_U_inf_tz : Nat.card (fr.U ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) = 3 ^ 4
  center_U : fr.U ⊓ centralizer (fr.U : Set G) = fr.S
  U_inf_centralizer_ZN : ∀ x ∈ fr.ZN, x ∉ fr.S → fr.U ⊓ centralizer ({x} : Set G) = fr.N
  isConj_of_mem_M : ∀ x ∈ fr.M, x ∉ fr.Mbar → IsConj x fr.s₁
  card_le_of_isConj_s₃ : ∀ y : G, IsConj y fr.s₃ → ∀ B : Subgroup G,
    B ≤ normalizer (zpowers y : Set G) → IsPGroup 3 B → Nat.card B ≤ 3 ^ 10
  normalizer_M : normalizer (fr.M : Set G) = normalizer (fr.P₁ : Set G)
  U_le_normalizer_I : fr.U ≤ normalizer (fr.I : Set G)
  centralizer_I : centralizer (fr.I : Set G) = fr.I
  centralizer_U : centralizer (fr.U : Set G) = fr.S
  centralizer_S : centralizer (fr.S : Set G) = fr.U
  K_le_normalizer_U : fr.K ≤ normalizer (fr.U : Set G)
  U_inf_K : fr.U ⊓ fr.K = ⊥
  K_le_normalizer_I : fr.K ≤ normalizer (fr.I : Set G)
  K_le_normalizer_S : fr.K ≤ normalizer (fr.S : Set G)
  eq_one_of_le_centralizer : ∀ k ∈ fr.K, fr.S ≤ centralizer ({k} : Set G) → k = 1
  factorization_three : (Nat.card G).factorization 3 = 10
  exists_choiceM : ∃ m : G, JankoChoiceM fr m

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
