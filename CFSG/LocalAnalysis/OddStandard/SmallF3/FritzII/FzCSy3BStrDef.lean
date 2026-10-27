module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3E0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGenRank

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

structure FzCSy3bStr (x₁ x₂ t a b c : G) (Wp F P M₂ M₃ U : Subgroup G) : Prop where
  comm : x₁ * x₂ = x₂ * x₁
  ord₁ : orderOf x₁ = 4
  ord₂ : orderOf x₂ = 4
  inf : zpowers x₁ ⊓ zpowers x₂ = ⊥
  t_sq : t ^ 2 = 1
  t_notin : t ∉ baseGrp x₁ x₂
  t_comm₁ : t * x₁ = x₁ * t
  t_comm₂ : t * x₂ = x₂ * t
  Wp_eq : Wp = baseGrp x₁ x₂ ⊔ zpowers t
  F_eq : F = Wp ⊔ zpowers a
  P_eq : P = F ⊔ zpowers b
  M₂_eq : M₂ = F ⊔ zpowers c
  M₃_eq : M₃ = F ⊔ zpowers (b * c)
  U_eq : U = P ⊔ zpowers c
  nrm_E : ∀ u ∈ U, ∀ e ∈ baseGrp x₁ x₂, u * e * u⁻¹ ∈ baseGrp x₁ x₂
  conj_t : ∀ u ∈ U, u * t * u⁻¹ * t ∈ baseGrp x₁ x₂
  P_E : ∀ p ∈ P, ∀ e ∈ baseGrp x₁ x₂, p * e * p⁻¹ * e⁻¹ ∈ fourGrp x₁ x₂
  P_t : ∀ p ∈ P, p * t * p⁻¹ * t ∈ fourGrp x₁ x₂
  b_sq : b ^ 2 * t ∈ baseGrp x₁ x₂
  ab_sq : (a * b) ^ 2 * t ∈ baseGrp x₁ x₂
  c_sq : c ^ 2 = t
  ac_sq : (a * c) ^ 2 * t ∈ baseGrp x₁ x₂
  b_a : b * a * b⁻¹ * a⁻¹ ∈ Wp
  c_a : c * a * c⁻¹ * a⁻¹ ∈ Wp
  c_b : c * b * c⁻¹ * (a * b)⁻¹ ∈ Wp
  a_notin : a ∉ Wp
  b_notin : b ∉ F
  c_notin : c ∉ P
  sp_ab : a ^ 2 * (b ^ 2)⁻¹ ∉ fourGrp x₁ x₂
  sp_a : a ^ 2 * ((a * b) ^ 2)⁻¹ ∉ fourGrp x₁ x₂
  sp_b : b ^ 2 * ((a * b) ^ 2)⁻¹ ∉ fourGrp x₁ x₂
  c_x₁ : c * x₁ * c⁻¹ = x₂
  c_x₂ : c * x₂ * c⁻¹ = x₁
  a_x : (a * x₁ * a⁻¹ = x₁ ^ 3 ∧ a * x₂ * a⁻¹ = x₂ ^ 3) ∨
    (a * x₁ * a⁻¹ = x₁ * x₂ ^ 2 ∧ a * x₂ * a⁻¹ = x₁ ^ 2 * x₂)
  a_t : a * t * a⁻¹ = t * (x₁ * x₂) ^ 2
  e₀ : a ^ 2 * t = x₁ * x₂ ^ 3 ∨ a ^ 2 * t = x₁ ^ 3 * x₂

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private lemma fzc_sy3_baseGrp_eq (x₁ x₂ : G) :
    baseGrp x₁ x₂ = zpowers x₁ ⊔ zpowers x₂ := by
  rw [baseGrp]
  have hset : ({x₁, x₂} : Set G) = {x₁} ∪ {x₂} := by ext; simp [or_comm]
  rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]

theorem E_comm (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ e ∈ baseGrp x₁ x₂, ∀ e' ∈ baseGrp x₁ x₂, e * e' = e' * e := by
  intro e he e' he'
  obtain ⟨i, j, -, -, rfl⟩ := fzc_sy3_coord hs.comm hs.ord₁ hs.ord₂ he
  obtain ⟨k, l, -, -, rfl⟩ := fzc_sy3_coord hs.comm hs.ord₁ hs.ord₂ he'
  have hcom : Commute x₁ x₂ := hs.comm
  have h1 : x₁ ^ i * x₂ ^ j * (x₁ ^ k * x₂ ^ l) = x₁ ^ (i + k) * x₂ ^ (j + l) := by
    calc x₁ ^ i * x₂ ^ j * (x₁ ^ k * x₂ ^ l)
        = x₁ ^ i * (x₂ ^ j * x₁ ^ k) * x₂ ^ l := by group
      _ = x₁ ^ i * (x₁ ^ k * x₂ ^ j) * x₂ ^ l := by rw [(hcom.pow_pow k j).eq]
      _ = x₁ ^ (i + k) * x₂ ^ (j + l) := by rw [pow_add, pow_add]; group
  have h2 : x₁ ^ k * x₂ ^ l * (x₁ ^ i * x₂ ^ j) = x₁ ^ (i + k) * x₂ ^ (j + l) := by
    calc x₁ ^ k * x₂ ^ l * (x₁ ^ i * x₂ ^ j)
        = x₁ ^ k * (x₂ ^ l * x₁ ^ i) * x₂ ^ j := by group
      _ = x₁ ^ k * (x₁ ^ i * x₂ ^ l) * x₂ ^ j := by rw [(hcom.pow_pow i l).eq]
      _ = x₁ ^ (k + i) * x₂ ^ (l + j) := by rw [pow_add, pow_add]; group
      _ = x₁ ^ (i + k) * x₂ ^ (j + l) := by rw [Nat.add_comm k i, Nat.add_comm l j]
  rw [h1, h2]

theorem E_exp (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ e ∈ baseGrp x₁ x₂, e ^ 4 = 1 := by
  have e₁ : x₁ ^ 4 = 1 := by rw [← hs.ord₁]; exact pow_orderOf_eq_one x₁
  have e₂ : x₂ ^ 4 = 1 := by rw [← hs.ord₂]; exact pow_orderOf_eq_one x₂
  intro e he
  obtain ⟨i, j, -, -, rfl⟩ := fzc_sy3_coord hs.comm hs.ord₁ hs.ord₂ he
  have hcom : Commute x₁ x₂ := hs.comm
  have h₁ : (x₁ ^ i) ^ 4 = 1 := by
    rw [← pow_mul, show i * 4 = 4 * i by ring, pow_mul, e₁, one_pow]
  have h₂ : (x₂ ^ j) ^ 4 = 1 := by
    rw [← pow_mul, show j * 4 = 4 * j by ring, pow_mul, e₂, one_pow]
  calc (x₁ ^ i * x₂ ^ j) ^ 4
      = (x₁ ^ i) ^ 4 * (x₂ ^ j) ^ 4 := (hcom.pow_pow i j).mul_pow 4
    _ = 1 := by rw [h₁, h₂, mul_one]

theorem E_rank (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    S4A.RankLE (baseGrp x₁ x₂) 2 := by
  have hcomm12 : ∀ u ∈ zpowers x₁, ∀ v ∈ zpowers x₂, u * v = v * u := by
    intro u hu v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute x₁ x₂ from hs.comm).zpow_zpow m n).eq
  have hB : S4A.RankLE (zpowers x₁ ⊔ zpowers x₂) 2 :=
    S4A.RankLE.sup hcomm12 (S4A.RankLE.of_isCyclic (K := zpowers x₁))
      (S4A.RankLE.of_isCyclic (K := zpowers x₂))
  rw [fzc_sy3_baseGrp_eq x₁ x₂]
  exact hB

theorem E_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ e ∈ baseGrp x₁ x₂, e ^ 2 ∈ fourGrp x₁ x₂ := by
  intro e he
  obtain ⟨i, j, hi, hj, rfl⟩ := fzc_sy3_coord hs.comm hs.ord₁ hs.ord₂ he
  rw [fzc_sy3_mem_fourGrp hs.comm hs.ord₁ hs.ord₂]
  refine ⟨i % 2, j % 2, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
  have hcom : Commute x₁ x₂ := hs.comm
  have hsq : (x₁ ^ i * x₂ ^ j) ^ 2 = x₁ ^ (2 * i) * x₂ ^ (2 * j) := by
    rw [(hcom.pow_pow i j).mul_pow 2, ← pow_mul, ← pow_mul,
      Nat.mul_comm i 2, Nat.mul_comm j 2]
  rw [hsq, fzc_sy3_coord_eq hs.ord₁ hs.ord₂ hs.inf]
  omega

theorem Z_le_E (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp]
  refine (Subgroup.closure_le (baseGrp x₁ x₂)).mpr ?_
  intro x hx
  rcases hx with rfl | rfl
  · exact pow_mem (Subgroup.subset_closure (by simp)) 2
  · exact pow_mem (mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

theorem E_le_Wp (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : baseGrp x₁ x₂ ≤ Wp := by
  rw [hs.Wp_eq]
  exact le_sup_left

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
