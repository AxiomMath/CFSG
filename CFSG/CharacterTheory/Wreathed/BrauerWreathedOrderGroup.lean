module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderGroupModel

public section

namespace CFSG.Wreathed.BrauerWreathedOrder

open scoped Pointwise
open CFSG.Wreathed.BrauerWong

universe u

theorem modelV_eq_closure {G : Type u} [Group G] [Finite G] {n : ℕ} (hn : 1 ≤ n)
    {S : Sylow 2 G} {S₁ S₂ T : G} (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T) :
    modelV S (hW.equiv hn) = Subgroup.closure {S₁ * S₂, S₁ ^ 2 ^ (n - 1), T} := by
  rw [modelV, Original.V, MonoidHom.map_closure, Set.image_insert_eq, Set.image_pair,
    hW.modelHom_a hn, hW.modelHom_x2 hn, hW.modelHom_z hn]

theorem caseA_iff_central_product_sym3 {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (S₁ S₂ T : G) (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T) :
    let J := (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let V := Subgroup.closure {S₁ * S₂, J₁, T}
    (∃ g ∈ Subgroup.centralizer {J}, g⁻¹ * T * g = J₁) ↔
      Nonempty (Subgroup.normalizer (V : Set G) ⧸
        (V.subgroupOf (Subgroup.normalizer (V : Set G)) ⊔
          (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))) ≃*
        Equiv.Perm (Fin 3)) := by
  intro J J₁ V
  have hn1 : 1 ≤ n := by omega
  have hJ : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁ : wreathModelHom S (hW.equiv hn1) (Original.x2 (2 ^ n)) = J₁ := hW.modelHom_x2 hn1
  have hz : wreathModelHom S (hW.equiv hn1) (Original.z (2 ^ n)) = T := hW.modelHom_z hn1
  have hV : modelV S (hW.equiv hn1) = V := modelV_eq_closure hn1 hW
  have key : Nonempty (Subgroup.normalizer (modelV S (hW.equiv hn1) : Set G) ⧸
      modelVInnerCentralizer S (hW.equiv hn1) ≃* Equiv.Perm (Fin 3)) ↔
      Nonempty (Subgroup.normalizer (V : Set G) ⧸
        (V.subgroupOf (Subgroup.normalizer (V : Set G)) ⊔
          (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))) ≃*
        Equiv.Perm (Fin 3)) := by
    rw [← hV]
    rfl
  constructor
  · intro h
    exact key.mp (vSym3_of_swap_conj n hn S (hW.equiv hn1) (by rw [hJ, hz, hJ₁]; exact h))
  · intro h
    have h'' := swap_conj_of_vSym3 n hn S (hW.equiv hn1) (key.mpr h)
    rw [hJ, hz, hJ₁] at h''
    exact h''

theorem noAbelianTwoPowerIndexIntersection_of_caseA {G : Type u} [Group G] [Finite G] (n : ℕ)
    (hn : 2 ≤ n) (S : Sylow 2 G) (S₁ S₂ T : G)
    (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T)
    (hA : ∃ g ∈ Subgroup.centralizer {(S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)},
      g⁻¹ * T * g = S₁ ^ 2 ^ (n - 1)) :
    NoAbelianTwoPowerIndexIntersection G (S : Subgroup G) := by
  have hn1 : 1 ≤ n := by omega
  have hJ : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) =
      (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1) := hW.modelHom_x hn
  have hJ₁ : wreathModelHom S (hW.equiv hn1) (Original.x2 (2 ^ n)) = S₁ ^ 2 ^ (n - 1) :=
    hW.modelHom_x2 hn1
  have hz : wreathModelHom S (hW.equiv hn1) (Original.z (2 ^ n)) = T := hW.modelHom_z hn1
  exact noAbelian_of_vSym3 n hn S (hW.equiv hn1)
    (vSym3_of_swap_conj n hn S (hW.equiv hn1) (by rw [hJ, hz, hJ₁]; exact hA))

theorem centralizer_J_typeII_of_caseA {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (S₁ S₂ T : G) (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T)
    (hA : ∃ g ∈ Subgroup.centralizer {(S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)},
      g⁻¹ * T * g = S₁ ^ 2 ^ (n - 1)) :
    let J := (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)
    (S : Subgroup G) ≤ Subgroup.centralizer {J} ∧
      NoAbelianTwoPowerIndexIntersection ↥(Subgroup.centralizer ({J} : Set G))
        ((S : Subgroup G).subgroupOf (Subgroup.centralizer {J})) ∧
      IsTypeII ↥(Subgroup.centralizer ({J} : Set G))
        ((S : Subgroup G).subgroupOf (Subgroup.centralizer {J})) n := by
  intro J
  have hn1 : 1 ≤ n := by omega
  have hJ : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁ : wreathModelHom S (hW.equiv hn1) (Original.x2 (2 ^ n)) = S₁ ^ 2 ^ (n - 1) :=
    hW.modelHom_x2 hn1
  have hz : wreathModelHom S (hW.equiv hn1) (Original.z (2 ^ n)) = T := hW.modelHom_z hn1
  have hsix := vSym3_of_swap_conj n hn S (hW.equiv hn1) (by rw [hJ, hz, hJ₁]; exact hA)
  have hJZ : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) ∈
      modelCenter S (hW.equiv hn1) :=
    ⟨_, (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩
  have hJ1 : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) ≠ 1 := by
    intro h
    have h' := (orderOf_injective _ (wreathModelHom_injective S (hW.equiv hn1))
      (Original.x (2 ^ n))).symm
    have hx2 := (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
    rw [h, orderOf_one, hx2] at h'
    omega
  have h := centralizer_noAbelian_and_typeII S (hW.equiv hn1) hn hsix hJZ hJ1
  rw [hJ] at h
  exact h

theorem case_one_three_cycle {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (S₁ S₂ T : G) (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T) :
    let J := (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let J₂ := S₂ ^ 2 ^ (n - 1)
    let S₀ := Subgroup.closure {S₁, S₂}
    (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G)) = 6 →
    ∃ Y : G, (∃ k : ℕ, orderOf Y = 3 ^ k) ∧ Y⁻¹ * J * Y = J₁ ∧ Y⁻¹ * J₁ * Y = J₂ ∧
      Y⁻¹ * J₂ * Y = J := by
  intro J J₁ J₂ S₀ h6
  have hn1 : 1 ≤ n := by omega
  have hJ : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁ : wreathModelHom S (hW.equiv hn1) (Original.x2 (2 ^ n)) = J₁ := hW.modelHom_x2 hn1
  have hJ₂ : wreathModelHom S (hW.equiv hn1) (Original.t (2 ^ n) ^ (2 ^ n / 2)) = J₂ :=
    hW.modelHom_t_half hn1
  have hB : modelBase S (hW.equiv hn1) = S₀ := hW.modelBase_eq hn1
  rcases base_relIndex_cases n hn S (hW.equiv hn1) with h2 | ⟨-, hbase⟩
  · rw [hB] at h2
    omega
  · have h := three_power_cycle_of_base_sym3 n hn S (hW.equiv hn1) hbase
    rw [hJ, hJ₁, hJ₂] at h
    exact h

theorem case_one_a_no_index_two {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (S₁ S₂ T : G) (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T) :
    let J := (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let S₀ := Subgroup.closure {S₁, S₂}
    (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G)) = 6 →
    (∃ g ∈ Subgroup.centralizer {J}, g⁻¹ * T * g = J₁) →
    ¬ ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  intro J J₁ S₀ h6 hA
  have hn1 : 1 ≤ n := by omega
  have hJ : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁ : wreathModelHom S (hW.equiv hn1) (Original.x2 (2 ^ n)) = J₁ := hW.modelHom_x2 hn1
  have hz : wreathModelHom S (hW.equiv hn1) (Original.z (2 ^ n)) = T := hW.modelHom_z hn1
  have hB : modelBase S (hW.equiv hn1) = S₀ := hW.modelBase_eq hn1
  rcases base_relIndex_cases n hn S (hW.equiv hn1) with h2 | ⟨-, hbase⟩
  · rw [hB] at h2
    omega
  · exact typeI_of_base_sym3 n hn S (hW.equiv hn1) hbase
      (vSym3_of_swap_conj n hn S (hW.equiv hn1) (by rw [hJ, hz, hJ₁]; exact hA))

theorem case_one_a_isTypeI {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (S₁ S₂ T : G) (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T)
    (h6 : (Subgroup.centralizer ((Subgroup.closure {S₁, S₂} : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer ((Subgroup.closure {S₁, S₂} : Subgroup G) : Set G)) = 6)
    (hA : ∃ g ∈ Subgroup.centralizer {(S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)},
      g⁻¹ * T * g = S₁ ^ 2 ^ (n - 1)) :
    IsTypeI G :=
  case_one_a_no_index_two n hn S S₁ S₂ T hW h6 hA

theorem case_one_a_all_involutions_conjugate {G : Type u} [Group G] [Finite G] (n : ℕ)
    (hn : 2 ≤ n) (S : Sylow 2 G) (S₁ S₂ T : G)
    (hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T) :
    let J := (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let S₀ := Subgroup.closure {S₁, S₂}
    (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G)) = 6 →
    (∃ g ∈ Subgroup.centralizer {J}, g⁻¹ * T * g = J₁) →
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  intro J J₁ S₀ h6 hA
  have hn1 : 1 ≤ n := by omega
  have hJ : wreathModelHom S (hW.equiv hn1) (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁ : wreathModelHom S (hW.equiv hn1) (Original.x2 (2 ^ n)) = J₁ := hW.modelHom_x2 hn1
  have hz : wreathModelHom S (hW.equiv hn1) (Original.z (2 ^ n)) = T := hW.modelHom_z hn1
  obtain ⟨Y, -, hY1, -, -⟩ := case_one_three_cycle n hn S S₁ S₂ T hW h6
  obtain ⟨g, -, hg⟩ := hA
  apply all_involutions_conjugate_of_conj n hn S (hW.equiv hn1)
  · rw [hJ, hJ₁]
    exact isConj_iff.mpr ⟨Y⁻¹, by rw [inv_inv]; exact hY1⟩
  · rw [hz, hJ₁]
    exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

theorem brauer_wreathed_order_group_cases {G : Type} [Group G] [Fintype G] (n : ℕ)
    (hn : 2 ≤ n) (S : Sylow 2 G) (S₁ S₂ T : G)
    (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1))
    (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
    (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂) :
    let A := S₁⁻¹ * S₂⁻¹
    let J := A ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let J₂ := S₂ ^ 2 ^ (n - 1)
    let S₀ := Subgroup.closure {S₁, S₂}
    let D := Subgroup.closure {J, J₁}
    let c : Set G → ℕ := fun X => Nat.card (Subgroup.centralizer X)
    let idx := (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G))
    let caseA : Prop := ∃ g ∈ Subgroup.centralizer {J}, g⁻¹ * T * g = J₁
    (idx = 2 ∨ idx = 6) ∧
    (idx = 2 → ¬ caseA → CFSG.HasNormalPComplement 2 G) ∧
    ((idx = 6 ∧ ¬ caseA) ∨ idx = 2 → ∃ H : Subgroup G, H.Normal ∧ H.index = 2) ∧
    (idx = 6 → caseA → ¬ ∃ H : Subgroup G, H.Normal ∧ H.index = 2) ∧
    (idx = 6 → ∃ Y : G, (∃ k : ℕ, orderOf Y = 3 ^ k) ∧ Y⁻¹ * J * Y = J₁ ∧ Y⁻¹ * J₁ * Y = J₂ ∧
      Y⁻¹ * J₂ * Y = J) ∧
    (idx = 6 → caseA → ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
    (idx = 2 → caseA → Nat.card G * c (D : Set G) ^ 2 = c {J} * c {J₁} ^ 2) := by
  intro A J J₁ J₂ S₀ D c idx caseA
  have hW : WreathGenerators n (S : Subgroup G) S₁ S₂ T :=
    ⟨hgen, hcard, hS₁, hS₂, hT, hcomm, hconj⟩
  have hn1 : 1 ≤ n := by omega
  set e := hW.equiv hn1 with he
  have hJ : wreathModelHom S e (Original.x (2 ^ n)) = J := hW.modelHom_x hn
  have hJ₁ : wreathModelHom S e (Original.x2 (2 ^ n)) = J₁ := hW.modelHom_x2 hn1
  have hz : wreathModelHom S e (Original.z (2 ^ n)) = T := hW.modelHom_z hn1
  have hB : modelBase S e = S₀ := hW.modelBase_eq hn1
  have hidx : idx = (Subgroup.centralizer (modelBase S e : Set G)).relIndex
      (Subgroup.normalizer (modelBase S e : Set G)) := by
    rw [hB]
  have hcaseA : caseA ↔ ∃ g ∈ Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} :
      Set G), g⁻¹ * wreathModelHom S e (Original.z (2 ^ n)) * g =
        wreathModelHom S e (Original.x2 (2 ^ n)) := by
    rw [hJ, hz, hJ₁]
  have hcases := base_relIndex_cases n hn S e
  rw [← hidx] at hcases
  have hb2 : idx = 2 → Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2 := by
    intro h2
    rw [← relIndex_eq_card_quotient, ← hidx]
    exact h2
  have hbase : idx = 6 → Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) := by
    intro h6
    rcases hcases with h2 | ⟨-, h⟩
    · omega
    · exact h
  have hv2 : ¬ caseA → Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2 := by
    intro hnA
    rcases modelVNormalizerQuotient_alternatives n hn S e with h | h
    · exact h
    · exact absurd (hcaseA.mpr (swap_conj_of_vSym3 n hn S e h)) hnA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rcases hcases with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  ·
    intro h2 hnA
    obtain ⟨N, hN, hodd, k, hk⟩ :=
      normal_two_complement_of_order_two n hn S e (hb2 h2) (hv2 hnA)
    refine ⟨N, hN, Nat.coprime_two_left.mpr hodd, IsPGroup.of_card (n := k) ?_⟩
    rw [← Subgroup.index_eq_card]
    exact hk
  ·
    rintro (⟨-, hnA⟩ | h2)
    · exact index_two_of_v_order_two n hn S e (hv2 hnA)
    · exact index_two_of_base_order_two n hn S e (hb2 h2)
  ·
    intro h6 hA
    exact typeI_of_base_sym3 n hn S e (hbase h6) (vSym3_of_swap_conj n hn S e (hcaseA.mp hA))
  ·
    intro h6
    exact case_one_three_cycle n hn S S₁ S₂ T hW h6
  ·
    intro h6 hA
    exact case_one_a_all_involutions_conjugate n hn S S₁ S₂ T hW h6 hA
  ·
    intro h2 _
    have h := order_formula_of_base_order_two n hn S e (hb2 h2)
    rw [hJ, hJ₁] at h
    exact h

end CFSG.Wreathed.BrauerWreathedOrder
