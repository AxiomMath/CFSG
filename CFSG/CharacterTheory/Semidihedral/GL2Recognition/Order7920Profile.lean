module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.Order7920ProfileSupport
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ExactGL2OrderAlternatives

public section

open scoped Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Semidihedral.Principal.GL2ThreeCharacters

theorem order7920_local_profile_and_degree_ten_character {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 7920)
    (hinv : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (t : G)
    (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3))) :
    (∀ A : Subgroup G, Nat.card A = 11 →
      Subgroup.centralizer (A : Set G) = A ∧ Nat.card (Subgroup.normalizer (A : Set G)) = 55) ∧
    (∀ P : Subgroup G, Nat.card P = 5 →
      Subgroup.centralizer (P : Set G) = P ∧
      ∃ F : Subgroup G, IsCyclic F ∧ Nat.card F = 4 ∧ F ≤ Subgroup.normalizer (P : Set G) ∧
        P ⊓ F = ⊥ ∧ Subgroup.normalizer (P : Set G) = P ⊔ F ∧
        F ⊓ Subgroup.centralizer (P : Set G) = ⊥) ∧
    (∃ g : Fin 10 → G, (∀ x : G, ∃ i, IsConj (g i) x) ∧
      (∀ i j, IsConj (g i) (g j) → i = j) ∧
      (∀ i, orderOf (g i) = ![1, 2, 3, 4, 5, 6, 8, 8, 11, 11] i) ∧
      (∀ i, Nat.card (ConjClasses.mk (g i)).carrier =
        ![1, 165, 440, 990, 1584, 1320, 990, 990, 720, 720] i)) ∧
    (∀ d, Nat.card {x : G // orderOf x = d} =
      if d = 1 then 1 else if d = 2 then 165 else if d = 3 then 440 else if d = 4 then 990
      else if d = 5 then 1584 else if d = 6 then 1320 else if d = 8 then 1980
      else if d = 11 then 1440 else 0) ∧
    (∀ R : Subgroup G, R.Normal → Odd (Nat.card R) → R = ⊥) ∧
    ∃ χ : G → ℂ, χ ∈ CFSG.BlocksIrr G ∧ χ 1 = 10 ∧ χ t = 2 ∧
      (∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 10 → ψ t = 2 → ψ = χ) ∧
      (∀ g, ∃ q : ℚ, χ g = q) ∧ (∀ g, χ g = 10 → g = 1) ∧
      (∀ g, orderOf g = 2 ∨ orderOf g = 4 → χ g = 2) ∧ (∀ g, orderOf g = 3 → χ g = 1) ∧
      (∀ g, orderOf g = 5 ∨ orderOf g = 8 → χ g = 0) ∧
      (∀ g, orderOf g = 6 ∨ orderOf g = 11 → χ g = -1) ∧
      ∃ ψ₂ ψ₃ : G → ℂ, ψ₂ ∈ CFSG.BlocksIrr G ∧ ψ₃ ∈ CFSG.BlocksIrr G ∧ ψ₂ ≠ ψ₃ ∧ ψ₂ ≠ χ ∧
        ψ₃ ≠ χ ∧ ψ₂ 1 = 10 ∧ ψ₃ 1 = 10 ∧ ψ₂ t = -2 ∧ ψ₃ t = -2 ∧
        ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ χ → ψ ≠ ψ₂ → ψ ≠ ψ₃ →
          ∃ d : ℕ, 10 < d ∧ ψ 1 = d := by
  obtain ⟨φ⟩ := hC
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := G23)
  obtain ⟨-, -, -, -, φ', -, -, hφ'val, -⟩ := GL2_three_ordinary_character_table_construction
    basisH a0 GL2ThreeStructure.U FourPointMatrices.C orderOf_a0 GL2ScaledOrders.orderOf_U
    GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center
  let φc : Fin 8 → G23 → ℂ := fun i => (basisH.representation (φ' i)).character
  have hφirr : ∀ i, φc i ∈ CFSG.BlocksIrr G23 := fun i =>
    GL2Columns.label_mem_blocksIrr basisH (φ' i)
  obtain ⟨hperf, hxor⟩ := exact_GL2_centralizer_order_alternatives_core hinv t ht φ a0
    GL2ThreeStructure.U FourPointMatrices.C orderOf_a0 GL2ScaledOrders.orderOf_U
    GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center φc hφirr hφ'val
  have h7920 := hxor.or.resolve_right fun h => by
    have := h.1
    omega
  obtain ⟨-, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ⟨hnd, h1, h2, h3, h4, h5, h6, h7, hβ0, hβ1, hβ2, hβ3,
    hβ4, -⟩, hdeg, ⟨θ₁, hθ₁, θ₂, hθ₂, -, hθ₁1, hθ₂1, hall⟩, -, h10⟩ := h7920
  have hd : ∀ i, ![(χ₁ : G → ℂ) 1, (χ₂ : G → ℂ) 1, (χ₃ : G → ℂ) 1, (χ₄ : G → ℂ) 1,
      (χ₅ : G → ℂ) 1, (χ₆ : G → ℂ) 1, (χ₇ : G → ℂ) 1] i = ![10, 11, 10, 10, 55, 44, 45] i :=
    fun i => congrFun hdeg i
  have hπt : φ ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1 :=
    mulEquiv_self_eq_neg_one ht φ
  obtain ⟨hvt, hvtq, -⟩ := (exact_GL2_centralizer_produces_two_character_columns t ht φ hπt a0
    GL2ThreeStructure.U FourPointMatrices.C orderOf_a0 GL2ScaledOrders.orderOf_U
    GL2ScaledOrders.orderOf_C GL2ScaledOrders.C_not_mem_center φc hφirr hφ'val).2
    χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ 1 (-1) 1 1 ⟨hnd, h1, h2, h3, h4, h5, h6, h7, Or.inl rfl, Or.inr rfl,
      Or.inl rfl, Or.inl rfl, by simpa using hβ0, by simpa using hβ1, by simpa using hβ2,
      by simpa [sub_eq_add_neg] using hβ3, by simpa [sub_eq_add_neg] using hβ4⟩
  have v1 : (χ₁ : G → ℂ) t = 2 := by simpa using congrFun hvt 0
  have v3 : (χ₃ : G → ℂ) t = -2 := by simpa using congrFun hvt 2
  have v4 : (χ₄ : G → ℂ) t = -2 := by simpa using congrFun hvt 3
  set q : G := ((φ.symm GL2ThreeStructure.U : Subgroup.centralizer ({t} : Set G)) : G) with hq
  have vq : (χ₁ : G → ℂ) (t * q) = -1 := by simpa using congrFun hvtq 0
  have hq3 : orderOf q = 3 := by
    rw [hq, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, GL2ScaledOrders.orderOf_U]
  have htq : Commute t q :=
    (Subgroup.mem_centralizer_singleton_iff.mp (φ.symm GL2ThreeStructure.U).2).symm
  have htq6 : orderOf (t * q) = 6 := by
    rw [htq.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ht, hq3]; norm_num), ht, hq3]
  have hirr1 : (χ₁ : G → ℂ) ∈ CFSG.BlocksIrr G := χ₁.2
  have hne1 : (χ₁ : G → ℂ) ≠ 1 := h1
  have hall' : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ∈ [1, (χ₁ : G → ℂ), χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, θ₁, θ₂] := by
    intro ψ hψ
    rcases hall ψ hψ with h | h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨hA, hP, hcl, hcount, hodd, huniq, hrat, hfaith, v24, v3', v58, v611, hgap⟩ :=
    Order7920.order7920_profile_of_core hG hperf hinv ht φ h10 hirr1 hne1 hall' (hd 0) (hd 1)
      (hd 4) (hd 5) (hd 6) hθ₁1 hθ₂1 v1 v3 v4 htq6 vq
  have hχ34 : (χ₃ : G → ℂ) ≠ χ₄ := fun h => by
    have hne := List.nodup_iff_injective_get.mp hnd
    have := @hne ⟨2, by simp⟩ ⟨3, by simp⟩ (Subtype.ext h)
    simp at this
  refine ⟨hA, hP, hcl, hcount, hodd, χ₁, hirr1, hd 0, v1, huniq, hrat, hfaith, v24, v3', v58,
    v611, χ₃, χ₄, χ₃.2, χ₄.2, hχ34, fun h => ?_, fun h => ?_, hd 2, hd 3, v3, v4, hgap⟩
  · have := congrFun h t
    rw [v3, v1] at this
    norm_num at this
  · have := congrFun h t
    rw [v4, v1] at this
    norm_num at this

end CFSG.Semidihedral.GL2Recognition
