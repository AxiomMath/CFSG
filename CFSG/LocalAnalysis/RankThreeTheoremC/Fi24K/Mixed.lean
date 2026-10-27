module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Facts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Dickson.I271.Fi7 Subgroup


theorem sK_mem_normalizer_of_comm {g : J} (h : g * C7 = C7 * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers C7 : Set J) := by
  refine TauCeti.mem_normalizer_zpowers_of_mul_mul_inv_eq_pow (isOfFinOrder_of_finite C7)
    (q := 1) ?_
  rw [pow_one]
  calc g * C7 * g⁻¹ = C7 * g * g⁻¹ := by rw [h]
    _ = C7 := by group


theorem sK_1087_conj_C7 : sK 1087 * C7 * (sK 1087)⁻¹ = C7 ^ 5 := by
  have h := sK_1087_conj
  have hm : sK 1087 * C7 ^ 3 * (sK 1087)⁻¹ = C7 := by
    rw [h]; group
  have h15 : C7 ^ 15 = C7 := by
    rw [show 15 = 7 * 2 + 1 by norm_num, pow_add, pow_mul, C7_pow_seven]
    simp
  have h35 : (C7 ^ 3) ^ 5 = C7 := by
    rw [← pow_mul, show 3 * 5 = 15 by norm_num, h15]
  have h5 : (sK 1087 * C7 ^ 3 * (sK 1087)⁻¹) ^ 5 = sK 1087 * C7 * (sK 1087)⁻¹ := by
    rw [conj_pow, h35]
  calc sK 1087 * C7 * (sK 1087)⁻¹ = (sK 1087 * C7 ^ 3 * (sK 1087)⁻¹) ^ 5 := h5.symm
    _ = C7 ^ 5 := by rw [hm]

theorem sK_1087_mem_normalizer :
    sK 1087 ∈ Subgroup.normalizer (Subgroup.zpowers C7 : Set J) :=
  TauCeti.mem_normalizer_zpowers_of_mul_mul_inv_eq_pow (isOfFinOrder_of_finite C7)
    sK_1087_conj_C7

theorem sK_64_eq : sK 64 = X7 := by
  rw [sK_prefix (by norm_num)]
  rfl

theorem sK_66_eq : sK 66 = Y7 := by
  rw [sK_prefix (by norm_num)]
  rfl

theorem sK_1085_mem_normalizer :
    sK 1085 ∈ Subgroup.normalizer (Subgroup.zpowers C7 : Set J) :=
  sK_mem_normalizer_of_comm sK_1085_comm

theorem sK_1086_mem_normalizer :
    sK 1086 ∈ Subgroup.normalizer (Subgroup.zpowers C7 : Set J) :=
  sK_mem_normalizer_of_comm sK_1086_comm

theorem sK_64_mem_normalizer :
    sK 64 ∈ Subgroup.normalizer (Subgroup.zpowers C7 : Set J) := by
  rw [sK_64_eq]
  exact sK_mem_normalizer_of_comm
    ((Subgroup.mem_centralizer_singleton_iff (g := C7) (k := X7)).1
      (Q7_le_centralizer_c X7_mem))

theorem sK_66_mem_normalizer :
    sK 66 ∈ Subgroup.normalizer (Subgroup.zpowers C7 : Set J) := by
  rw [sK_66_eq]
  exact sK_mem_normalizer_of_comm
    ((Subgroup.mem_centralizer_singleton_iff (g := C7) (k := Y7)).1
      (Q7_le_centralizer_c Y7_mem))

theorem sK_common_mem_normalizer {k : ℕ} (hk : k ∈ [1085, 1086, 64, 66, 1087]) :
    sK k ∈ Subgroup.normalizer (Subgroup.zpowers C7 : Set J) := by
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  exacts [sK_1085_mem_normalizer, sK_1086_mem_normalizer, sK_64_mem_normalizer,
    sK_66_mem_normalizer, sK_1087_mem_normalizer]

theorem sK_1107_mem_centralizer (k : ℕ) (hk : k < 3) :
    sK (1107 + k) ∈ Subgroup.centralizer ({X7} : Set J) := by
  rw [Subgroup.mem_centralizer_singleton_iff, sK_centX hk]
  have hYX : X7 = (sK 1088)⁻¹ * Y7 * sK 1088 := by
    have h := sK_1088_conj
    calc X7 = (sK 1088)⁻¹ * (sK 1088 * X7) := by group
      _ = (sK 1088)⁻¹ * (Y7 * sK 1088) := by rw [h]
      _ = (sK 1088)⁻¹ * Y7 * sK 1088 := by group
  rw [hYX]
  have hc := sK_comm_Y7 hk
  calc (sK 1088)⁻¹ * sK (1082 + k) * sK 1088 * ((sK 1088)⁻¹ * Y7 * sK 1088)
      = (sK 1088)⁻¹ * (sK (1082 + k) * Y7) * sK 1088 := by group
    _ = (sK 1088)⁻¹ * (Y7 * sK (1082 + k)) * sK 1088 := by rw [hc]
    _ = ((sK 1088)⁻¹ * Y7 * sK 1088) * ((sK 1088)⁻¹ * sK (1082 + k) * sK 1088) := by
      group

theorem closure_normalizer_union_centralizer_Y7 :
    Subgroup.closure ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
      (centralizer ({Y7} : Set J) : Set J)) = ⊤ := by
  set S : Set J := (normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
    (centralizer ({Y7} : Set J) : Set J) with hS
  change Subgroup.closure S = ⊤
  have hgs : sK '' {k | k ∈ [1085, 1086, 64, 66, 1087, 1082, 1083, 1084]} ⊆
      Subgroup.closure S := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inr (Subgroup.mem_centralizer_singleton_iff.2
        (sK_comm_Y7 (k := 0) (by norm_num))))
    · exact Subgroup.subset_closure (Or.inr (Subgroup.mem_centralizer_singleton_iff.2
        (sK_comm_Y7 (k := 1) (by norm_num))))
    · exact Subgroup.subset_closure (Or.inr (Subgroup.mem_centralizer_singleton_iff.2
        (sK_comm_Y7 (k := 2) (by norm_num))))
  have hle : Subgroup.closure (sK '' {k | k ∈ [1085, 1086, 64, 66, 1087, 1082, 1083, 1084]}) ≤
      Subgroup.closure S := by
    rw [Subgroup.closure_le]
    exact hgs
  obtain ⟨ha, hb⟩ := mixed_facts
    ⟨[1085, 1086, 64, 66, 1087, 1082, 1083, 1084], 1110, 1657, 1655, 1656⟩
    (by simp [mixedSecs])
  have hab : Subgroup.closure ({a, b} : Set J) ≤ Subgroup.closure S := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hle ha
    · exact hle hb
  have htop : (⊤ : Subgroup J) ≤ Subgroup.closure S := by
    rw [← closure_ab]
    exact hab
  exact top_le_iff.mp htop

theorem closure_normalizer_union_centralizer_X7 :
    Subgroup.closure ((normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
      (centralizer ({X7} : Set J) : Set J)) = ⊤ := by
  set S : Set J := (normalizer ((zpowers C7 : Subgroup J) : Set J) : Set J) ∪
    (centralizer ({X7} : Set J) : Set J) with hS
  change Subgroup.closure S = ⊤
  have hgs : sK '' {k | k ∈ [1085, 1086, 64, 66, 1087, 1107, 1108, 1109]} ⊆
      Subgroup.closure S := by
    rintro _ ⟨k, hk, rfl⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inl (sK_common_mem_normalizer (by simp)))
    · exact Subgroup.subset_closure (Or.inr (sK_1107_mem_centralizer 0 (by norm_num)))
    · exact Subgroup.subset_closure (Or.inr (sK_1107_mem_centralizer 1 (by norm_num)))
    · exact Subgroup.subset_closure (Or.inr (sK_1107_mem_centralizer 2 (by norm_num)))
  have hle : Subgroup.closure (sK '' {k | k ∈ [1085, 1086, 64, 66, 1087, 1107, 1108, 1109]}) ≤
      Subgroup.closure S := by
    rw [Subgroup.closure_le]
    exact hgs
  obtain ⟨ha, hb⟩ := mixed_facts
    ⟨[1085, 1086, 64, 66, 1087, 1107, 1108, 1109], 1657, 2208, 2206, 2207⟩
    (by simp [mixedSecs])
  have hab : Subgroup.closure ({a, b} : Set J) ≤ Subgroup.closure S := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hle ha
    · exact hle hb
  have htop : (⊤ : Subgroup J) ≤ Subgroup.closure S := by
    rw [← closure_ab]
    exact hab
  exact top_le_iff.mp htop

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
