module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AProd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma31Elem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma31Cent
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem t_mem_S_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : t ∈ S := by
  rw [(S_eq_prod_of h h43 h44).1]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)

theorem t_mem_of_isE16 (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {Y : Subgroup G} (hY : IsE16In S Y) : t ∈ Y := by
  by_contra htY
  have hM := m12Rel_of_ctx h h44
  have hY'leS : Y ⊔ zpowers t ≤ S :=
    sup_le hY.1 (Subgroup.zpowers_le.mpr (t_mem_S_of h h43 h44))
  have hY'ele : CFSG.Open.IsElemAbelian 2 (Y ⊔ zpowers t) :=
    isElemAbelian_sup_zpowers h hY.1 hY.2.1
  have hcardY' : Nat.card (Y ⊔ zpowers t : Subgroup G) = 2 * Nat.card Y :=
    card_sup_zpowers_of_t_not_mem h hY.1 htY
  have htY' : t ∈ (Y ⊔ zpowers t : Subgroup G) := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hcard' : Nat.card ((Y ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) = 16 := by
    have hthis := (eq_sup_inf_of_t_mem h h43 h44 hY'leS htY').2
    rw [hcardY', hY.2.2] at hthis
    omega
  have hle8 : Nat.card ((Y ⊔ zpowers t) ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) ≤ 8 :=
    hM.card_le_eight_of_elemAbelian inf_le_right (CFSG.Open.IsElemAbelian.mono hY'ele inf_le_left)
  omega

theorem E16_facts (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {Y : Subgroup G} (hY : IsE16In S Y) :
    Y = zpowers t ⊔ (Y ⊓ m12Grp x₁ x₂ lam tau) ∧
      CFSG.Open.IsElemAbelian 2 (Y ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) ∧
      Nat.card (Y ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) = 8 := by
  obtain ⟨hYeq, hcard2⟩ := eq_sup_inf_of_t_mem h h43 h44 hY.1
    (t_mem_of_isE16 h h43 h44 hY)
  refine ⟨hYeq, CFSG.Open.IsElemAbelian.mono hY.2.1 inf_le_left, ?_⟩
  rw [hY.2.2] at hcard2
  omega

theorem z_mem_of_isE16 (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {Y : Subgroup G} (hY : IsE16In S Y) : (x₁ * x₂) ^ 2 ∈ Y := by
  have hM := m12Rel_of_ctx h h44
  obtain ⟨-, hea, hcard8⟩ := E16_facts h h43 h44 hY
  have hz_in : (x₁ * x₂) ^ 2 ∈
      m12Grp x₁ x₂ lam tau ⊓ centralizer ((m12Grp x₁ x₂ lam tau : Subgroup G) : Set G) := by
    rw [hM.center_eq]
    exact Subgroup.mem_zpowers _
  have hzM : (x₁ * x₂) ^ 2 ∈ m12Grp x₁ x₂ lam tau := (Subgroup.mem_inf.mp hz_in).1
  have hzC : (x₁ * x₂) ^ 2 ∈
      centralizer ((m12Grp x₁ x₂ lam tau : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hz_in).2
  have hzCE8 : (x₁ * x₂) ^ 2 ∈
      centralizer ((Y ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp hzC) e (Subgroup.mem_inf.mp he).2
  have hzE8 : (x₁ * x₂) ^ 2 ∈ (Y ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) := by
    rw [← hM.centralizer_eq_of_elemAbelian_eight inf_le_right hea hcard8]
    exact Subgroup.mem_inf.mpr ⟨hzM, hzCE8⟩
  exact (Subgroup.mem_inf.mp hzE8).1

theorem lemma4_7a_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : Lemma4_7aConcl t S x₁ x₂ := by
  intro Y hY
  have hM := m12Rel_of_ctx h h44
  obtain ⟨hYeq, hea, hcard8⟩ := E16_facts h h43 h44 hY
  refine ⟨(center_S_of h h43).symm, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact t_mem_of_isE16 h h43 h44 hY
    · exact z_mem_of_isE16 h h43 h44 hY
  · refine le_antisymm ?_ ?_
    · calc S ⊓ centralizer (Y : Set G)
          ≤ S ⊓ centralizer ((Y ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) : Set G) :=
            inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left)
        _ = zpowers t ⊔ (m12Grp x₁ x₂ lam tau ⊓
              centralizer ((Y ⊓ m12Grp x₁ x₂ lam tau : Subgroup G) : Set G)) :=
            centralizer_S_inf h h43 h44 inf_le_right
        _ = zpowers t ⊔ (Y ⊓ m12Grp x₁ x₂ lam tau) := by
            rw [hM.centralizer_eq_of_elemAbelian_eight inf_le_right hea hcard8]
        _ = Y := hYeq.symm
    · intro y hy
      rw [Subgroup.mem_inf]
      refine ⟨hY.1 hy, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      have hc := hY.2.1.1.is_comm.comm (⟨y, hy⟩ : Y) (⟨y', hy'⟩ : Y)
      exact (congrArg Subtype.val hc).symm

theorem lemma4_7b_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : Lemma4_7bConcl t S x₁ x₂ tau := by
  intro Y hY hYN
  have hM := m12Rel_of_ctx h h44
  obtain ⟨hYeq, hea, hcard8⟩ := E16_facts h h43 h44 hY
  have hE8N : NormalIn (Y ⊓ m12Grp x₁ x₂ lam tau) (m12Grp x₁ x₂ lam tau) :=
    normalIn_inf_m12Grp h hYN
  have hzY : (x₁ * x₂) ^ 2 ∈ Y := z_mem_of_isE16 h h43 h44 hY
  have hzsq : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
    rw [← pow_two]
    exact hY.2.1.2 ((x₁ * x₂) ^ 2) hzY
  have hx1_4 : x₁ ^ 4 = 1 := by
    rw [← hM.ord_x₁]; exact pow_orderOf_eq_one x₁
  have hx2_4 : x₂ ^ 4 = 1 := by
    rw [← hM.ord_x₂]; exact pow_orderOf_eq_one x₂
  have hu4 : (x₁ * x₂) ^ 4 = 1 := by
    rw [(show Commute x₁ x₂ from hM.comm).mul_pow 4, hx1_4, hx2_4, mul_one]
  have hconj : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
    calc tau * (x₁ * x₂) * tau⁻¹
        = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
      _ = x₁⁻¹ * x₂⁻¹ := by rw [hM.tau_x₁, hM.tau_x₂]
      _ = (x₁ * x₂)⁻¹ := by rw [← mul_inv_rev, hM.comm.symm]
  have hu3 : (x₁ * x₂) ^ 3 = (x₁ * x₂)⁻¹ := by
    have h4' : (x₁ * x₂) ^ 3 * (x₁ * x₂) = 1 := by rw [← pow_succ, hu4]
    calc (x₁ * x₂) ^ 3
        = ((x₁ * x₂) ^ 3 * (x₁ * x₂)) * (x₁ * x₂)⁻¹ := by group
      _ = 1 * (x₁ * x₂)⁻¹ := by rw [h4']
      _ = (x₁ * x₂)⁻¹ := by rw [one_mul]
  have hzeq : tau * (x₁ * x₂) = (x₁ * x₂) ^ 2 * (x₁ * x₂ * tau) := by
    calc tau * (x₁ * x₂)
        = (tau * (x₁ * x₂) * tau⁻¹) * tau := by group
      _ = (x₁ * x₂)⁻¹ * tau := by rw [hconj]
      _ = (x₁ * x₂) ^ 3 * tau := by rw [hu3]
      _ = ((x₁ * x₂) ^ 2 * (x₁ * x₂)) * tau := by
            rw [show (x₁ * x₂) ^ 3 = (x₁ * x₂) ^ 2 * (x₁ * x₂) from pow_succ _ 2]
      _ = (x₁ * x₂) ^ 2 * (x₁ * x₂ * tau) := by group
  have hzeq2 : x₁ * x₂ * tau = (x₁ * x₂) ^ 2 * (tau * (x₁ * x₂)) := by
    rw [hzeq, ← mul_assoc, hzsq, one_mul]
  rcases hM.eq_of_normal_elemAbelian_eight inf_le_right hea hcard8 hE8N with hcase | hcase
  · left
    rw [hYeq, hcase, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · right
    rw [hYeq, hcase, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    have hUnion : ({t} ∪ ({x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} : Set G)) =
        ({t, x₁ ^ 2, (x₁ * x₂) ^ 2, x₁ * x₂ * tau} : Set G) := by
      ext x
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hUnion]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · rw [hzeq2]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · rw [hzeq]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
