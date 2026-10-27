module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.K28Data
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.SylowConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathInvol

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.K28

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier CFSG.Certificates

section Orders


theorem card_P : Nat.card QP.originalSubgroup = 6048 := by
  rw [card_group QP QP_ok, QP_valid.2]

theorem card_A : Nat.card QA.originalSubgroup = 12096 := by
  rw [card_group QA QA_ok, QA_valid.2]

theorem T_le_P : wreathGrp fx₁ fx₂ flam ≤ QP.originalSubgroup := by
  rw [wreathGrp, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact fx₁_mem
  · exact fx₂_mem
  · exact flam_mem

theorem card_T : Nat.card (wreathGrp fx₁ fx₂ flam) = 32 :=
  wreathRel_frame.card_wreathGrp

theorem S_le_A : m12Grp fx₁ fx₂ flam ftau ≤ QA.originalSubgroup := by
  rw [m12Grp, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact P_le_A fx₁_mem
  · exact P_le_A fx₂_mem
  · exact P_le_A flam_mem
  · exact ftau_mem_A

theorem card_S : Nat.card (m12Grp fx₁ fx₂ flam ftau) = 64 :=
  m12Rel_frame.card_m12Grp

theorem P_normal_in_A : ∀ a ∈ QA.originalSubgroup, ∀ p ∈ QP.originalSubgroup,
    a * p * a⁻¹ ∈ QP.originalSubgroup := by
  obtain ⟨M, hP, hA⟩ := CFSG.GH74.KGroups.U33.autModel
    (K := ↥QP.originalSubgroup) (MulEquiv.refl _)
  intro a ha p hp
  have haA : a ∈ M.A := by rw [hA]; exact ha
  let ψ : MulAut (↥QP.originalSubgroup) := M.Φ.symm ⟨a, haA⟩
  have hΦ : (M.Φ ψ : Pm) = a := by simp [ψ]
  let x : ↥QP.originalSubgroup := M.e.symm ⟨p, by rw [hP]; exact hp⟩
  have hx : (M.e x : Pm) = p := by simp [x]
  have hspec : ((M.e (ψ x) : ↥M.P) : Pm) = a * p * a⁻¹ := by
    rw [M.spec ψ x, hΦ, hx]
  have hmemP : ((M.e (ψ x) : ↥M.P) : Pm) ∈ M.P := (M.e (ψ x)).2
  rw [← hspec]
  exact (le_of_eq hP) hmemP

theorem mem_A_cases : ∀ a ∈ QA.originalSubgroup,
    a ∈ QP.originalSubgroup ∨ a * ftau ∈ QP.originalSubgroup := by
  intro a ha
  by_cases haP : a ∈ QP.originalSubgroup
  · exact Or.inl haP
  · right
    have hHindex : (QP.originalSubgroup.subgroupOf QA.originalSubgroup).index = 2 := by
      have hrel : QP.originalSubgroup.relIndex QA.originalSubgroup = 2 := by
        have h := Subgroup.relIndex_mul_card (H := QP.originalSubgroup)
          (K := QA.originalSubgroup)
        rw [inf_of_le_left P_le_A, card_P, card_A] at h
        have h' : QP.originalSubgroup.relIndex QA.originalSubgroup * 6048 = 2 * 6048 := by
          rw [h]
        exact Nat.mul_right_cancel (by norm_num) h'
      exact hrel
    have hftauA : ftau ∈ QA.originalSubgroup := ftau_mem_A
    have hb : (⟨a, ha⟩ : ↥QA.originalSubgroup) ∉
        QP.originalSubgroup.subgroupOf QA.originalSubgroup := fun h => haP h
    have ht : (⟨ftau, hftauA⟩ : ↥QA.originalSubgroup) ∉
        QP.originalSubgroup.subgroupOf QA.originalSubgroup := fun h => ftau_not_mem_P h
    have hmul : (⟨a, ha⟩ : ↥QA.originalSubgroup) * ⟨ftau, hftauA⟩ ∈
        QP.originalSubgroup.subgroupOf QA.originalSubgroup := by
      rw [Subgroup.mul_mem_iff_of_index_two hHindex]
      exact iff_of_false hb ht
    exact Subgroup.mem_subgroupOf.mp hmul

end Orders

section Classes


private lemma conj_trans {c₂ c₁ g g' : Pm} (hgg : g' = c₁ * g * c₁⁻¹)
    (h : c₂ * g' * c₂⁻¹ = fz) : (c₂ * c₁) * g * (c₂ * c₁)⁻¹ = fz := by
  have key : (c₂ * c₁) * g * (c₂ * c₁)⁻¹ = c₂ * g' * c₂⁻¹ := by
    rw [hgg]
    group
  rw [key, h]

theorem invol_conj_fz {g : Pm} (hg : g ∈ QP.originalSubgroup) (h2 : g * g = 1) (h1 : g ≠ 1) :
    ∃ c ∈ QP.originalSubgroup, c * g * c⁻¹ = fz := by
  obtain ⟨c₁, hc₁, hc₁T⟩ := exists_conj_mem_sylow (Γ := QP.originalSubgroup)
    (Q := wreathGrp fx₁ fx₂ flam) (p := 2) (a := 5) (m := 189)
    (by rw [card_P]; norm_num) (by norm_num) T_le_P (by rw [card_T]; norm_num)
    hg (by rw [pow_two]; exact h2)
  set g' : Pm := c₁ * g * c₁⁻¹ with hg'def
  have hg'T : g' ∈ wreathGrp fx₁ fx₂ flam := by rw [hg'def]; exact hc₁T
  have hg'2 : g' * g' = 1 := by
    rw [hg'def]
    calc (c₁ * g * c₁⁻¹) * (c₁ * g * c₁⁻¹) = c₁ * (g * g) * c₁⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hg'1 : g' ≠ 1 := by
    intro h
    apply h1
    have hg_eq : c₁⁻¹ * g' * c₁ = g := by rw [hg'def]; group
    rw [← hg_eq, h]
    group
  rcases WreathRel.involution_cases wreathRel_frame hg'T hg'2 hg'1 with
    hcase | hcase | hcase | ⟨a, hcase⟩
  · have hconj : frho * g' * frho⁻¹ = fz := by
      rw [hcase, ← fy]
      exact involT_conj_fz.1
    exact ⟨frho * c₁, Subgroup.mul_mem _ frho_mem hc₁, conj_trans hg'def hconj⟩
  · have hconj : frho⁻¹ * g' * (frho⁻¹)⁻¹ = fz := by
      rw [hcase]
      exact involT_conj_fz.2.1
    exact ⟨frho⁻¹ * c₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ frho_mem) hc₁,
      conj_trans hg'def hconj⟩
  · have hconj : g' = fz := by rw [hcase]; rfl
    refine ⟨c₁, hc₁, ?_⟩
    rw [hg'def.symm, hconj]
  · have hconj : (fk0⁻¹ * (fx₁⁻¹) ^ a.val) * g' * (fk0⁻¹ * (fx₁⁻¹) ^ a.val)⁻¹ = fz := by
      rw [hcase]
      exact involT_conj_fz.2.2 a
    refine ⟨(fk0⁻¹ * (fx₁⁻¹) ^ a.val) * c₁, ?_, conj_trans hg'def hconj⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ fk0_mem)
      (Subgroup.pow_mem _ (Subgroup.inv_mem _ fx₁_mem) a.val)) hc₁

theorem outer_invol_conj_ftau {g : Pm} (hg : g ∈ QA.originalSubgroup)
    (hgP : g ∉ QP.originalSubgroup) (h2 : g * g = 1) :
    ∃ c ∈ QP.originalSubgroup, c * ftau * c⁻¹ = g := by
  obtain ⟨c₀, hc₀A, hc₀S⟩ := exists_conj_mem_sylow (Γ := QA.originalSubgroup)
    (Q := m12Grp fx₁ fx₂ flam ftau) (p := 2) (a := 6) (m := 189)
    (by rw [card_A]; norm_num) (by norm_num) S_le_A (by rw [card_S]; norm_num)
    hg (by rw [pow_two]; exact h2)
  set g' : Pm := c₀ * g * c₀⁻¹ with hg'def
  have hg'S : g' ∈ m12Grp fx₁ fx₂ flam ftau := by rw [hg'def]; exact hc₀S
  have hg'2 : g' * g' = 1 := by
    rw [hg'def]
    calc (c₀ * g * c₀⁻¹) * (c₀ * g * c₀⁻¹) = c₀ * (g * g) * c₀⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have hg'T : g' ∉ wreathGrp fx₁ fx₂ flam := by
    intro hT
    apply hgP
    have hg'P : g' ∈ QP.originalSubgroup := T_le_P hT
    have hmem := P_normal_in_A c₀⁻¹ (Subgroup.inv_mem _ hc₀A) g' hg'P
    have hgeq : g = c₀⁻¹ * g' * c₀ := by rw [hg'def]; group
    rw [hgeq]
    simpa using hmem
  rcases M12Rel.outer_involution_cases m12Rel_frame hg'S hg'T hg'2 with
    ⟨a, b, hg'⟩ | ⟨a, hg'⟩
  · let w : Pm := wordP (outerW.getD (4 * a.val + b.val) [])
    have hwP : w ∈ QP.originalSubgroup := by dsimp only [w]; exact wordP_mem _
    have hwspec : w * ftau * w⁻¹ = g' := by
      dsimp only [w]
      rw [outerW_spec a b]
      exact hg'.symm
    let q : Pm := c₀⁻¹ * w
    have hqA : q ∈ QA.originalSubgroup :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₀A) (P_le_A hwP)
    have hqeq : q * ftau * q⁻¹ = g := by
      have h1 : g = c₀⁻¹ * g' * c₀ := by rw [hg'def]; group
      rw [h1, ← hwspec]
      dsimp only [q]
      group
    rcases mem_A_cases q hqA with hqP | hqp
    · exact ⟨q, hqP, hqeq⟩
    · refine ⟨q * ftau, hqp, ?_⟩
      rw [← hqeq]
      have hftau2 : ftau * ftau = 1 := by rw [← pow_two]; exact ftau_pow.1
      have hfinv : ftau⁻¹ = ftau := inv_eq_of_mul_eq_one_right hftau2
      have hkey : (q * ftau) * ftau * (q * ftau)⁻¹ = q * (ftau * ftau) * (q * ftau)⁻¹ := by
        group
      rw [hkey, hftau2, mul_one, mul_inv_rev, hfinv]
      group
  · let w : Pm := wordP (outerL.getD a.val [])
    have hwP : w ∈ QP.originalSubgroup := by dsimp only [w]; exact wordP_mem _
    have hwspec : w * ftau * w⁻¹ = g' := by
      dsimp only [w]
      rw [outerL_spec a]
      exact hg'.symm
    let q : Pm := c₀⁻¹ * w
    have hqA : q ∈ QA.originalSubgroup :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₀A) (P_le_A hwP)
    have hqeq : q * ftau * q⁻¹ = g := by
      have h1 : g = c₀⁻¹ * g' * c₀ := by rw [hg'def]; group
      rw [h1, ← hwspec]
      dsimp only [q]
      group
    rcases mem_A_cases q hqA with hqP | hqp
    · exact ⟨q, hqP, hqeq⟩
    · refine ⟨q * ftau, hqp, ?_⟩
      rw [← hqeq]
      have hftau2 : ftau * ftau = 1 := by rw [← pow_two]; exact ftau_pow.1
      have hfinv : ftau⁻¹ = ftau := inv_eq_of_mul_eq_one_right hftau2
      have hkey : (q * ftau) * ftau * (q * ftau)⁻¹ = q * (ftau * ftau) * (q * ftau)⁻¹ := by
        group
      rw [hkey, hftau2, mul_one, mul_inv_rev, hfinv]
      group

end Classes

end CFSG.OddStandard.SmallF3.HarrisU33.K28
