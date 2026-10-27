module

public import CFSG.ClassicalInvolution.Q3.E64Ker.Frame
public import CFSG.ClassicalInvolution.Q3.E64Ker.Generic

public section

namespace CFSG.ClassicalInvolution.Q3.E64Ker

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E64Data

variable {X : Type} [Group X] {φ : X →* AEQ 7} {Q : Set (Subgroup X)}

namespace Lab

variable (F : Lab φ Q)

private theorem el_phi_K1 (H : Hyp φ Q) {x : X}
    (hx : x ∈ F.K1) : ∃ W ∈ localWords, φ x = mkQ 7 (mWord 0 W) := by
  have hx0 : x ∈ F.L 0 := by rw [F.L_zero]; exact hx
  obtain ⟨W, hW, rfl⟩ := F.mem_L H (by norm_num) hx0
  exact ⟨W, hW, F.phi_ev (by norm_num) (localWords_lt W hW)⟩

private theorem el_mkQ_mem_L (j : ℕ) (hj : j < 14) {W : List ℕ} (hW : ∀ l ∈ W, l < 2) :
    mkQ 7 (mWord j W) ∈ (F.L j).map φ := by
  rw [← F.phi_ev hj hW]
  exact Subgroup.mem_map_of_mem φ (F.ev_mem_L j hW)

private theorem el_mkQ_mem_K1 {W : List ℕ} (hW : ∀ l ∈ W, l < 2) :
    mkQ 7 (mWord 0 W) ∈ F.K1.map φ := by
  have h := el_mkQ_mem_L F 0 (by norm_num) hW
  rwa [F.L_zero] at h

private theorem el_ev_mem_closure {S : Set X} (j : ℕ) {W : List ℕ} (hW : ∀ l ∈ W, l < 2)
    (hS : ∀ l < 2, F.gen (2 * j + l) ∈ S) : F.ev j W ∈ Subgroup.closure S := by
  unfold Lab.ev
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
  exact Subgroup.subset_closure (hS l (hW l hl))

private theorem el_L_le_closure (H : Hyp φ Q) {j : ℕ}
    (hj : j < 14) : F.L j ≤ Subgroup.closure {F.gen (2 * j), F.gen (2 * j + 1)} := by
  intro x hx
  obtain ⟨W, hW, rfl⟩ := F.mem_L H hj hx
  refine el_ev_mem_closure F j (localWords_lt W hW) fun l hl => ?_
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private theorem el_K1_le_closure (H : Hyp φ Q) :
    F.K1 ≤ Subgroup.closure {F.a, F.b} := by
  intro x hx
  have hx0 : x ∈ F.L 0 := by rw [F.L_zero]; exact hx
  obtain ⟨W, hW, rfl⟩ := F.mem_L H (by norm_num) hx0
  refine el_ev_mem_closure F 0 (localWords_lt W hW) fun l hl => ?_
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · show F.gen 0 ∈ ({F.a, F.b} : Set X)
    rw [F.gen_zero]
    exact Set.mem_insert _ _
  · show F.gen 1 ∈ ({F.a, F.b} : Set X)
    rw [F.gen_one]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private theorem el_phi_z1 : φ F.z1 = mkQ 7 (mA * mA) := by
  show φ (F.a * F.a) = mkQ 7 (mA * mA)
  rw [map_mul, F.phi_a, ← map_mul]

private theorem el_phi_zj :
    φ (F.zj e64JStar) = mkQ 7 (mA * mA) := by
  have h4 : 2 * e64JStar < 28 := by decide
  rw [F.zj_eq_sq, map_mul, F.phi_gen h4, ← map_mul, partner_facts.2.2]

private theorem el_z1_mem : F.z1 ∈ F.K1 := F.K1.mul_mem F.a_mem F.a_mem

private theorem el_pow_four_K1 (H : Hyp φ Q) {x : X}
    (hx : x ∈ F.K1) : x ^ 4 = 1 := by
  obtain ⟨W, hW, hφx⟩ := el_phi_K1 F H hx
  have hw4 : mWord 0 W ^ 4 = 1 := by
    rw [show mWord 0 W ^ 4 = mWord 0 W * mWord 0 W * mWord 0 W * mWord 0 W by
      simp only [pow_succ, pow_zero, one_mul]]
    exact local_pow_four W hW
  apply H.injOn F.mem_Q (F.K1.pow_mem hx 4) F.K1.one_mem
  rw [map_pow, hφx, map_one, ← map_pow, hw4, map_one]

private theorem el_z1_ne_one : F.z1 ≠ 1 := by
  intro h1
  have h3 : mkQ 7 (mA * mA) = mkQ 7 1 := by
    rw [← el_phi_z1 F, h1, map_one, map_one]
  exact mA_sq_ne_one (mkQ7_inj ((aeSub 7).mul_mem mA_mem mA_mem) ((aeSub 7).one_mem) h3)

private theorem el_z1_sq (H : Hyp φ Q) : F.z1 * F.z1 = 1 := by
  have h4 : F.a ^ 4 = F.z1 * F.z1 := by
    show F.a ^ 4 = F.a * F.a * (F.a * F.a)
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [← h4]
  exact el_pow_four_K1 F H F.a_mem

private theorem el_z1_unique (H : Hyp φ Q) :
    ∀ y ∈ F.K1, y * y = 1 → y = 1 ∨ y = F.z1 := by
  intro y hy hyy
  obtain ⟨W, hW, hφy⟩ := el_phi_K1 F H hy
  have hwmem : mWord 0 W ∈ aeSub 7 := mWord_mem (by norm_num) (localWords_lt W hW)
  have hsq : mWord 0 W * mWord 0 W = 1 := by
    have h1 : φ (y * y) = φ 1 := by rw [hyy]
    rw [map_mul, hφy, map_one, ← map_mul] at h1
    exact mkQ7_inj ((aeSub 7).mul_mem hwmem hwmem) ((aeSub 7).one_mem)
      (h1.trans (map_one (mkQ 7)).symm)
  rcases local_sq_eq_one W hW hsq with h | h
  · left
    apply H.injOn F.mem_Q hy F.K1.one_mem
    rw [hφy, h, map_one, map_one]
  · right
    apply H.injOn F.mem_Q hy (el_z1_mem F)
    rw [hφy, el_phi_z1 F, h]

theorem isUniqueInvolution_K1 (H : Hyp φ Q) :
    IsUniqueInvolution F.K1 F.z1 :=
  ⟨el_z1_mem F, el_z1_ne_one F, el_z1_sq F H, el_z1_unique F H⟩

theorem pow_four_K1 (H : Hyp φ Q) :
    ∀ k ∈ F.K1, k ^ 4 = 1 :=
  fun _ hk => el_pow_four_K1 F H hk

theorem central_K1 (H : Hyp φ Q) :
    ∀ k ∈ F.K1, k * F.z1 = F.z1 * k := by
  intro k hk
  obtain ⟨W, hW, hφk⟩ := el_phi_K1 F H hk
  apply H.injOn F.mem_Q (F.K1.mul_mem hk (el_z1_mem F)) (F.K1.mul_mem (el_z1_mem F) hk)
  rw [map_mul, map_mul, hφk, el_phi_z1 F, ← map_mul, ← map_mul, local_central W hW]

theorem isUniqueInvolution_L (H : Hyp φ Q) (j : ℕ) :
    IsUniqueInvolution (F.L j) (F.zj j) :=
  (F.isUniqueInvolution_K1 H).conj (F.T j)

theorem pow_four_L (H : Hyp φ Q) (j : ℕ) :
    ∀ k ∈ F.L j, k ^ 4 = 1 := by
  intro k hk
  obtain ⟨k', hk', rfl⟩ : ∃ k' ∈ F.K1, k = F.T j * k' * (F.T j)⁻¹ :=
    ⟨(F.T j)⁻¹ * k * F.T j, mem_conjSub_iff.mp hk, by group⟩
  rw [conj_pow, el_pow_four_K1 F H hk', mul_one, mul_inv_cancel]

theorem central_L (H : Hyp φ Q) (j : ℕ) :
    ∀ k ∈ F.L j, k * F.zj j = F.zj j * k := by
  intro k hk
  obtain ⟨k', hk', rfl⟩ : ∃ k' ∈ F.K1, k = F.T j * k' * (F.T j)⁻¹ :=
    ⟨(F.T j)⁻¹ * k * F.T j, mem_conjSub_iff.mp hk, by group⟩
  have hc : k' * F.z1 = F.z1 * k' := F.central_K1 H k' hk'
  show F.T j * k' * (F.T j)⁻¹ * (F.T j * F.z1 * (F.T j)⁻¹) =
    F.T j * F.z1 * (F.T j)⁻¹ * (F.T j * k' * (F.T j)⁻¹)
  calc F.T j * k' * (F.T j)⁻¹ * (F.T j * F.z1 * (F.T j)⁻¹)
      = F.T j * (k' * F.z1) * (F.T j)⁻¹ := by group
    _ = F.T j * (F.z1 * k') * (F.T j)⁻¹ := by rw [hc]
    _ = F.T j * F.z1 * (F.T j)⁻¹ * (F.T j * k' * (F.T j)⁻¹) := by group

theorem n0_mem_ker (H : Hyp φ Q) : F.n0 ∈ φ.ker := by
  rw [MonoidHom.mem_ker]
  show φ (F.z1⁻¹ * F.zj e64JStar) = 1
  rw [map_mul, map_inv, el_phi_z1 F, el_phi_zj F, inv_mul_cancel]

theorem exists_y [Finite X] (H : Hyp φ Q) :
    ∃ y : X, (∃ n : ℕ, y ^ 3 ^ n = 1) ∧
      (∀ k ∈ F.K1, y * k * y⁻¹ ∈ F.K1) ∧ (∃ k ∈ F.K1, y * k ≠ k * y) ∧
      (∀ k ∈ F.L e64JStar, y * k * y⁻¹ ∈ F.L e64JStar) ∧
      (∃ k ∈ F.L e64JStar, y * k ≠ k * y) := by
  obtain ⟨hY3, hsub, hrow, hnc0, hnc1⟩ := y3_facts
  have hcube : mkQ 7 mY3 ^ 3 = 1 := by
    rw [pow_three', ← map_mul, ← map_mul, hY3, map_one]
  have hmem : mkQ 7 mY3 ∈ φ.range := by
    rw [H.range_eq]
    exact Subgroup.mem_map_of_mem (mkQ 7) hsub
  obtain ⟨y, hφy, n, hyn⟩ := exists_three_lift φ hcube hmem
  have hY3aeSub : mY3 ∈ aeSub 7 := (Subgroup.mem_inf.mp hsub).1
  have hG2 : mG (2 * e64JStar) ∈ aeSub 7 := mG_mem (by decide)
  have hconj : ∀ x : X, ∀ g : Wr 7, φ x = mkQ 7 g →
      φ (y * x * y⁻¹) = mkQ 7 (mY3 * g * mY3⁻¹) := by
    intro x g hx
    simp only [map_mul, map_inv, hφy, hx]
  have e1 : mY3 * mA * mY3⁻¹ = mWord 0 [1] := by
    have h : mY3 * mG (2 * 0 + 0) * mY3⁻¹ = mWord 0 [1] :=
      hrow (0, 0, [1]) (by simp [e64Y3Rows])
    have hA : mG (2 * 0 + 0) = mA := mG_zero
    rw [hA] at h
    exact h
  have e2 : mY3 * mB * mY3⁻¹ = mWord 0 [1, 0, 0, 0] := by
    have h : mY3 * mG (2 * 0 + 1) * mY3⁻¹ = mWord 0 [1, 0, 0, 0] :=
      hrow (0, 1, [1, 0, 0, 0]) (by simp [e64Y3Rows])
    have hB : mG (2 * 0 + 1) = mB := mG_one
    rw [hB] at h
    exact h
  have e3 : mY3 * mG (2 * e64JStar) * mY3⁻¹ = mWord e64JStar [1, 0, 0, 0] :=
    hrow (e64JStar, 0, [1, 0, 0, 0]) (by simp [e64Y3Rows])
  have e4 : mY3 * mG (2 * e64JStar + 1) * mY3⁻¹ = mWord e64JStar [0] :=
    hrow (e64JStar, 1, [0]) (by simp [e64Y3Rows])
  have hK1 : conjSub y F.K1 = F.K1 := by
    refine H.conjSub_eq_of_gen F.mem_Q F.mem_Q (el_K1_le_closure F H) ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [hconj F.a mA F.phi_a, e1]
      exact el_mkQ_mem_K1 F (by decide)
    · rw [hconj F.b mB F.phi_b, e2]
      exact el_mkQ_mem_K1 F (by decide)
  have hLj : e64JStar < 14 := partner_facts.1
  have hL : conjSub y (F.L e64JStar) = F.L e64JStar := by
    refine H.conjSub_eq_of_gen (F.L_mem_Q H e64JStar) (F.L_mem_Q H e64JStar)
      (el_L_le_closure F H hLj) ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [hconj _ _ (F.phi_gen (by decide : 2 * e64JStar < 28)), e3]
      exact el_mkQ_mem_L F e64JStar hLj (by decide)
    · rw [hconj _ _ (F.phi_gen (by decide : 2 * e64JStar + 1 < 28)), e4]
      exact el_mkQ_mem_L F e64JStar hLj (by decide)
  refine ⟨y, ⟨n, hyn⟩, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h := conj_mem_conjSub (n := y) hk
    rwa [hK1] at h
  · refine ⟨F.a, F.a_mem, fun h => ?_⟩
    have h1 : φ (y * F.a) = φ (F.a * y) := congrArg φ h
    rw [map_mul, map_mul, hφy, F.phi_a, ← map_mul, ← map_mul] at h1
    exact hnc0 (mkQ7_inj ((aeSub 7).mul_mem hY3aeSub mA_mem)
      ((aeSub 7).mul_mem mA_mem hY3aeSub) h1)
  · intro k hk
    have h := conj_mem_conjSub (n := y) hk
    rwa [hL] at h
  · have hk : F.gen (2 * e64JStar) ∈ F.L e64JStar :=
      F.gen_mem_L e64JStar (by norm_num : (0 : ℕ) < 2)
    refine ⟨F.gen (2 * e64JStar), hk, fun h => ?_⟩
    have h1 : φ (y * F.gen (2 * e64JStar)) = φ (F.gen (2 * e64JStar) * y) := congrArg φ h
    rw [map_mul, map_mul, hφy, F.phi_gen (by decide : 2 * e64JStar < 28), ← map_mul,
      ← map_mul] at h1
    exact hnc1 (mkQ7_inj ((aeSub 7).mul_mem hY3aeSub hG2)
      ((aeSub 7).mul_mem hG2 hY3aeSub) h1)

end Lab

end CFSG.ClassicalInvolution.Q3.E64Ker
