module

public import CFSG.ClassicalInvolution.Q3.E29Ker.Frame
public import CFSG.ClassicalInvolution.Q3.E64Ker.Generic

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data

variable {X : Type} [Group X] {φ : X →* AEQ 8} {Q : Set (Subgroup X)}

namespace Lab

variable (F : Lab φ Q)

private theorem el_lt28 {k : ℕ} (hk : k ∈ 0 :: e29Partners) :
    k < 28 := by
  rcases List.mem_cons.mp hk with rfl | hp
  · norm_num
  · exact (partner_facts k hp).1

private theorem el_phi_K1 (H : Hyp φ Q) {x : X}
    (hx : x ∈ F.K1) : ∃ W ∈ localWords29, φ x = mkQ 8 (nWord 0 W) := by
  have hx0 : x ∈ F.L 0 := by rw [F.L_zero]; exact hx
  obtain ⟨W, hW, rfl⟩ := F.mem_L H (by norm_num) hx0
  exact ⟨W, hW, F.phi_ev (by norm_num) (localWords29_lt W hW)⟩

private theorem el_mkQ_mem_L {j : ℕ} (hj : j < 28) {W : List ℕ} (hW : ∀ l ∈ W, l < 2) :
    mkQ 8 (nWord j W) ∈ (F.L j).map φ := by
  rw [← F.phi_ev hj hW]
  exact Subgroup.mem_map_of_mem φ (F.ev_mem_L j hW)

private theorem el_ev_mem_closure {S : Set X} (j : ℕ) {W : List ℕ} (hW : ∀ l ∈ W, l < 2)
    (hS : ∀ l < 2, F.gen (2 * j + l) ∈ S) : F.ev j W ∈ Subgroup.closure S := by
  unfold Lab.ev
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
  exact Subgroup.subset_closure (hS l (hW l hl))

private theorem el_L_le_closure (H : Hyp φ Q) {j : ℕ}
    (hj : j < 28) : F.L j ≤ Subgroup.closure {F.gen (2 * j), F.gen (2 * j + 1)} := by
  intro x hx
  obtain ⟨W, hW, rfl⟩ := F.mem_L H hj hx
  refine el_ev_mem_closure F j (localWords29_lt W hW) fun l hl => ?_
  rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private theorem el_phi_z1 : φ F.z1 = mkQ 8 nA * mkQ 8 nA := by
  show φ (F.a * F.a) = mkQ 8 nA * mkQ 8 nA
  rw [map_mul, F.phi_a]

private theorem el_phi_zj {p : ℕ} (hp : p < 28)
    (hpsq : mkQ 8 (nG (2 * p)) * mkQ 8 (nG (2 * p)) = mkQ 8 nA * mkQ 8 nA) :
    φ (F.zj p) = mkQ 8 nA * mkQ 8 nA := by
  rw [F.zj_eq_sq, map_mul, F.phi_gen (by omega : 2 * p < 56)]
  exact hpsq

private theorem el_z1_mem : F.z1 ∈ F.K1 := F.K1.mul_mem F.a_mem F.a_mem

private theorem el_z1_ne_one : F.z1 ≠ 1 := by
  intro h1
  have h2 : φ F.z1 = 1 := by rw [h1, map_one]
  rw [el_phi_z1 F] at h2
  exact nA_sq_ne_one h2

private theorem el_pow_four_K1 (H : Hyp φ Q) {x : X}
    (hx : x ∈ F.K1) : x ^ 4 = 1 := by
  obtain ⟨W, hW, hφx⟩ := el_phi_K1 F H hx
  have hw4 : mkQ 8 (nWord 0 W) ^ 4 = 1 := by
    rw [show mkQ 8 (nWord 0 W) ^ 4 = mkQ 8 (nWord 0 W) * mkQ 8 (nWord 0 W) * mkQ 8 (nWord 0 W) *
      mkQ 8 (nWord 0 W) by simp only [pow_succ, pow_zero, one_mul]]
    exact local_pow_four W hW
  apply H.injOn F.mem_Q (F.K1.pow_mem hx 4) F.K1.one_mem
  rw [map_pow, hφx, map_one]
  exact hw4

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
  have hsq : mkQ 8 (nWord 0 W) * mkQ 8 (nWord 0 W) = 1 := by
    rw [← hφy, ← map_mul, hyy, map_one]
  rcases local_sq_eq_one W hW hsq with h | h
  · left
    apply H.injOn F.mem_Q hy F.K1.one_mem
    rw [hφy, h, map_one]
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
  rw [map_mul, map_mul, hφk, el_phi_z1 F]
  exact local_central W hW

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

theorem np_mem_ker (H : Hyp φ Q) {p : ℕ}
    (hp : p ∈ e29Partners) : F.np p ∈ φ.ker := by
  obtain ⟨hp28, -, hpsq⟩ := partner_facts p hp
  rw [MonoidHom.mem_ker]
  show φ ((F.z1)⁻¹ * F.zj p) = 1
  rw [map_mul, map_inv, el_phi_z1 F, el_phi_zj F hp28 hpsq, inv_mul_cancel]

theorem exists_y [Finite X] (H : Hyp φ Q) :
    ∃ y : X, (∃ n : ℕ, y ^ 3 ^ n = 1) ∧ ∀ k ∈ 0 :: e29Partners,
      (∀ x ∈ F.L k, y * x * y⁻¹ ∈ F.L k) ∧ ∃ x ∈ F.L k, y * x ≠ x * y := by
  obtain ⟨hY3, hsub, hrow, hnc⟩ := y3_facts
  have hcube : mkQ 8 nY3 ^ 3 = 1 := by
    rw [pow_three', ← map_mul, ← map_mul, hY3, map_one]
  have hmem : mkQ 8 nY3 ∈ φ.range := by
    rw [H.range_eq]
    exact Subgroup.mem_map_of_mem (mkQ 8) hsub
  obtain ⟨y, hφy, n, hyn⟩ :=
    CFSG.ClassicalInvolution.Q3.E64Ker.exists_three_lift φ hcube hmem
  have hconj : ∀ (x : X) (g : Wr 8), φ x = mkQ 8 g →
      φ (y * x * y⁻¹) = mkQ 8 nY3 * mkQ 8 g * (mkQ 8 nY3)⁻¹ := by
    intro x g hx
    rw [map_mul, map_mul, map_inv, hφy, hx]
  have hgen : ∀ k ∈ 0 :: e29Partners, ∀ t < 2,
      φ (y * F.gen (2 * k + t) * y⁻¹) ∈ (F.L k).map φ := by
    intro k hk t ht
    obtain ⟨r, hr, hr1, hr2⟩ := y3Rows_complete k hk t ht
    have hx := hrow r hr
    rw [hr1, hr2] at hx
    rw [hconj _ _ (F.phi_gen (by have := el_lt28 hk; omega : 2 * k + t < 56)), hx]
    exact el_mkQ_mem_L F (el_lt28 hk) ((y3Rows_bounds r hr).2.2)
  have hnorm : ∀ k ∈ 0 :: e29Partners, conjSub y (F.L k) = F.L k := by
    intro k hk
    refine H.conjSub_eq_of_gen (F.L_mem_Q H k) (F.L_mem_Q H k)
      (el_L_le_closure F H (el_lt28 hk)) ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · have h0 := hgen k hk 0 (by norm_num)
      rwa [add_zero] at h0
    · exact hgen k hk 1 (by norm_num)
  refine ⟨y, ⟨n, hyn⟩, fun k hk => ⟨fun x hx => ?_, ?_⟩⟩
  · have h := conj_mem_conjSub (n := y) hx
    rwa [hnorm k hk] at h
  · refine ⟨F.gen (2 * k), ?_, fun h => ?_⟩
    · have h0 := F.gen_mem_L k (l := 0) (by norm_num)
      rwa [add_zero] at h0
    · have h1 : φ (y * F.gen (2 * k)) = φ (F.gen (2 * k) * y) := congrArg φ h
      rw [map_mul, map_mul, hφy, F.phi_gen (by have := el_lt28 hk; omega : 2 * k < 56)] at h1
      exact hnc k hk h1

end Lab

end CFSG.ClassicalInvolution.Q3.E29Ker
