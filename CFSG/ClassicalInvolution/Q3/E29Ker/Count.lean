module

public import CFSG.ClassicalInvolution.Q3.E29Ker.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.E29Ker

open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E29Data

variable {X : Type} [Group X] {φ : X →* AEQ 8} {Q : Set (Subgroup X)}

private theorem ct_e29Sets_ncard : e29Sets.ncard ≤ 14 := by
  have hsub : e29Sets ⊆ ↑(affinePlanes.toFinset) := by
    intro α hα
    exact Finset.mem_coe.mpr (List.mem_toFinset.mpr hα)
  calc e29Sets.ncard
      ≤ (↑(affinePlanes.toFinset) : Set (Finset (Fin 8))).ncard := Set.ncard_le_ncard hsub
    _ = affinePlanes.toFinset.card := Set.ncard_coe_finset _
    _ ≤ affinePlanes.length := List.toFinset_card_le _
    _ = 14 := by simp [affinePlanes]

private noncomputable def ct_memBarOf (p : Finset (Fin 8) × Bool) : Subgroup (AEQ 8) :=
  if h : p.1.card = 4 then memBar p.1 h p.2 else ⊥

private theorem ct_memBarOf_mk {α : Finset (Fin 8)} (h : α.card = 4) (b : Bool) :
    ct_memBarOf (α, b) = memBar α h b := by
  unfold ct_memBarOf
  exact dif_pos h

private theorem ct_univ_bool : (Set.univ : Set Bool).ncard = 2 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool]

private theorem ct_members_subset :
    {M : Subgroup (AEQ 8) | ∃ α ∈ e29Sets, ∃ (h : α.card = 4) (b : Bool), M = memBar α h b} ⊆
      ct_memBarOf '' (e29Sets ×ˢ Set.univ) := by
  rintro M ⟨α, hα, h, b, rfl⟩
  exact ⟨(α, b), ⟨hα, Set.mem_univ _⟩, ct_memBarOf_mk h b⟩

private theorem ct_members_finite :
    {M : Subgroup (AEQ 8) | ∃ α ∈ e29Sets, ∃ (h : α.card = 4) (b : Bool), M = memBar α h b}.Finite :=
  Set.Finite.subset (Set.Finite.image ct_memBarOf (Set.toFinite _)) ct_members_subset

theorem ncard_members_le : {M : Subgroup (AEQ 8) | ∃ α ∈ e29Sets, ∃ (h : α.card = 4) (b : Bool),
    M = memBar α h b}.ncard ≤ 28 := by
  calc _ ≤ (ct_memBarOf '' (e29Sets ×ˢ Set.univ)).ncard :=
        Set.ncard_le_ncard ct_members_subset (Set.Finite.image ct_memBarOf (Set.toFinite _))
    _ ≤ (e29Sets ×ˢ Set.univ).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = e29Sets.ncard * (Set.univ : Set Bool).ncard := Set.ncard_prod
    _ ≤ 14 * 2 := Nat.mul_le_mul ct_e29Sets_ncard ct_univ_bool.le
    _ = 28 := by norm_num

namespace Lab

variable (F : Lab φ Q)

private theorem ct_map_ne (H : Hyp φ Q) {j k : ℕ} (hj : j < 28)
    (hk : k < 28) (hne : j ≠ k) : (F.L j).map φ ≠ (F.L k).map φ := by
  intro heq
  have hx0 : F.gen (2 * j) ∈ F.L j := by
    simpa using F.gen_mem_L j (show (0 : ℕ) < 2 by norm_num)
  have hx : φ (F.gen (2 * j)) ∈ (F.L k).map φ := by
    rw [← heq]
    exact Subgroup.mem_map_of_mem φ hx0
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  obtain ⟨W, hW, rfl⟩ := F.mem_L H hk hy
  have hWl : ∀ l ∈ W, l < 2 := localWords29_lt W hW
  have hjl : 2 * j < 56 := by omega
  rw [F.phi_ev hk hWl, F.phi_gen hjl] at hyx
  exact distinct_ne hj hk hne W hW hyx.symm

theorem exists_L (H : Hyp φ Q) {L : Subgroup X} (hL : L ∈ Q) :
    ∃ j < 28, L = F.L j := by
  have hinj : Set.InjOn (fun j : ℕ => (F.L j).map φ) (Finset.range 28 : Set ℕ) := by
    intro j hj k hk hjk
    by_contra hne
    exact F.ct_map_ne H (Finset.mem_range.mp (Finset.mem_coe.mp hj))
      (Finset.mem_range.mp (Finset.mem_coe.mp hk)) hne hjk
  have hTS : (fun j : ℕ => (F.L j).map φ) '' (Finset.range 28 : Set ℕ) ⊆
      {M : Subgroup (AEQ 8) | ∃ α ∈ e29Sets, ∃ (h : α.card = 4) (b : Bool), M = memBar α h b} := by
    rintro _ ⟨j, -, rfl⟩
    obtain ⟨α, hα, h, b, hjα⟩ := H.lab _ (F.L_mem_Q H j)
    exact ⟨α, hα, h, b, hjα⟩
  have hT : ((fun j : ℕ => (F.L j).map φ) '' (Finset.range 28 : Set ℕ)).ncard = 28 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
  have hST : {M : Subgroup (AEQ 8) | ∃ α ∈ e29Sets, ∃ (h : α.card = 4) (b : Bool),
      M = memBar α h b} = (fun j : ℕ => (F.L j).map φ) '' (Finset.range 28 : Set ℕ) :=
    (Set.eq_of_subset_of_ncard_le hTS (by rw [hT]; exact ncard_members_le)
      ct_members_finite).symm
  obtain ⟨α, hα, h, b, hLα⟩ := H.lab L hL
  have hLS : L.map φ ∈ {M : Subgroup (AEQ 8) | ∃ α ∈ e29Sets, ∃ (h : α.card = 4) (b : Bool),
      M = memBar α h b} := ⟨α, hα, h, b, hLα⟩
  rw [hST] at hLS
  obtain ⟨j, hj, hjL⟩ := hLS
  exact ⟨j, Finset.mem_range.mp (Finset.mem_coe.mp hj),
    (H.inj _ (F.L_mem_Q H j) L hL hjL).symm⟩

theorem le_closure_gen (H : Hyp φ Q) {L : Subgroup X}
    (hL : L ∈ Q) : L ≤ Subgroup.closure (F.gen '' Set.Iio 56) := by
  obtain ⟨j, hj, rfl⟩ := F.exists_L H hL
  rintro x hx
  obtain ⟨W, hW, rfl⟩ := F.mem_L H hj hx
  unfold Lab.ev
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
  have hl2 : l < 2 := localWords29_lt W hW l hl
  have hlt : 2 * j + l < 56 := by omega
  exact Subgroup.subset_closure (Set.mem_image_of_mem F.gen (Set.mem_Iio.mpr hlt))

end Lab

end CFSG.ClassicalInvolution.Q3.E29Ker
