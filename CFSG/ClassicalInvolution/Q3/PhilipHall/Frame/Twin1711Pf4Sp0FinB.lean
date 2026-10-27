module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0FinA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0RowsAll

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

set_option linter.unusedSectionVars false


theorem card_TT : Nat.card ↥(Sp0Core.TT r2H) = 4608 := by
  obtain ⟨h1, h2, -⟩ := sp6_cent_spec₂
  have h3 : Nat.card ↥(centralizerIn co3X36 sp6Rep2) = 4608 := by
    rw [← sp6Q_originalSubgroup, h1]
    exact h2
  have hle : centralizerIn co3X36 sp6Rep2 ≤ co3X36 := inf_le_left
  have hT : Sp0Core.TT r2H = (centralizerIn co3X36 sp6Rep2).subgroupOf co3X36 := by
    ext x
    have hr : (r2H : Equiv.Perm (Fin 36)) = sp6Rep2 := tab_eq _
    rw [mem_TT_iff, Subgroup.mem_subgroupOf, centralizerIn, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨x.2, ?_⟩
      have h' : (x : Equiv.Perm (Fin 36)) * (r2H : Equiv.Perm (Fin 36)) = r2H * x :=
        congrArg Subtype.val h
      rwa [hr] at h'
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show (x : Equiv.Perm (Fin 36)) * (r2H : Equiv.Perm (Fin 36)) =
        (r2H : Equiv.Perm (Fin 36)) * x
      rwa [hr]
  rw [hT, ← h3]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

@[expose] def elt (r : List ℕ) : ModSp0 := hm (r.drop 4)

theorem rowsAll_sound :
    (∀ r ∈ rowsAll, rowChk r = true) ∧ (rowsAll.map rowVal).Pairwise (· < ·) :=
  let h := chk_sound rowsAll 0 rowsAll_chk
  ⟨h.1, h.2.1⟩

theorem elt_mem_TT {r : List ℕ} (hr : r ∈ rowsAll) : elt r ∈ Sp0Core.TT r2H :=
  hm_mem_TT (rowChk_sound prep_base invChk_true badChk_true (rowsAll_sound.1 r hr)).1

theorem nodup_elts : (rowsAll.map elt).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  have h := rowsAll_sound.2
  rw [List.pairwise_map] at h
  refine h.imp ?_
  intro a b hab heq
  have h1 := prepW (a.drop 4)
  have h2 := prepW (b.drop 4)
  have h3 : permW (LG GB) (a.drop 4) = permW (LG GB) (b.drop 4) := congrArg Subtype.val heq
  rw [h3] at h1
  have := h1.inj h2
  exact absurd this (ne_of_lt hab)

theorem exists_row {g : ModSp0} (hg : g ∈ Sp0Core.TT r2H) : ∃ r ∈ rowsAll, elt r = g := by
  by_contra hne
  push Not at hne
  classical
  have : Fintype ModSp0 := Fintype.ofFinite _
  have hcard : (rowsAll.map elt).toFinset.card = 4608 := by
    rw [List.toFinset_card_of_nodup nodup_elts, List.length_map, rowsAll_length]
  have hnot : g ∉ (rowsAll.map elt).toFinset := by
    intro h
    obtain ⟨r, hr, hrg⟩ := List.mem_map.1 (List.mem_toFinset.1 h)
    exact hne r hr hrg
  have hsub : insert g (rowsAll.map elt).toFinset ⊆
      (Finset.univ : Finset ModSp0).filter (fun x => x ∈ Sp0Core.TT r2H) := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using hg
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      simpa using elt_mem_TT hr
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, hcard] at h1
  have h2 : ((Finset.univ : Finset ModSp0).filter (fun x => x ∈ Sp0Core.TT r2H)).card = 4608 := by
    rw [← card_TT, Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem getD_mem_or {α : Type} (l : List α) (n : ℕ) (d : α) : l.getD n d = d ∨ l.getD n d ∈ l := by
  by_cases h : n < l.length
  · right
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · left
    exact getD_default' _ _ _ (by omega)

theorem egWords_mem_EE {e : ℕ} (he : e < 4) : hm (egWords.getD e []) ∈ Sp0Core.EE K0H r2H := by
  have h4 : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact hm_mem_EE_K0 (w := [12]) (by simp)
  · exact hm_mem_EE_K0 (w := [13]) (by simp)
  · exact hm_conj_mem_EE (w := [12]) (by simp)
  · exact hm_conj_mem_EE (w := [13]) (by simp)

theorem r2H_mem_EE : r2H ∈ Sp0Core.EE K0H r2H := by
  have h := hm_mem_EE_K0 (w := [12, 12]) (by simp)
  rw [← r2H_eq] at h
  exact h

theorem centE_bound : Nat.card ↥(Subgroup.centralizer (Sp0Core.EE K0H r2H : Set ModSp0)) ≤ 8 := by
  classical
  set C := Subgroup.centralizer (Sp0Core.EE K0H r2H : Set ModSp0) with hC
  have hmem : ∀ g ∈ C, ∃ r ∈ rowsAll.filter (fun r => decide (4 ≤ r.getD 0 0)), elt r = g := by
    intro g hg
    have hcomm : ∀ y ∈ Sp0Core.EE K0H r2H, y * g = g * y := fun y hy =>
      Subgroup.mem_centralizer_iff.1 hg y hy
    have hgT : g ∈ Sp0Core.TT r2H := by
      rw [mem_TT_iff]
      exact (hcomm _ r2H_mem_EE).symm
    obtain ⟨r, hr, hrg⟩ := exists_row hgT
    refine ⟨r, List.mem_filter.2 ⟨hr, ?_⟩, hrg⟩
    by_contra hlt
    have hlt' : r.getD 0 0 < 4 := by simpa using hlt
    have hs := (rowChk_sound prep_base invChk_true badChk_true (rowsAll_sound.1 r hr)).2.1 hlt'
    apply hs
    have h1 := hcomm _ (egWords_mem_EE hlt')
    have h2 := congrArg Subtype.val h1
    rw [← hrg] at h2
    exact h2.symm
  have hsub : (C : Set ModSp0) ⊆ ↑((rowsAll.filter (fun r => decide (4 ≤ r.getD 0 0))).map elt).toFinset := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := hmem g hg
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact List.mem_map_of_mem hr
  calc Nat.card ↥C = (C : Set ModSp0).ncard := (Nat.card_coe_set_eq _)
    _ ≤ (((rowsAll.filter (fun r => decide (4 ≤ r.getD 0 0))).map elt).toFinset : Set ModSp0).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((rowsAll.filter (fun r => decide (4 ≤ r.getD 0 0))).map elt).toFinset.card :=
        Set.ncard_coe_finset _
    _ ≤ ((rowsAll.filter (fun r => decide (4 ≤ r.getD 0 0))).map elt).length :=
        List.toFinset_card_le _
    _ = 8 := by
        rw [List.length_map]
        exact rowsAll_cntE

theorem Ywords_letters : ∀ w ∈ Ywords, ∀ l ∈ w, 4 ≤ l ∧ l ≤ 15 := by
  intro w hw l hl
  simp only [Ywords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl <;> simp at hl <;> omega

theorem hm_getD_Y_mem (y : ℕ) : hm (Ywords.getD y []) ∈ Sp0Core.TT r2H := by
  rcases getD_mem_or Ywords y [] with h | h
  · rw [h]; exact hm_mem_TT (by simp)
  · exact hm_mem_TT (Ywords_letters _ h)

theorem hm_getD_L0_mem (i : ℕ) : hm (L0w.getD i []) ∈ Sp0Core.EE K0H r2H := by
  rcases getD_mem_or L0w i [] with h | h
  · rw [h]; exact hm_mem_EE_K0 (by simp)
  · exact hm_mem_EE_K0 (L0w_letters _ h)

theorem hm_getD_L1_mem (i : ℕ) : hm (L1w.getD i []) ∈ Sp0Core.EE K0H r2H := by
  rcases getD_mem_or L1w i [] with h | h
  · rw [h]; exact hm_mem_EE_K0 (by simp)
  · obtain ⟨w, hw, hwe⟩ := List.mem_map.1 h
    rw [← hwe]
    exact hm_conj_mem_EE (L0w_letters _ hw)

theorem index_big (N : Subgroup ModSp0) (hE : Sp0Core.EE K0H r2H ≤ N) (hN : N ≤ Sp0Core.TT r2H)
    (hnorm : (N.subgroupOf (Sp0Core.TT r2H)).Normal)
    (hinv : ∀ x : ModSp0, x * r2H * x⁻¹ ∈ N → x * r2H * x⁻¹ = r2H) :
    8 < N.relIndex (Sp0Core.TT r2H) := by
  classical
  have hmem : ∀ g ∈ N, ∃ r ∈ rowsAll.filter (fun r => decide (3 ≤ r.getD 1 0)), elt r = g := by
    intro g hg
    obtain ⟨r, hr, hrg⟩ := exists_row (hN hg)
    refine ⟨r, List.mem_filter.2 ⟨hr, ?_⟩, hrg⟩
    by_contra hlt
    have hy : r.getD 1 0 < 3 := by simpa using hlt
    obtain ⟨hwl, hwm, hzeq, hz2⟩ :=
      (rowChk_sound prep_base invChk_true badChk_true (rowsAll_sound.1 r hr)).2.2 hy
    set Ye := hm (Ywords.getD (r.getD 1 0) []) with hYe
    set L0e := hm (L0w.getD (r.getD 2 0) []) with hL0
    set L1e := hm (L1w.getD (r.getD 3 0) []) with hL1
    have hYT : Ye ∈ Sp0Core.TT r2H := hm_getD_Y_mem _
    have hc : Ye⁻¹ * g * Ye ∈ N := by
      have := hnorm.conj_mem ⟨g, hN hg⟩ (Subgroup.mem_subgroupOf.2 hg)
        ⟨Ye⁻¹, (Sp0Core.TT r2H).inv_mem hYT⟩
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hzN : g⁻¹ * Ye⁻¹ * g * Ye * L0e * L1e ∈ N := by
      have e : g⁻¹ * Ye⁻¹ * g * Ye * L0e * L1e = g⁻¹ * (Ye⁻¹ * g * Ye) * L0e * L1e := by group
      rw [e]
      exact N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem hg) hc) (hE (hm_getD_L0_mem _)))
        (hE (hm_getD_L1_mem _))
    have hzH : g⁻¹ * Ye⁻¹ * g * Ye * L0e * L1e = hm hwl * r2H * (hm hwl)⁻¹ := by
      apply Subtype.ext
      rw [← hrg]
      show _ = permW (LG GB) hwl * (r2H : Equiv.Perm (Fin 36)) * (permW (LG GB) hwl)⁻¹
      rw [r2H_val]
      exact hzeq
    have := hinv (hm hwl) (by rw [← hzH]; exact hzN)
    rw [← hzH] at this
    apply hz2
    have h3 := congrArg Subtype.val this
    rw [← hrg] at h3
    rw [r2H_val] at h3
    exact h3
  have hsub : (N : Set ModSp0) ⊆ ↑((rowsAll.filter (fun r => decide (3 ≤ r.getD 1 0))).map elt).toFinset := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := hmem g hg
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact List.mem_map_of_mem hr
  have hcardN : Nat.card ↥N ≤ 192 := by
    calc Nat.card ↥N = (N : Set ModSp0).ncard := (Nat.card_coe_set_eq _)
      _ ≤ (((rowsAll.filter (fun r => decide (3 ≤ r.getD 1 0))).map elt).toFinset : Set ModSp0).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ((rowsAll.filter (fun r => decide (3 ≤ r.getD 1 0))).map elt).toFinset.card :=
          Set.ncard_coe_finset _
      _ ≤ ((rowsAll.filter (fun r => decide (3 ≤ r.getD 1 0))).map elt).length :=
          List.toFinset_card_le _
      _ = 192 := by
          rw [List.length_map]
          exact rowsAll_cntS
  have hrel := Subgroup.relIndex_mul_card (H := N) (K := Sp0Core.TT r2H)
  rw [inf_of_le_left hN, card_TT] at hrel
  by_contra hle
  push Not at hle
  have := Nat.mul_le_mul hle hcardN
  omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K
