module

public import Certificates.Data.Kernel.HMathieu.FixCert

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

@[expose] def linL (M : List ℕ) (m : ℕ) : ℕ := actM M m ^^^ m

theorem linL_xor (M : List ℕ) : XorLin (linL M) := fun a b => by
  simp only [linL, actM_xor M a b]
  ac_rfl

theorem xor_eq_zero_iff {a b : ℕ} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = (a ^^^ b) ^^^ b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      _ = b := by rw [h, Nat.zero_xor]
  · rintro rfl
    exact Nat.xor_self a

theorem linL_eq_zero_iff {M : List ℕ} {m : ℕ} : linL M m = 0 ↔ actM M m = m :=
  xor_eq_zero_iff

@[expose] def fixF (n : ℕ) (M : List ℕ) : Finset ℕ :=
  (Finset.range (2 ^ n)).filter fun m => actM M m = m

theorem length_filter_eq_card (n : ℕ) (M : List ℕ) :
    ((List.range (2 ^ n)).filter fun m => actM M m == m).length = (fixF n M).card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext m
  simp [fixF]

theorem card_fix_mul_card_img (n : ℕ) (M : List ℕ) :
    (fixF n M).card * ((Finset.range (2 ^ n)).image (linL M)).card = 2 ^ n := by
  have hL := linL_xor M
  have hfib : ∀ y ∈ (Finset.range (2 ^ n)).image (linL M),
      ((Finset.range (2 ^ n)).filter fun x => linL M x = y).card = (fixF n M).card := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
    have ha' : a < 2 ^ n := Finset.mem_range.1 ha
    refine Finset.card_nbij' (fun x => x ^^^ a) (fun x => x ^^^ a) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
      simp only [fixF, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨Nat.xor_lt_two_pow hx.1 ha', ?_⟩
      rw [← linL_eq_zero_iff, hL, hx.2, Nat.xor_self]
    · intro x hx
      simp only [fixF, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      refine ⟨Nat.xor_lt_two_pow hx.1 ha', ?_⟩
      rw [hL, (linL_eq_zero_iff).2 hx.2, Nat.zero_xor]
    · intro x _
      simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · intro x _
      simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have h := Finset.card_eq_sum_card_image (linL M) (Finset.range (2 ^ n))
  rw [Finset.sum_const_nat hfib, Finset.card_range] at h
  rw [mul_comm]
  exact h.symm

theorem combos_map {f : ℕ → ℕ} (hf : XorLin f) :
    ∀ l : List ℕ, combos (l.map f) = (combos l).map f
  | [] => by simp [combos, hf.map_zero]
  | a :: l => by
    rw [List.map_cons, combos, combos, combos_map hf l, List.map_append, List.map_map,
      List.map_map]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, hf x a]

theorem combos_fixed {M : List ℕ} :
    ∀ {l : List ℕ}, (∀ v ∈ l, actM M v = v) → ∀ x ∈ combos l, actM M x = x
  | [], _, x, hx => by
    simp only [combos, List.mem_singleton] at hx
    rw [hx]
    exact (actM_xor M).map_zero
  | a :: l, h, x, hx => by
    rw [combos, List.mem_append, List.mem_map] at hx
    have hl := combos_fixed (M := M) (fun v hv => h v (List.mem_cons_of_mem a hv))
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hl x hx
    · rw [actM_xor, hl y hy, h a List.mem_cons_self]

theorem fix_le_of_imgOK {n : ℕ} {M J : List ℕ} (hJ : ∀ j ∈ J, j < n) (h : imgOK M J = true) :
    (fixF n M).card ≤ 2 ^ (n - J.length) := by
  have hL := linL_xor M
  set l := combos ((J.map fun j => 2 ^ j).map (linL M)) with hl
  have hnd : l.Nodup := by
    rw [hl, List.map_map]
    exact (nodup_of_nodupB _ _ h).1
  have hsub : l.toFinset ⊆ (Finset.range (2 ^ n)).image (linL M) := by
    intro y hy
    rw [List.mem_toFinset, hl, combos_map hL, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    refine Finset.mem_image.2 ⟨x, Finset.mem_range.2 ?_, rfl⟩
    refine combos_lt (fun b hb => ?_) x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    exact Nat.pow_lt_pow_right (by norm_num) (hJ j hj)
  have hlen : l.toFinset.card = 2 ^ J.length := by
    rw [List.toFinset_card_of_nodup hnd, hl, length_combos, List.length_map, List.length_map]
  have himg : 2 ^ J.length ≤ ((Finset.range (2 ^ n)).image (linL M)).card :=
    hlen ▸ Finset.card_le_card hsub
  have hle : ((Finset.range (2 ^ n)).image (linL M)).card ≤ 2 ^ n :=
    Finset.card_image_le.trans (Finset.card_range _).le
  have hr : J.length ≤ n :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (himg.trans hle)
  have hmul := card_fix_mul_card_img n M
  have hpow : 2 ^ n = 2 ^ (n - J.length) * 2 ^ J.length := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos J.length)
  rw [← hpow, ← hmul]
  exact Nat.mul_le_mul_left _ himg

theorem fix_ge_of_kerOK {n : ℕ} {M K : List ℕ} (hK : ∀ v ∈ K, v < 2 ^ n)
    (h : kerOK M K = true) : 2 ^ K.length ≤ (fixF n M).card := by
  simp only [kerOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  have hnd := (nodup_of_nodupB _ _ h.2).1
  have hsub : (combos K).toFinset ⊆ fixF n M := by
    intro x hx
    rw [List.mem_toFinset] at hx
    simp only [fixF, Finset.mem_filter, Finset.mem_range]
    exact ⟨combos_lt hK x hx, combos_fixed h.1 x hx⟩
  rw [← length_combos, ← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card hsub

theorem allImg_sound {n r : ℕ} : ∀ {Ms Js : List (List ℕ)}, allImg n r Ms Js = true →
    ∀ M ∈ Ms, ((List.range (2 ^ n)).filter fun m => actM M m == m).length ≤ 2 ^ (n - r)
  | [], [], _, _, hM => absurd hM List.not_mem_nil
  | M :: Ms, J :: Js, h, M', hM' => by
    simp only [allImg, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hr, hJ⟩, hok⟩, hrest⟩ := h
    rcases List.mem_cons.1 hM' with rfl | hM'
    · rw [length_filter_eq_card, ← hr]
      exact fix_le_of_imgOK hJ hok
    · exact allImg_sound hrest M' hM'
  | [], _ :: _, h, _, _ => by simp [allImg] at h
  | _ :: _, [], h, _, _ => by simp [allImg] at h

theorem allKer_sound {n k : ℕ} : ∀ {Ms Ks : List (List ℕ)}, allKer n k Ms Ks = true →
    ∀ M ∈ Ms, 2 ^ k ≤ ((List.range (2 ^ n)).filter fun m => actM M m == m).length
  | [], [], _, _, hM => absurd hM List.not_mem_nil
  | M :: Ms, K :: Ks, h, M', hM' => by
    simp only [allKer, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hk, hK⟩, hok⟩, hrest⟩ := h
    rcases List.mem_cons.1 hM' with rfl | hM'
    · rw [length_filter_eq_card, ← hk]
      exact fix_ge_of_kerOK hK hok
    · exact allKer_sound hrest M' hM'
  | [], _ :: _, h, _, _ => by simp [allKer] at h
  | _ :: _, [], h, _, _ => by simp [allKer] at h

end CFSG.KC.HMathieu

end
