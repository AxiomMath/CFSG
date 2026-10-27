module

public import Certificates.Certificate255001
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2MemberE64

public section

namespace CFSG.ClassicalInvolution.Q3.E64Ker

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.E64Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

theorem mkQ7_inj {x y : Wr 7} (hx : x ∈ aeSub 7) (hy : y ∈ aeSub 7)
    (h : mkQ 7 x = mkQ 7 y) : x = y := by
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact inv_mul_eq_one.mp h1
  · exfalso
    have hm : x⁻¹ * y ∈ aeSub 7 := (aeSub 7).mul_mem ((aeSub 7).inv_mem hx) hy
    rw [h1] at hm
    exact (by decide +kernel : wsum (allOnes 7) ≠ 0) (mem_aeSub.mp hm).1

theorem mA_mem : mA ∈ aeSub 7 :=
  mem_aeSub.mpr (by decide +kernel)

theorem mB_mem : mB ∈ aeSub 7 :=
  mem_aeSub.mpr (by decide +kernel)

theorem mC_zero : mC 0 = 1 := by
  decide +kernel

theorem mG_even (j : ℕ) : mG (2 * j) = mC j * mA * (mC j)⁻¹ := by
  have h1 : 2 * j / 2 = j := by omega
  have h2 : 2 * j % 2 = 0 := by omega
  simp only [mG, h1, h2, if_true]

theorem mG_odd (j : ℕ) : mG (2 * j + 1) = mC j * mB * (mC j)⁻¹ := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have h2 : (2 * j + 1) % 2 = 1 := by omega
  simp only [mG, h1, h2, one_ne_zero, if_false]

theorem mG_zero : mG 0 = mA := by
  decide +kernel

theorem mG_one : mG 1 = mB := by
  decide +kernel

theorem model_check :
    e64ConjData.all rowOK = true ∧ conjOK = true ∧ (m8 0).Nodup ∧ distinctOK = true ∧
      partnerOK = true ∧ y3OK = true ∧ (l32Fin ()).card = 168 ∧ (evenFin ()).card = 64 := by
  obtain ⟨-, hA, hB, hC, hD, hE, hF, hG, hH⟩ := Certificates.certificate255001
  refine ⟨List.all_eq_true.mpr fun d hd => decide_eq_true (hA d hd),
    List.all_eq_true.mpr fun j hj => decide_eq_true (hB j (List.mem_range.mp hj)), hC, ?_, ?_, ?_,
    hG, hH⟩
  · refine List.all_eq_true.mpr fun j hj => List.all_eq_true.mpr fun k hk => ?_
    rw [List.mem_range] at hj hk
    by_cases hjk : j = k
    · simp [hjk]
    · have hn := hD j hj k hk hjk
      simp [hjk, hn]
  · simp only [partnerOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨⟨hE.1, hE.2.1⟩, hE.2.2⟩
  · simp only [y3OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨⟨⟨hF.1, hF.2.1⟩, hF.2.2.1⟩, hF.2.2.2.1⟩, hF.2.2.2.2⟩

theorem mC_mem {j : ℕ} (hj : j < 14) :
    mC j ∈ aeSubOver l32 := by
  have h := model_check.2.1
  unfold conjOK at h
  rw [List.all_eq_true] at h
  have h1 := h j (List.mem_range.mpr hj)
  rw [decide_eq_true_eq] at h1
  exact ofPerm_mem_aeSubOver h1.1 h1.2

theorem mG_mem {i : ℕ} (hi : i < 28) : mG i ∈ aeSub 7 := by
  have hc : mC (i / 2) ∈ aeSub 7 := (mC_mem (by omega)).1
  unfold mG
  refine (aeSub 7).mul_mem ((aeSub 7).mul_mem hc ?_) ((aeSub 7).inv_mem hc)
  split_ifs
  · exact mA_mem
  · exact mB_mem

theorem mWord_mem {k : ℕ} (hk : k < 14) {W : List ℕ}
    (hW : ∀ l ∈ W, l < 2) : mWord k W ∈ aeSub 7 := by
  unfold mWord
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  have := hW l hl
  exact mG_mem (by omega)

theorem α0_mem_e64Sets : α0 ∈ e64Sets :=
  ⟨{0, 1, 3}, by decide +kernel, by decide +kernel⟩

theorem mA_eq_aW : mA = aW := by
  decide +kernel

theorem mB_eq_bW : mB = bW := by
  decide +kernel

theorem mA_mem_memAt : mA ∈ memAt α0 α0_card true := by
  rw [mA_eq_aW]
  exact aW_mem_memAt

theorem mB_mem_memAt : mB ∈ memAt α0 α0_card true := by
  rw [mB_eq_bW]
  exact bW_mem_memAt

theorem mkQ_mA_mem : mkQ 7 mA ∈ memBar α0 α0_card true :=
  ⟨mA, mA_mem_memAt, rfl⟩

theorem mkQ_mB_mem : mkQ 7 mB ∈ memBar α0 α0_card true :=
  ⟨mB, mB_mem_memAt, rfl⟩

theorem mWord_zero_mem_memAt {W : List ℕ} (hW : ∀ l ∈ W, l < 2) :
    mWord 0 W ∈ memAt α0 α0_card true := by
  unfold mWord
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  have hl2 := hW l hl
  interval_cases l
  · rw [show 2 * 0 + 0 = 0 from rfl, mG_zero]
    exact mA_mem_memAt
  · rw [show 2 * 0 + 1 = 1 from rfl, mG_one]
    exact mB_mem_memAt

theorem localWords_lt : ∀ W ∈ localWords, ∀ l ∈ W, l < 2 := by
  decide +kernel

theorem q8_pow_four : mA * mA * mA * mA = 1 := by
  decide +kernel

theorem q8_sq_eq : mA * mA = mB * mB := by
  decide +kernel

theorem q8_conj : mB * mA * mB⁻¹ * mA = 1 := by
  decide +kernel

theorem mA_sq_ne_one : mA * mA ≠ 1 := by
  decide +kernel

theorem local_pow_four : ∀ W ∈ localWords,
    mWord 0 W * mWord 0 W * mWord 0 W * mWord 0 W = 1 := by
  decide +kernel

theorem local_sq_eq_one : ∀ W ∈ localWords,
    mWord 0 W * mWord 0 W = 1 → mWord 0 W = 1 ∨ mWord 0 W = mA * mA := by
  decide +kernel

theorem local_central : ∀ W ∈ localWords,
    mWord 0 W * (mA * mA) = (mA * mA) * mWord 0 W := by
  decide +kernel

theorem conjData_bounds : ∀ d ∈ e64ConjData, d.1 < 28 ∧ d.2.1 < 14 ∧ d.2.2.1 < 2 ∧
    d.2.2.2.1 < 14 ∧ ∀ l ∈ d.2.2.2.2, l < 2 := by
  decide +kernel

theorem conjData_sibling : ∀ d ∈ e64ConjData, ∀ l < 2, ∃ d' ∈ e64ConjData, d'.1 = d.1 ∧
    d'.2.1 = d.2.1 ∧ d'.2.2.1 = l ∧ d'.2.2.2.1 = d.2.2.2.1 := by
  decide +kernel

theorem row_eq {d : Nat × Nat × Nat × Nat × List Nat}
    (hd : d ∈ e64ConjData) :
    mG d.1 * mG (2 * d.2.1 + d.2.2.1) * (mG d.1)⁻¹ = mWord d.2.2.2.1 d.2.2.2.2 := by
  have h := model_check.1
  rw [List.all_eq_true] at h
  have h1 := h d hd
  unfold rowOK at h1
  exact of_decide_eq_true h1

theorem distinct_ne {j k : ℕ} (hj : j < 14) (hk : k < 14)
    (hne : j ≠ k) : ∀ W ∈ localWords, mG (2 * j) ≠ mWord k W := by
  intro W hW heq
  have h := model_check.2.2.2.1
  unfold distinctOK at h
  rw [List.all_eq_true] at h
  have h1 := h j (List.mem_range.mpr hj)
  rw [List.all_eq_true] at h1
  have h2 := h1 k (List.mem_range.mpr hk)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exact hne h2
  · have hmem : mG (2 * j) ∈ m8 k := by
      rw [heq]
      exact List.mem_map_of_mem hW
    have h3 : (m8 k).contains (mG (2 * j)) = true := List.elem_eq_true_of_mem hmem
    rw [h3] at h2
    exact Bool.noConfusion h2

theorem partner_facts :
    e64JStar < 14 ∧ e64JStar ≠ 0 ∧ mG (2 * e64JStar) * mG (2 * e64JStar) = mA * mA := by
  have h := model_check.2.2.2.2.1
  simp only [partnerOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem y3_facts :
    mY3 * mY3 * mY3 = 1 ∧ mY3 ∈ aeSubOver l32 ∧
      (∀ r ∈ e64Y3Rows, mY3 * mG (2 * r.1 + r.2.1) * mY3⁻¹ = mWord r.1 r.2.2) ∧
      mY3 * mA ≠ mA * mY3 ∧ mY3 * mG (2 * e64JStar) ≠ mG (2 * e64JStar) * mY3 := by
  have h := model_check.2.2.2.2.2.1
  simp only [y3OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, ofPerm_mem_aeSubOver h2.1 h2.2, h3, h4, h5⟩

end CFSG.ClassicalInvolution.Q3.E64Ker
