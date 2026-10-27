module

public import Certificates.Data.GH23Perm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Vocab

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

@[expose] def gh23Code (σ : Equiv.Perm (Fin 8)) : ℕ := ∑ i : Fin 8, (σ i : ℕ) * 8 ^ (i : ℕ)

private lemma gh23_img_sum (d : Fin 8 → ℕ) (hd : ∀ j, d j < 8) (k : Fin 8) :
    (∑ j : Fin 8, d j * 8 ^ (j : ℕ)) / 2 ^ (3 * (k : ℕ)) % 8 = d k := by
  rw [Fin.sum_univ_eight]
  fin_cases k <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, pow_zero, pow_one,
      mul_one, zero_mul] <;>
    norm_num <;>
    (have h0 := hd 0; have h1 := hd 1; have h2 := hd 2; have h3 := hd 3;
     have h4 := hd 4; have h5 := hd 5; have h6 := hd 6; have h7 := hd 7) <;>
    omega

theorem gh23_img_code (σ : Equiv.Perm (Fin 8)) (i : Fin 8) :
    img (gh23Code σ) i = (σ i : ℕ) := by
  unfold gh23Code img
  rw [Nat.shiftRight_eq_div_pow]
  exact gh23_img_sum (fun j => (σ j : ℕ)) (fun j => (σ j).isLt) i

theorem gh23_code_injective : Function.Injective gh23Code := by
  intro σ τ h
  apply Equiv.ext
  intro i
  apply Fin.ext
  have h1 := gh23_img_code σ i
  have h2 := gh23_img_code τ i
  rw [h] at h1
  rw [h1] at h2
  exact h2

private lemma mulC_eq_sum (a b : ℕ) :
    mulC a b = ∑ k : Fin 8, img a (img b k) * 8 ^ (k : ℕ) := by
  simp only [mulC, Fin.sum_univ_eight]
  norm_num
  ring

theorem gh23_mulC_code (σ τ : Equiv.Perm (Fin 8)) :
    mulC (gh23Code σ) (gh23Code τ) = gh23Code (σ * τ) := by
  rw [mulC_eq_sum]
  show ∑ k : Fin 8, img (gh23Code σ) (img (gh23Code τ) k) * 8 ^ (k : ℕ)
      = ∑ k : Fin 8, ((σ * τ) k : ℕ) * 8 ^ (k : ℕ)
  apply Finset.sum_congr rfl
  intro k _
  rw [gh23_img_code τ k, gh23_img_code σ (τ k), Equiv.Perm.mul_apply]

theorem gh23_oneC : oneC = gh23Code 1 := by
  decide +kernel

private lemma gh23_sum_img (c : ℕ) (hc : c < 16777216) :
    (∑ i : Fin 8, img c i * 8 ^ (i : ℕ)) = c := by
  simp only [img, Nat.shiftRight_eq_div_pow]
  rw [Fin.sum_univ_eight]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat]
  norm_num
  omega

theorem gh23_exists_of_validC {c : ℕ} (h : validC c = true) :
    ∃ σ : Equiv.Perm (Fin 8), gh23Code σ = c := by
  rw [validC, Bool.and_eq_true] at h
  obtain ⟨hlt, hall⟩ := h
  rw [decide_eq_true_iff] at hlt
  rw [List.all_eq_true] at hall
  have hdigit : ∀ i j : Fin 8, (j : ℕ) < (i : ℕ) → img c i ≠ img c j := by
    intro i j hij
    have hi := hall i (List.mem_range.mpr i.isLt)
    rw [List.all_eq_true] at hi
    have hj := hi j (List.mem_range.mpr hij)
    rwa [bne_iff_ne] at hj
  let f : Fin 8 → Fin 8 := fun i => ⟨img c i, Nat.mod_lt _ (by norm_num)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : img c i = img c j := congrArg Fin.val hij
    rcases lt_or_gt_of_ne hne with hlt' | hlt'
    · exact hdigit j i (by exact_mod_cast hlt') heq.symm
    · exact hdigit i j (by exact_mod_cast hlt') heq
  let σ : Equiv.Perm (Fin 8) := Equiv.ofBijective f hf.bijective_of_finite
  refine ⟨σ, ?_⟩
  have hσ : ∀ i : Fin 8, (σ i : ℕ) = img c i := fun i => rfl
  have hcode : gh23Code σ = ∑ i : Fin 8, img c i * 8 ^ (i : ℕ) := by
    unfold gh23Code
    apply Finset.sum_congr rfl
    intro i _
    rw [hσ i]
  rw [hcode, gh23_sum_img c hlt]

theorem gh23_code_g5 : gh23Code gh23g5 = 16419025 := by
  decide +kernel

theorem gh23_code_g7 : gh23Code gh23g7 = 14899409 := by
  decide +kernel

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
