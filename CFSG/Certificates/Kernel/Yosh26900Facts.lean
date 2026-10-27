module

public import Certificates.Data.Kernel.Yosh26900
public import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Yosh26900

open Equiv Finset CFSG.KC.Ord CFSG.KC.LQT.P

theorem hn14 : (14 : ℕ) ≤ 32 := by norm_num

theorem cntN_eq (m : ℕ) (f : ℕ → Bool) : cntN m f = ((range m).filter fun j => f j = true).card := by
  rw [card_filter]
  induction m with
  | zero => rfl
  | succ m ih =>
    change Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 (f m)) (cntN m f) = _
    rw [sum_range_succ, ← ih]
    cases f m
    · change 0 + cntN m f = cntN m f + 0
      omega
    · change 1 + cntN m f = cntN m f + 1
      omega

section Facts

variable {N : ℕ} {E : ℕ → ℕ} {X : ℕ → Perm (Fin 14)}

theorem cen_sound (hX : ∀ k < N, E k = code (X k)) {V : ℕ → ℕ} {Y : ℕ → Perm (Fin 14)}
    (hY : ∀ k < N, V k = code (Y k)) (c : Perm (Fin 14)) {α : ℕ}
    (h : ∀ k < N, cenAt E V (code c) α k = true) :
    ∀ k < N, Y k = X k * c ^ (epsK (code (X k)) + α * lamK (code (X k))) := by
  intro k hk
  have h1 := h k hk
  unfold cenAt at h1
  rw [letB_eq, hX k hk, hY k hk, code_pow hn14, code_mul hn14, beq_code hn14] at h1
  exact h1

theorem pt_sound {V TE TI PJ : ℕ → ℕ} {T Y : ℕ → Perm (Fin 14)} (hT : ∀ j < 128, TE j = code (T j))
    (hY : ∀ j < 128, V (TI j) = code (Y j)) (h : ∀ j < 128, ptAt V TE TI PJ j = true) :
    ∀ j < 128, ∃ i < 128, Y j = T i := by
  intro j hj
  have h1 := h j hj
  unfold ptAt at h1
  rw [letB_eq] at h1
  obtain ⟨hi, he⟩ := andB_iff.1 h1
  have hi' := Nat.blt_eq.mp hi
  refine ⟨_, hi', ?_⟩
  rw [hT _ hi', hY j hj, beq_code hn14] at he
  exact he.symm

theorem twB_code (u pu t : Perm (Fin 14)) :
    twB (code u) (code pu) (code t) = true ↔ t * pu = u * t := by
  unfold twB
  rw [code_mul hn14, code_mul hn14, beq_code hn14]

theorem bad_sound {TE TI V : ℕ → ℕ} {T Z : ℕ → Perm (Fin 14)} (hT : ∀ j < 128, TE j = code (T j))
    (hZ : ∀ j < 128, V (TI j) = code (Z j)) (u pu : Perm (Fin 14))
    (h : badAt TE TI V (code u) (code pu) = true) :
    ((range 128).filter fun j => T j * u = u * T j).card +
        ((range 128).filter fun j => T j * pu = u * T j).card = 128 ∧
      (∀ j < 128, T j * u = u * T j → T j ^ 4 = 1) ∧
      (∀ j < 128, T j * pu = u * T j → (T j * Z j) ^ 2 = 1) := by
  unfold badAt at h
  obtain ⟨hc, ha⟩ := andB_iff.1 h
  rw [allN_iff] at ha
  have hfa : ∀ (q : Perm (Fin 14)), ((range 128).filter fun j => twB (code u) (code q) (TE j) = true) =
      (range 128).filter fun j => T j * q = u * T j := by
    intro q
    refine filter_congr fun j hj => ?_
    rw [hT j (mem_range.1 hj), twB_code]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hfa u, ← hfa pu, ← cntN_eq, ← cntN_eq]
    exact Nat.eq_of_beq_eq_true hc
  · intro j hj hc'
    have h1 := ha j hj
    unfold bad4At at h1
    rw [letB_eq, hT j hj] at h1
    have h2 := impB_iff.1 (andB_iff.1 h1).1 ((twB_code u u (T j)).2 hc')
    rwa [code_pow hn14, code_one, beq_code hn14] at h2
  · intro j hj hc'
    have h1 := ha j hj
    unfold bad4At at h1
    rw [letB_eq, hT j hj] at h1
    have h2 := impB_iff.1 (andB_iff.1 h1).2 ((twB_code u pu (T j)).2 hc')
    rwa [hZ j hj, code_mul hn14, code_pow hn14, code_one, beq_code hn14] at h2

theorem cn_sound (hX : ∀ k < N, E k = code (X k)) (e c : Perm (Fin 14))
    (h : ∀ k < N, cnAt E (code e) (code c) k = true) :
    ∀ k < N, X k * e = e * X k ∧ X k * c = c * X k := by
  intro k hk
  have h1 := h k hk
  unfold cnAt at h1
  rw [hX k hk, andB_iff, comm_code hn14, comm_code hn14] at h1
  exact h1

theorem cs_sound (hX : ∀ k < N, E k = code (X k)) (s e c : Perm (Fin 14))
    (h : ∀ k < N, csAt E (code s) (code e) (code c) k = true) :
    ∀ k < N, X k * s = s * X k → ∃ a < 2, ∃ b < 2, ∃ r < 3, e ^ a * c ^ b * s ^ r = X k := by
  intro k hk hcs
  have h1 := h k hk
  unfold csAt at h1
  rw [hX k hk, impB_iff, comm_code hn14] at h1
  obtain ⟨a, ha, h1⟩ := (anyN_iff _ _).1 (h1 hcs)
  obtain ⟨b, hb, h1⟩ := (anyN_iff _ _).1 h1
  obtain ⟨r, hr, h1⟩ := (anyN_iff _ _).1 h1
  rw [code_pow hn14, code_pow hn14, code_pow hn14, code_mul hn14, code_mul hn14,
    beq_code hn14] at h1
  exact ⟨a, ha, b, hb, r, hr, h1⟩

theorem syl_sound (hX : ∀ k < 384, E k = code (X k)) {SY : ℕ → ℕ} (s : Perm (Fin 14))
    (h : ∀ k < 384, sylAt E SY (code s) k = true) :
    ∀ k < 384, X k ^ 3 = 1 → X k ≠ 1 →
      SY k < 384 ∧ (X (SY k) * X k = s * X (SY k) ∨ X (SY k) * X k = s * s * X (SY k)) := by
  intro k hk h3 h1
  have h2 := h k hk
  unfold sylAt at h2
  rw [hX k hk, impB_iff, andB_iff, notB_iff, code_pow hn14, code_one, beq_code hn14,
    beq_code hn14] at h2
  have h4 := h2 ⟨h3, h1⟩
  rw [letB_eq, andB_iff, orB_iff] at h4
  obtain ⟨hlt, h5⟩ := h4
  have hlt' := Nat.blt_eq.mp hlt
  refine ⟨hlt', ?_⟩
  rwa [hX _ hlt', code_mul hn14, code_mul hn14, code_mul hn14, code_mul hn14, beq_code hn14,
    beq_code hn14] at h5

end Facts

end CFSG.KC.Yosh26900

end
