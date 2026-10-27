module

public import CFSG.Permutation.FinPackPow

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239K

open Equiv Equiv.Perm CFSG.Permutation.FinPack

theorem h16 : 7 ≤ 16 := by norm_num

@[expose] noncomputable def commK (c d : ℕ) : Bool := Nat.beq (mulK 7 c d) (mulK 7 d c)

@[expose] noncomputable def cB (c : ℕ) : Bool := commK c 105194241 && evenK 7 c

variable {s : Perm (Fin 7)}

theorem cB_iff (hs : enc s = 105194241) (a : Perm (Fin 7)) :
    (a * s = s * a ∧ sign a = 1) ↔ cB (enc a) = true := by
  have e : commK (enc a) 105194241 = true ↔ a * s = s * a := by
    rw [← hs]
    exact comm_enc_iff h16
  rw [cB.eq_1, Bool.and_eq_true, ← sign_eq_one_iff_evenK h16, e]

theorem ne_of_beq {σ τ : Perm (Fin 7)} (h : Nat.beq (enc σ) (enc τ) = false) : σ ≠ τ :=
  fun e => by
    rw [e, Nat.beq_refl] at h
    cases h

theorem cnt_cB : cntK 7 cB 7 0 0 0 = 24 := by decide +kernel

theorem card_K (hs : enc s = 105194241) :
    (Finset.univ.filter fun a : Perm (Fin 7) => a * s = s * a ∧ sign a = 1).card = 24 := by
  rw [Finset.filter_congr (fun a _ => cB_iff hs a), card_filter_eq_cntK, cnt_cB]

@[expose] noncomputable def KL : List ℕ := [106181136, 106177281, 105198081, 105194256]

@[expose] noncomputable def wB (y c : ℕ) : Bool :=
  cB c &&
    !Nat.beq (powK 7 106181136 (mulK 7 y (mulK 7 (mulK 7 c y) (invPK 7 c))) 8) 106181136

@[expose] noncomputable def qNK (y : ℕ) : Bool :=
  !cB y || memK y KL || !walkK 7 (fun c => !wB y c) 7 0 0 0

theorem qNK_walk : walkK 7 qNK 7 0 0 0 = true := by decide +kernel

theorem not_klein_K (hs : enc s = 105194241) (he : enc (1 : Perm (Fin 7)) = 106181136)
    {k₁ k₂ k₃ : Perm (Fin 7)} (h₁ : enc k₁ = 106177281) (h₂ : enc k₂ = 105198081)
    (h₃ : enc k₃ = 105194256) : ∀ y : Perm (Fin 7), (y * s = s * y ∧ sign y = 1) →
      ¬ (y = 1 ∨ y = k₁ ∨ y = k₂ ∨ y = k₃) →
      ∃ c : Perm (Fin 7), (c * s = s * c ∧ sign c = 1) ∧ (y * (c * y * c⁻¹)) ^ 8 ≠ 1 := by
  intro y hy hk
  have h := walkK_sound qNK_walk y
  have e1 : memK (enc y) KL = false := by
    refine Bool.eq_false_iff.2 fun e => hk ?_
    rw [memK_iff] at e
    simp only [KL, List.mem_cons, List.not_mem_nil, or_false] at e
    rw [← he, ← h₁, ← h₂, ← h₃] at e
    rcases e with e | e | e | e
    · exact Or.inl (enc_inj h16 e)
    · exact Or.inr (Or.inl (enc_inj h16 e))
    · exact Or.inr (Or.inr (Or.inl (enc_inj h16 e)))
    · exact Or.inr (Or.inr (Or.inr (enc_inj h16 e)))
  rw [qNK.eq_1, (cB_iff hs y).1 hy, e1] at h
  simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true'] at h
  obtain ⟨c, hc⟩ := exists_of_walkK (P := wB (enc y)) h
  rw [wB.eq_1, Bool.and_eq_true, Bool.not_eq_true', ← enc_inv h16] at hc
  simp only [← enc_mul h16] at hc
  rw [← enc_pow h16 he, ← he] at hc
  exact ⟨c, (cB_iff hs c).2 hc.1, ne_of_beq hc.2⟩

@[expose] noncomputable def KL3 : List ℕ := [106177281, 105198081, 105194256]

@[expose] noncomputable def conjB : Bool :=
  allK (fun y => allK (fun v =>
    !walkK 7 (fun c => !(cB c && Nat.beq (mulK 7 c y) (mulK 7 v c))) 7 0 0 0) KL3) KL3

theorem conjB_check : conjB = true := by decide +kernel

theorem conj_K (hs : enc s = 105194241) {l : List (Perm (Fin 7))} (hl : l.map enc = KL3) :
    ∀ y ∈ l, ∀ v ∈ l, ∃ c : Perm (Fin 7), (c * s = s * c ∧ sign c = 1) ∧ c * y * c⁻¹ = v := by
  intro y hy v hv
  have hm : ∀ {a : Perm (Fin 7)}, a ∈ l → enc a ∈ KL3 := fun h' => by
    rw [← hl]
    exact List.mem_map_of_mem h'
  have h := allK_iff.1 (allK_iff.1 conjB_check (enc y) (hm hy)) (enc v) (hm hv)
  rw [Bool.not_eq_true'] at h
  obtain ⟨c, hc⟩ := exists_of_walkK
    (P := fun c => cB c && Nat.beq (mulK 7 c (enc y)) (mulK 7 (enc v) c)) h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hc1, hc2⟩ := hc
  rw [← enc_mul h16, ← enc_mul h16, beq_enc_iff h16] at hc2
  exact ⟨c, (cB_iff hs c).2 hc1, by rw [mul_inv_eq_iff_eq_mul]; exact hc2⟩

@[expose] noncomputable def kB : Bool :=
  allK (fun a => allK (fun b => memK (mulK 7 a b) KL) KL && (memK (invPK 7 a) KL && evenK 7 a)) KL

theorem kB_check : kB = true := by decide +kernel

theorem klein_K {l : List (Perm (Fin 7))} (hl : l.map enc = KL) :
    (∀ x ∈ l, ∀ y ∈ l, x * y ∈ l) ∧ (∀ x ∈ l, x⁻¹ ∈ l) ∧ ∀ x ∈ l, sign x = 1 := by
  have hm : ∀ {a : Perm (Fin 7)}, a ∈ l → enc a ∈ KL := fun h' => by
    rw [← hl]
    exact List.mem_map_of_mem h'
  have hmem : ∀ a : Perm (Fin 7), memK (enc a) KL = true ↔ a ∈ l := fun a => by
    rw [memK_iff, ← hl, ← mem_iff_enc h16]
  have H : ∀ x ∈ l, (∀ y ∈ l, x * y ∈ l) ∧ x⁻¹ ∈ l ∧ sign x = 1 := by
    intro x hx
    have h := allK_iff.1 kB_check (enc x) (hm hx)
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun y hy => ?_, ?_, (sign_eq_one_iff_evenK h16 x).2 h3⟩
    · have := allK_iff.1 h1 (enc y) (hm hy)
      rw [← enc_mul h16, hmem] at this
      exact this
    · rw [← enc_inv h16, hmem] at h2
      exact h2
  exact ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2.1, fun x hx => (H x hx).2.2⟩

end CFSG.QuasithinUnique.Vol2Native.L239K
