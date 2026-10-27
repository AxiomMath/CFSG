module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Alt7KleinHypK

open Equiv Equiv.Perm Finset CFSG.Permutation.FinPack

theorem h16 : 7 ≤ 16 := by norm_num

@[expose] noncomputable def qInv (c : ℕ) : Bool :=
  Nat.beq (mulK 7 c c) 106181136 && !Nat.beq c 106181136 && evenK 7 c

theorem qInv_iff (h1 : enc (1 : Perm (Fin 7)) = 106181136)
    (σ : Perm (Fin 7)) : qInv (enc σ) = true ↔ σ * σ = 1 ∧ σ ≠ 1 ∧ Perm.sign σ = 1 := by
  rw [qInv.eq_1, ← h1, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    ← enc_mul h16, beq_enc_iff h16, ← sign_eq_one_iff_evenK h16]
  constructor
  · rintro ⟨⟨hs, hn⟩, he⟩
    refine ⟨hs, fun h => ?_, he⟩
    have e := (beq_enc_iff h16).2 h
    rw [hn] at e
    exact Bool.false_ne_true e
  · rintro ⟨hs, hn, he⟩
    exact ⟨⟨hs, beq_enc_false h16 hn⟩, he⟩

theorem cnt_qInv : cntK 7 qInv 7 0 0 0 = 105 := by decide +kernel

theorem card_even_invol_K (h1 : enc (1 : Perm (Fin 7)) = 106181136) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 7) =>
      σ * σ = 1 ∧ σ ≠ 1 ∧ Equiv.Perm.sign σ = 1)).card = 105 := by
  rw [Finset.filter_congr fun σ _ => (qInv_iff h1 σ).symm, card_filter_eq_cntK, cnt_qInv]

@[expose] noncomputable def qNoConj (c : ℕ) (g : ℕ) : Bool :=
  !(Nat.beq (mulK 7 g 106177281) (mulK 7 c g) && evenK 7 g)

@[expose] noncomputable def qConj (c : ℕ) : Bool :=
  !qInv c || !walkK 7 (qNoConj c) 7 0 0 0

theorem qConj_walk : walkK 7 qConj 7 0 0 0 = true := by decide +kernel

theorem even_invol_conj_K (a₀ : Perm (Fin 7)) (h1 : enc (1 : Perm (Fin 7)) = 106181136)
    (ha : enc a₀ = 106177281) (x : Perm (Fin 7)) (hx1 : x * x = 1) (hx2 : x ≠ 1)
    (hx3 : Perm.sign x = 1) : ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ g * a₀ * g⁻¹ = x := by
  have h := walkK_sound qConj_walk x
  rw [qConj.eq_1, (qInv_iff h1 x).2 ⟨hx1, hx2, hx3⟩, Bool.not_true,
    Bool.false_or, Bool.not_eq_true'] at h
  obtain ⟨g, hg⟩ := exists_of_walkK
    (P := fun g => Nat.beq (mulK 7 g 106177281) (mulK 7 (enc x) g) && evenK 7 g) h
  have hg' : (Nat.beq (mulK 7 (enc g) 106177281) (mulK 7 (enc x) (enc g)) &&
      evenK 7 (enc g)) = true := hg
  rw [Bool.and_eq_true, ← ha, ← enc_mul h16, ← enc_mul h16, beq_enc_iff h16,
    ← sign_eq_one_iff_evenK h16] at hg'
  exact ⟨g, hg'.2, by rw [mul_inv_eq_iff_eq_mul]; exact hg'.1⟩

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Alt7KleinHypK
