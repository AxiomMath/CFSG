module

public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.LargeExtraspecial.AS62PackK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

theorem enc_one5 : enc (1 : Perm (Fin 5)) = 274960 := by decide +kernel

@[expose] noncomputable def commPowB (c d : ℕ) : Bool :=
  !(Nat.beq (powK 5 274960 (mulK 5 (mulK 5 (mulK 5 d c) (invCK 5 d)) (invCK 5 c)) 8) 274960)

@[expose] noncomputable def witQ (c : ℕ) : Bool :=
  Nat.beq c 274960 || anyK (fun d => permValidK 5 d && (evenK 5 d && commPowB c d))
    [213280, 213505, 271105, 148240]

theorem wit_walk : walkK 5 witQ 5 0 0 0 = true := by decide +kernel

theorem exists_comm_pow_ne_pack : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 →
    ∃ a : Equiv.Perm (Fin 5), Equiv.Perm.sign a = 1 ∧ (a * σ * a⁻¹ * σ⁻¹) ^ 8 ≠ 1 := by
  intro σ hσ
  have h := walkK_sound wit_walk σ
  have hb : Nat.beq (enc σ) 274960 = false := by
    rw [← enc_one5]
    exact beq_enc_false (by norm_num) hσ
  rw [witQ, hb, Bool.false_or] at h
  obtain ⟨a, ha⟩ := exists_of_anyK_valid h
  simp only [Bool.and_eq_true] at ha
  refine ⟨a, (sign_eq_one_iff_evenK (by norm_num) a).2 ha.1, ?_⟩
  have key : powK 5 274960 (mulK 5 (mulK 5 (mulK 5 (enc a) (enc σ)) (invCK 5 (enc a)))
      (invCK 5 (enc σ))) 8 = enc ((a * σ * a⁻¹ * σ⁻¹) ^ 8) := by
    rw [enc_pow (by norm_num) enc_one5, enc_mul (by norm_num), enc_mul (by norm_num),
      enc_mul (by norm_num), enc_inv_invCK (by norm_num), enc_inv_invCK (by norm_num)]
  intro heq
  have h2 := ha.2
  rw [commPowB, key, heq, enc_one5, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

end CFSG.LargeExtraspecial.AS62PackK
