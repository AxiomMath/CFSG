module

public import CFSG.Permutation.FinPackDec
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree

open CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def letM12 (l : ℤ) : NativeSporadic.M12 :=
  if l = 1 then m12a else if l = -1 then m12a⁻¹ else if l = 2 then m12b else m12b⁻¹

@[expose] def wordM12 (w : List ℤ) : NativeSporadic.M12 := (w.map letM12).prod

@[expose] def m12x : NativeSporadic.M12 :=
  wordM12 [1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2]

@[expose] def m12y : NativeSporadic.M12 :=
  wordM12 [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1,
    -2]

@[expose] def m12z : NativeSporadic.M12 := m12x * m12y * m12x⁻¹ * m12y⁻¹

@[expose] def m12f (p : Fin 3 × Fin 3 × Fin 3) : NativeSporadic.M12 :=
  m12x ^ (p.1 : ℕ) * m12y ^ (p.2.1 : ℕ) * m12z ^ (p.2.2 : ℕ)

@[expose] def m12tws : List (List ℤ) :=
  [[], [2, 1, 2, 1, -2, 1, -2], [2, 1, 2, 1, -2, 1, -2],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2],
    [1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2],
    [1, -2, 1, 2, 1], [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1, -2, 1, 2, 1],
    [1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2],
    [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1, -2, 1, 2, 1],
    [-2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2],
    [2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2], [1, -2, 1, 2, 1],
    [2, 1, 2, 1, -2, 1, -2], [2, 1, 2, 1, -2, 1, -2], [1, -2, 1, 2, 1],
    [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1, -2, 1, 2, 1],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [2, 1, 2, 1, -2, 1, -2],
    [2, 1, 2, 1, -2, 1, -2], [1, -2, 1, 2, 1], [1, -2, 1, 2, 1],
    [2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2],
    [-2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2]]

@[expose] def m12t (p : Fin 3 × Fin 3 × Fin 3) : NativeSporadic.M12 :=
  wordM12 (m12tws.getD (9 * (p.1 : ℕ) + 3 * (p.2.1 : ℕ) + (p.2.2 : ℕ)) [])

@[expose] def m12σx (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  (p.1 + 1, p.2.1, p.2.2 - p.2.1)

@[expose] def m12σy (p : Fin 3 × Fin 3 × Fin 3) : Fin 3 × Fin 3 × Fin 3 :=
  (p.1, p.2.1 + 1, p.2.2)

theorem m12_gen_facts : m12x ^ 3 = 1 ∧ m12y ^ 3 = 1 := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem m12f_inj : Function.Injective m12f := by
  intro p q h
  revert p q
  decide +kernel

theorem m12f_σx : ∀ p, m12f p * m12x = m12f (m12σx p) := by decide +kernel

theorem m12f_σy : ∀ p, m12f p * m12y = m12f (m12σy p) := by decide +kernel

theorem m12f_one : ∃ p, m12f p = 1 := ⟨(0, 0, 0), by decide +kernel⟩

section M12Codes

open CFSG.Permutation.FinPack

@[expose] noncomputable def m12LetK (l : ℤ) : ℕ :=
  if l = 1 then 92532767328531 else if l = -1 then 92532767328531 else if l = 2 then 180734465348391
    else 82837192188216

@[expose] noncomputable def m12WordK (w : List ℤ) : ℕ :=
  w.foldr (fun l acc => mulK 12 (m12LetK l) acc) (enc (1 : Equiv.Perm (Fin 12)))

theorem m12gA_enc : enc m12gA = 92532767328531 := by decide +kernel
theorem m12gAinv_enc : enc m12gA⁻¹ = 92532767328531 := by decide +kernel
theorem m12gB_enc : enc m12gB = 180734465348391 := by decide +kernel
theorem m12gBinv_enc : enc m12gB⁻¹ = 82837192188216 := by decide +kernel

theorem m12LetK_enc (l : ℤ) :
    enc ((letM12 l : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12LetK l := by
  unfold letM12 m12LetK
  split_ifs <;> simp only [InvMemClass.coe_inv, m12gA_enc, m12gAinv_enc, m12gB_enc, m12gBinv_enc]

theorem m12WordK_enc (w : List ℤ) :
    enc ((wordM12 w : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12WordK w := by
  have hn : 12 ≤ 16 := by norm_num
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [m12WordK, List.foldr_cons, ← m12WordK, ← ih, ← m12LetK_enc, ← enc_mul hn, wordM12,
      List.map_cons, List.prod_cons, Subgroup.coe_mul, ← wordM12]

@[expose] noncomputable def m12fK (p : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  mulK 12 (mulK 12
      (powK 12 (enc (1 : Equiv.Perm (Fin 12))) (m12WordK [1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2,
        1, -2, 1, -2, 1, -2, 1, 2]) (p.1 : ℕ))
      (powK 12 (enc (1 : Equiv.Perm (Fin 12))) (m12WordK [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2,
        1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2]) (p.2.1 : ℕ)))
    (powK 12 (enc (1 : Equiv.Perm (Fin 12)))
      (mulK 12 (mulK 12 (mulK 12
        (m12WordK [1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2])
        (m12WordK [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2,
          1, -2, 1, -2]))
        (invCK 12 (m12WordK [1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2])))
        (invCK 12 (m12WordK [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1,
          2, 1, 2, 1, -2, 1, -2]))) (p.2.2 : ℕ))

theorem m12fK_enc (p : Fin 3 × Fin 3 × Fin 3) :
    enc ((m12f p : NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12fK p := by
  have hn : 12 ≤ 16 := by norm_num
  simp only [m12f, m12z, Subgroup.coe_mul, SubmonoidClass.coe_pow, InvMemClass.coe_inv,
    enc_mul hn, ← powK_enc hn, enc_inv_invCK hn, m12x, m12y, m12WordK_enc, m12fK]

@[expose] noncomputable def m12tK (p : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  m12WordK (m12tws.getD (9 * (p.1 : ℕ) + 3 * (p.2.1 : ℕ) + (p.2.2 : ℕ)) [])

theorem m12f_tinv_codes : ∀ p : Fin 3 × Fin 3 × Fin 3,
    Nat.beq (mulK 12 (mulK 12 (m12tK p) (m12fK p)) (invCK 12 (m12tK p))) (invCK 12 (m12fK p)) =
      true := by
  decide +kernel

theorem m12f_tinv : ∀ p, m12t p * m12f p * (m12t p)⁻¹ = (m12f p)⁻¹ := by
  have hn : 12 ≤ 16 := by norm_num
  intro p
  have h := m12f_tinv_codes p
  rw [m12tK, ← m12WordK_enc, ← m12t, ← m12fK_enc, invCK_enc hn, invCK_enc hn, ← enc_mul hn,
    ← enc_mul hn, beq_enc_iff hn] at h
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using h

end M12Codes

theorem m12f_mem : ∀ p, m12f p ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) := by
  intro p
  have hx : m12x ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) :=
    Subgroup.subset_closure (by simp)
  have hy : m12y ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) :=
    Subgroup.subset_closure (by simp)
  have hz : m12z ∈ Subgroup.closure ({m12x, m12y} : Set NativeSporadic.M12) :=
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  exact mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem hz _)

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree
