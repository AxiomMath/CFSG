module

public import Certificates.Data.Kernel.Sp43KCount
public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Group

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43 CFSG.Sp43.Native

set_option maxRecDepth 20000

theorem natRec_sum (g : ℕ → ℕ) :
    ∀ n, (Nat.rec (motive := fun _ => ℕ) 0 (fun y acc => acc + g y) n : ℕ) =
      ∑ y ∈ Finset.range n, g y
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← natRec_sum g n]

theorem cntRow_eq (f : ℕ → ℕ → Bool) (x : ℕ) :
    cntRow f x = ∑ y ∈ Finset.range 81, if f x y then 1 else 0 :=
  natRec_sum (fun y => if f x y then 1 else 0) 81

theorem cnt2_eq (f : ℕ → ℕ → Bool) :
    cnt2 f = ((Finset.range 81 ×ˢ Finset.range 81).filter fun p => f p.1 p.2 = true).card := by
  have e : cnt2 f = ∑ x ∈ Finset.range 81, cntRow f x := natRec_sum (cntRow f) 81
  rw [e, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => cntRow_eq f x

@[expose] def rowc (c k : ℕ) : ℕ := c / 81 ^ k % 81

@[irreducible] noncomputable def enc (g : G) : ℕ :=
  encode (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))

theorem enc_mem (g : G) : enc g ∈ spCodes () := by
  rw [enc]
  exact encode_mem_spCodes g

theorem ofCode_enc (g : G) : ofCode (enc g) = g := by
  rw [enc]
  exact ofCode_encode g

private theorem mem_spCodes_iff' (c : ℕ) :
    c ∈ spCodes () ↔ ∃ r0 r1 r2 r3, r0 < 81 ∧ r1 < 81 ∧ r2 < 81 ∧ r3 < 81 ∧
      omg r2 r3 = 0 ∧ omg r1 r2 = 0 ∧ omg r1 r3 = 2 ∧ omg r0 r1 = 0 ∧ omg r0 r2 = 2 ∧
      omg r0 r3 = 0 ∧ c = r0 + 81 * r1 + 6561 * r2 + 531441 * r3 := by
  simp only [spCodes, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_range,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨r3, h3, r2, ⟨h2, h23⟩, r1, ⟨h1, h12, h13⟩, r0, ⟨h0, ⟨h01, h02⟩, h03⟩, rfl⟩
    exact ⟨r0, r1, r2, r3, h0, h1, h2, h3, h23, h12, h13, h01, h02, h03, rfl⟩
  · rintro ⟨r0, r1, r2, r3, h0, h1, h2, h3, h23, h12, h13, h01, h02, h03, rfl⟩
    exact ⟨r3, h3, r2, ⟨h2, h23⟩, r1, ⟨h1, h12, h13⟩, r0, ⟨h0, ⟨h01, h02⟩, h03⟩, rfl⟩

theorem rows_of_mem {c : ℕ} (h : c ∈ spCodes ()) :
    rowc c 0 < 81 ∧ rowc c 1 < 81 ∧ rowc c 2 < 81 ∧ rowc c 3 < 81 ∧
      omg (rowc c 2) (rowc c 3) = 0 ∧ omg (rowc c 1) (rowc c 2) = 0 ∧
      omg (rowc c 1) (rowc c 3) = 2 ∧ omg (rowc c 0) (rowc c 1) = 0 ∧
      omg (rowc c 0) (rowc c 2) = 2 ∧ omg (rowc c 0) (rowc c 3) = 0 ∧
      c = rowc c 0 + 81 * rowc c 1 + 6561 * rowc c 2 + 531441 * rowc c 3 := by
  obtain ⟨r0, r1, r2, r3, h0, h1, h2, h3, h23, h12, h13, h01, h02, h03, rfl⟩ :=
    (mem_spCodes_iff' c).1 h
  have e0 : rowc (r0 + 81 * r1 + 6561 * r2 + 531441 * r3) 0 = r0 := by simp [rowc]; omega
  have e1 : rowc (r0 + 81 * r1 + 6561 * r2 + 531441 * r3) 1 = r1 := by simp [rowc]; omega
  have e2 : rowc (r0 + 81 * r1 + 6561 * r2 + 531441 * r3) 2 = r2 := by simp [rowc]; omega
  have e3 : rowc (r0 + 81 * r1 + 6561 * r2 + 531441 * r3) 3 = r3 := by simp [rowc]; omega
  rw [e0, e1, e2, e3]
  exact ⟨h0, h1, h2, h3, h23, h12, h13, h01, h02, h03, rfl⟩

private theorem dig_row (c i j : ℕ) (hj : j < 4) : dig (c / 81 ^ i % 81) j = ent c i j := by
  have h : 3 ^ (4 * i + j) = 81 ^ i * 3 ^ j := by
    rw [pow_add, pow_mul]
    norm_num
  simp only [ent, dig, h, ← Nat.div_div_eq_div_mul]
  generalize c / 81 ^ i = t
  interval_cases j <;> omega

private theorem ix_lt (a : Fin 2 ⊕ Fin 2) : ix a < 4 := by
  rcases a with i | i <;> simp only [ix] <;> omega

private theorem ix_idx {k : ℕ} (hk : k < 4) : ix (idx k) = k := by
  unfold idx
  split_ifs with h <;> simp [ix]
  omega

theorem toV_rowc (g : G) {k : ℕ} (hk : k < 4) :
    toV (rowc (enc g) k) = (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) (idx k) := by
  funext a
  have e : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) (idx k) a =
      toM (enc g) (idx k) a := by
    rw [enc, toM_encode]
  rw [e]
  simp only [toV, toM, rowc, dig_row _ _ _ (ix_lt a), ix_idx hk]

theorem rowc_lt (c k : ℕ) : rowc c k < 81 := Nat.mod_lt _ (by norm_num)

theorem rowc_mul {g g' : G} {k : ℕ} (hk : k < 4) (h : rowc (enc g) k = rowc (enc g') k)
    (s : G) : rowc (enc (g * s)) k = rowc (enc (g' * s)) k := by
  have hr : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) (idx k) =
      (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) (idx k) := by
    rw [← toV_rowc g hk, ← toV_rowc g' hk, h]
  apply eq_of_toV_eq (rowc_lt _ _) (rowc_lt _ _)
  rw [toV_rowc _ hk, toV_rowc _ hk, Submonoid.coe_mul, Submonoid.coe_mul]
  funext b
  simp only [Matrix.mul_apply', hr]

@[irreducible] noncomputable def psi (g : G) : ℕ × ℕ := (rowc (enc g) 0, rowc (enc g) 2)

@[expose] def xSet : Finset (ℕ × ℕ) :=
  (Finset.range 81 ×ˢ Finset.range 81).filter fun p => xCond p.1 p.2 = true

@[expose] def hSet : Finset (ℕ × ℕ) :=
  (Finset.range 81 ×ˢ Finset.range 81).filter fun p => hCond p.1 p.2 = true

private theorem oneC_mem_spCodes : oneC ∈ spCodes () :=
  (mem_spCodes_iff _).2 ⟨by decide, symp_oneC⟩

theorem enc_one : enc 1 = oneC := by
  apply ofCode_injOn (enc_mem 1) oneC_mem_spCodes
  rw [ofCode_enc, ofCode_oneC]

private theorem rowc_oneC : rowc oneC 0 = 1 ∧ rowc oneC 2 = 9 := by
  constructor <;> decide

theorem psi_one : psi 1 = (1, 9) := by
  rw [psi, enc_one, rowc_oneC.1, rowc_oneC.2]

theorem psi_mem (g : G) : psi g ∈ xSet := by
  obtain ⟨h0, -, h2, -, -, -, -, -, h02, -⟩ := rows_of_mem (enc_mem g)
  rw [psi]
  simp only [xSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, xCond, beq_iff_eq]
  exact ⟨⟨h0, h2⟩, h02⟩

abbrev Stab : Type := {h : G // psi h = (1, 9)}

theorem card_stab_le : Nat.card Stab ≤ hSet.card := by
  have hmem : ∀ h : Stab, (rowc (enc h.1) 1, rowc (enc h.1) 3) ∈ hSet := by
    rintro ⟨h, hh⟩
    rw [psi, Prod.mk.injEq] at hh
    obtain ⟨-, h1, -, h3, h23, h12, h13, h01, h02, h03, -⟩ := rows_of_mem (enc_mem h)
    rw [hh.1] at h01 h02 h03
    rw [hh.2] at h23 h12 h02
    simp only [hSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, hCond,
      Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨h1, h3⟩, ⟨⟨⟨⟨⟨h23, h12⟩, h13⟩, h01⟩, h02⟩, h03⟩⟩
  have hinj : Function.Injective fun h : Stab => (⟨_, hmem h⟩ : hSet) := by
    rintro ⟨h, hh⟩ ⟨h', hh'⟩ e
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at e
    have hc := (rows_of_mem (enc_mem h)).2.2.2.2.2.2.2.2.2.2
    have hc' := (rows_of_mem (enc_mem h')).2.2.2.2.2.2.2.2.2.2
    rw [psi, Prod.mk.injEq] at hh hh'
    have ee : enc h = enc h' := by omega
    apply Subtype.ext
    calc h = ofCode (enc h) := (ofCode_enc h).symm
      _ = ofCode (enc h') := congrArg ofCode ee
      _ = h' := ofCode_enc h'
  calc Nat.card Stab ≤ Nat.card hSet := Nat.card_le_card_of_injective _ hinj
    _ = hSet.card := Nat.card_eq_finsetCard _

private theorem psi_mul_inv {g t : G} (h : psi t = psi g) : psi (g * t⁻¹) = (1, 9) := by
  rw [psi, psi, Prod.mk.injEq] at h
  have e0 := rowc_mul (by norm_num) h.1.symm t⁻¹
  have e2 := rowc_mul (by norm_num) h.2.symm t⁻¹
  rw [mul_inv_cancel] at e0 e2
  rw [← psi_one, psi, psi, e0, e2]

theorem card_G_le : Nat.card G ≤ xSet.card * hSet.card := by
  classical
  let s : ℕ × ℕ → G := fun p => if h : ∃ g, psi g = p then Classical.choose h else 1
  have hs : ∀ g, psi (s (psi g)) = psi g := by
    intro g
    have h : ∃ g', psi g' = psi g := ⟨g, rfl⟩
    simp only [s, dif_pos h]
    exact Classical.choose_spec h
  let f : G → xSet × Stab := fun g =>
    (⟨psi g, psi_mem g⟩, ⟨g * (s (psi g))⁻¹, psi_mul_inv (hs g)⟩)
  have hinj : Function.Injective f := by
    intro g g' e
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    rw [e1] at e2
    exact mul_right_cancel e2
  calc Nat.card G ≤ Nat.card (xSet × Stab) := Nat.card_le_card_of_injective f hinj
    _ = xSet.card * Nat.card Stab := by rw [Nat.card_prod, Nat.card_eq_finsetCard]
    _ ≤ xSet.card * hSet.card := Nat.mul_le_mul_left _ card_stab_le

theorem card_G_le_of_cnt (hx : cnt2 xCond = 2160) (hh : cnt2 hCond = 24) :
    Nat.card G ≤ 51840 := by
  have ex : xSet.card = 2160 := by rw [← hx, cnt2_eq, xSet]
  have eh : hSet.card = 24 := by rw [← hh, cnt2_eq, hSet]
  have := card_G_le
  rw [ex, eh] at this
  exact this

end CFSG.KC.Sp43K

end
