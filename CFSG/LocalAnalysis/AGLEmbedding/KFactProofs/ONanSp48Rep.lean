module

public import Certificates.Data.ONanSp48Code

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin

theorem ofNat_mulNat {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    GF8.ofNat' (GF8.mulNat a b) = GF8.ofNat' a * GF8.ofNat' b := by
  show _ = GF8.ofNat' (GF8.mulNat (GF8.ofNat' a).toNat (GF8.ofNat' b).toNat)
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem mulNat_lt {a b : ℕ} (ha : a < 8) (hb : b < 8) : GF8.mulNat a b < 8 := by
  have h : ∀ a : Fin 8, ∀ b : Fin 8, GF8.mulNat a b < 8 := by decide
  exact h ⟨a, ha⟩ ⟨b, hb⟩

theorem xor_lt8 {a b : ℕ} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 :=
  Nat.xor_lt_two_pow (n := 3) ha hb

theorem ofNat_xor {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    GF8.ofNat' (a ^^^ b) = GF8.ofNat' a + GF8.ofNat' b := by
  show _ = GF8.ofNat' ((GF8.ofNat' a).toNat ^^^ (GF8.ofNat' b).toNat)
  simp [GF8.ofNat', GF8.toNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_xor4 {a b c d : ℕ} (ha : a < 8) (hb : b < 8) (hc : c < 8) (hd : d < 8) :
    GF8.ofNat' (a ^^^ b ^^^ c ^^^ d) =
      GF8.ofNat' a + GF8.ofNat' b + GF8.ofNat' c + GF8.ofNat' d := by
  have hab := xor_lt8 ha hb
  have habc := xor_lt8 hab hc
  rw [ofNat_xor habc hd, ofNat_xor hab hc, ofNat_xor ha hb]

theorem ofNat_inj {x y : ℕ} (hx : x < 8) (hy : y < 8) (h : GF8.ofNat' x = GF8.ofNat' y) :
    x = y := by
  simp only [GF8.ofNat', GF8.mk.injEq, Fin.mk.injEq, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy] at h
  exact h

@[expose] def ix : Fin 2 ⊕ Fin 2 → ℕ
  | .inl i => i.val
  | .inr i => 2 + i.val

theorem ix_lt (i : Fin 2 ⊕ Fin 2) : ix i < 4 := by
  rcases i with i | i <;> simp only [ix] <;> omega

theorem ix_injective : Function.Injective ix := by
  rintro (i | i) (j | j) h <;> simp only [ix] at h <;> first | omega | (congr 1; ext; omega)

@[expose] def decode (A : Array ℕ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF8 :=
  Matrix.of fun i j => GF8.ofNat' A[4 * ix i + ix j]!

@[expose] def Valid (A : Array ℕ) : Prop := A.size = 16 ∧ ∀ i < 16, A[i]! < 8

theorem validB_iff {A : Array ℕ} : validB A = true ↔ Valid A := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Valid]

theorem getElem!_ofFn {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem idx_lt (i j : Fin 2 ⊕ Fin 2) : 4 * ix i + ix j < 16 := by
  have := ix_lt i; have := ix_lt j; omega

theorem valid_idCode : Valid idCode := by
  refine ⟨by simp [idCode], fun i hi => ?_⟩
  rw [idCode, getElem!_ofFn _ hi]
  split_ifs <;> norm_num

theorem decode_idCode : decode idCode = 1 := by
  ext i j
  simp only [decode, Matrix.of_apply, idCode]
  rw [getElem!_ofFn _ (idx_lt i j)]
  have h1 : (4 * ix i + ix j) / 4 = ix i := by have := ix_lt j; omega
  have h2 : (4 * ix i + ix j) % 4 = ix j := by have := ix_lt j; omega
  simp only [h1, h2, Matrix.one_apply]
  split_ifs with ha hb hb
  · rfl
  · exact absurd (ix_injective ha) hb
  · exact absurd (hb ▸ rfl) ha
  · rfl

theorem valid_mulCode {A B : Array ℕ} (hA : Valid A) (hB : Valid B) : Valid (mulCode A B) := by
  refine ⟨by simp [mulCode], fun t ht => ?_⟩
  rw [mulCode, getElem!_ofFn _ ht, mulEntry]
  have a := hA.2; have b := hB.2
  have ht4 : t / 4 < 4 := by omega
  have hr : t % 4 < 4 := by omega
  refine xor_lt8 (xor_lt8 (xor_lt8 (mulNat_lt (a _ (by omega)) (b _ (by omega)))
    (mulNat_lt (a _ (by omega)) (b _ (by omega)))) (mulNat_lt (a _ (by omega))
    (b _ (by omega)))) (mulNat_lt (a _ (by omega)) (b _ (by omega)))

theorem valid_frobCode {A : Array ℕ} (hA : Valid A) : Valid (frobCode A) := by
  refine ⟨by simp [frobCode], fun t ht => ?_⟩
  rw [frobCode, getElem!_ofFn _ ht]
  exact mulNat_lt (hA.2 t ht) (hA.2 t ht)

theorem valid_frobPow (n : ℕ) {A : Array ℕ} (hA : Valid A) : Valid (frobPow n A) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact valid_frobCode ih

theorem ix_inl (i : Fin 2) : ix (.inl i) = i.val := rfl

theorem ix_inr (i : Fin 2) : ix (.inr i) = 2 + i.val := rfl

theorem ofNat_mulEntry {A B : Array ℕ} (hA : Valid A) (hB : Valid B) {r c : ℕ} (hr : r < 4)
    (hc : c < 4) :
    GF8.ofNat' (mulEntry A B r c) =
      GF8.ofNat' A[4 * r]! * GF8.ofNat' B[c]! + GF8.ofNat' A[4 * r + 1]! * GF8.ofNat' B[4 + c]! +
        GF8.ofNat' A[4 * r + 2]! * GF8.ofNat' B[8 + c]! +
        GF8.ofNat' A[4 * r + 3]! * GF8.ofNat' B[12 + c]! := by
  have a := hA.2; have b := hB.2
  rw [mulEntry, ofNat_xor4 (mulNat_lt (a _ (by omega)) (b _ (by omega)))
    (mulNat_lt (a _ (by omega)) (b _ (by omega))) (mulNat_lt (a _ (by omega)) (b _ (by omega)))
    (mulNat_lt (a _ (by omega)) (b _ (by omega))), ofNat_mulNat (a _ (by omega)) (b _ (by omega)),
    ofNat_mulNat (a _ (by omega)) (b _ (by omega)), ofNat_mulNat (a _ (by omega)) (b _ (by omega)),
    ofNat_mulNat (a _ (by omega)) (b _ (by omega))]

theorem decode_mulCode {A B : Array ℕ} (hA : Valid A) (hB : Valid B) :
    decode (mulCode A B) = decode A * decode B := by
  ext i j
  have hlt := idx_lt i j
  have hi := ix_lt i; have hj := ix_lt j
  simp only [decode, Matrix.of_apply, mulCode]
  rw [getElem!_ofFn _ hlt]
  have h1 : (4 * ix i + ix j) / 4 = ix i := by omega
  have h2 : (4 * ix i + ix j) % 4 = ix j := by omega
  simp only [h1, h2]
  rw [ofNat_mulEntry hA hB hi hj, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp only [Matrix.of_apply, ix_inl, ix_inr, Fin.val_zero, Fin.val_one]
  have e0 : 4 * 0 + ix j = ix j := by omega
  have e1 : 4 * 1 + ix j = 4 + ix j := by omega
  have e2 : 4 * (2 + 0) + ix j = 8 + ix j := by omega
  have e3 : 4 * (2 + 1) + ix j = 12 + ix j := by omega
  simp only [e0, e1, e2, e3, Nat.add_zero, add_assoc]

theorem decode_frobCode {A : Array ℕ} (hA : Valid A) :
    decode (frobCode A) = (decode A).map fun a => a * a := by
  ext i j
  have hlt := idx_lt i j
  simp only [decode, Matrix.of_apply, frobCode, Matrix.map_apply]
  rw [getElem!_ofFn _ hlt]
  exact ofNat_mulNat (hA.2 _ hlt) (hA.2 _ hlt)

theorem decode_inj {A B : Array ℕ} (hA : Valid A) (hB : Valid B) (h : decode A = decode B) :
    A = B := by
  apply Array.ext (hA.1.trans hB.1.symm)
  intro t h1 _
  have ht : t < 16 := by simpa [hA.1] using h1
  have key : ∀ r c : Fin 2 ⊕ Fin 2, A[4 * ix r + ix c]! = B[4 * ix r + ix c]! := by
    intro r c
    have := congrFun (congrFun h r) c
    simp only [decode, Matrix.of_apply] at this
    exact ofNat_inj (hA.2 _ (idx_lt r c)) (hB.2 _ (idx_lt r c)) this
  have hr : ∃ r c : Fin 2 ⊕ Fin 2, t = 4 * ix r + ix c := by
    have h4 : t / 4 < 4 := by omega
    have h5 : t % 4 < 4 := by omega
    have surj : ∀ n < 4, ∃ r : Fin 2 ⊕ Fin 2, ix r = n := by
      intro n hn
      interval_cases n
      · exact ⟨.inl 0, rfl⟩
      · exact ⟨.inl 1, rfl⟩
      · exact ⟨.inr 0, rfl⟩
      · exact ⟨.inr 1, rfl⟩
    obtain ⟨r, hr⟩ := surj _ h4
    obtain ⟨c, hc⟩ := surj _ h5
    exact ⟨r, c, by omega⟩
  obtain ⟨r, c, rfl⟩ := hr
  have := key r c
  rwa [getElem!_pos A _ (by simp [hA.1]; exact idx_lt r c),
    getElem!_pos B _ (by simp [hB.1]; exact idx_lt r c)] at this

end CFSG.AGLEmbedding.KFactProofs.Sp48
