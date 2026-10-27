module

public import CFSG.Certificates.Kernel.KStep.Defs
public import CFSG.Certificates.Kernel.KDense.KeysSound

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense

namespace KeyBindAux

open CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.KDense.KeysAux CFSG.KC.KDense.InitAux

theorem testBit_plane {X b p : ℕ} (hp : p < SX) : (plane SX b X).testBit p = X.testBit (b * SX + p) := by
  unfold plane
  rw [nland, nshr, nmul, Nat.testBit_and, Nat.testBit_shiftRight, SortAux.testBit_ones,
    decide_eq_true hp, Bool.and_true, Nat.add_comm]

theorem keyA_bit {F : Fix} {KT : ℕ} (h5 : keyPlanesOK F KT = true) {b p : ℕ} (hb : b < 12)
    (hp : p < SX) : F.keyA.testBit (b * SX + p) = KT.testBit (32 * p + b) := by
  have := keyPlane_bit h5 (by omega : b < 24) hp
  have e : Nat.blt b (nat_lit 12) = true := by simpa using hb
  unfold keyPlane at this
  rw [e] at this
  rw [← testBit_plane hp]
  exact this

theorem keyD_bit {F : Fix} {KT : ℕ} (h5 : keyPlanesOK F KT = true) {b p : ℕ} (hb : b < 12)
    (hp : p < SX) : F.keyD.testBit (b * SX + p) = KT.testBit (32 * p + (b + 12)) := by
  have := keyPlane_bit h5 (by omega : b + 12 < 24) hp
  have e : Nat.blt (b + 12) (nat_lit 12) = false := by
    cases h : Nat.blt (b + 12) (nat_lit 12)
    · rfl
    · simp at h
  unfold keyPlane at this
  rw [e] at this
  have e2 : Nat.sub (b + 12) (nat_lit 12) = b := Nat.add_sub_cancel b 12
  rw [e2] at this
  rw [← testBit_plane hp]
  exact this

theorem fold_lt (KT o : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (rawPlane KT 32 SX 17 0 (o + b)) (Nat.mul b SX))) 12 <
      2 ^ (12 * SX) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [← Bool.not_eq_true, testBit_foldOr (fun b => Nat.shiftLeft (rawPlane KT 32 SX 17 0 (o + b))
    (Nat.mul b SX))]
  rintro (h | ⟨j, hj, h⟩)
  · simp at h
  · rw [testBit_shl, SortAux.testBit_rawPlane (by decide) SortAux.SX_pow, nmul] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    have : i < (j + 1) * SX := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have : (j + 1) * SX ≤ 12 * SX := Nat.mul_le_mul_right _ (by omega)
    omega

theorem keyA_lt {F : Fix} {KT : ℕ} (h5 : keyPlanesOK F KT = true) : F.keyA < 2 ^ (12 * SX) := by
  obtain ⟨hA, -⟩ := andB_true h5
  rw [Nat.eq_of_beq_eq_true hA]
  have := fold_lt KT 0
  simp only [Nat.zero_add] at this
  exact this

theorem keyD_lt {F : Fix} {KT : ℕ} (h5 : keyPlanesOK F KT = true) : F.keyD < 2 ^ (12 * SX) := by
  obtain ⟨-, hD⟩ := andB_true h5
  rw [Nat.eq_of_beq_eq_true hD]
  have := fold_lt KT 12
  simp only [Nat.add_comm 12] at this
  exact this

end KeyBindAux

open KeyBindAux InitAux in
theorem keyBind_of {F : Fix} {KT TH OCT DU1 : ℕ} (h1 : thOK TH = true) (h2 : octOK OCT = true)
    (h3 : du1OK DU1 = true) (h4 : keysOK TH OCT DU1 KT = true) (h5 : keyPlanesOK F KT = true) :
    KeyBind F := by
  have hk := keysOK_sound TH OCT DU1 KT h1 h2 h3 h4
  refine ⟨fun q hq b hb => ?_, fun q hq b hb => ?_, fun p hp hn b hb => ?_,
    fun p hp hn b hb => ?_, keyA_lt h5, keyD_lt h5⟩
  · rw [keyA_bit h5 hb (xposK_lt' hq), keyQ, hk q hq, ← KeysAux.testBit_keyRecAt _ _ _ (by omega)]
    change _ = (keyRecAt KT (xposK q) % 2 ^ 12).testBit b
    rw [Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and]
  · rw [keyD_bit h5 hb (xposK_lt' hq), keyQ, hk q hq, ← KeysAux.testBit_keyRecAt _ _ _ (by omega)]
    change _ = (keyRecAt KT (xposK q) / 2 ^ 12 % 2 ^ 12).testBit b
    rw [Nat.testBit_mod_two_pow, decide_eq_true hb, Bool.true_and, Nat.testBit_div_two_pow]
  · rw [keyA_bit h5 hb hp]
    exact keysOK_pad h4 hp hn (by omega)
  · rw [keyD_bit h5 hb hp]
    exact keysOK_pad h4 hp hn (by omega)

end CFSG.KC.KStep

end
