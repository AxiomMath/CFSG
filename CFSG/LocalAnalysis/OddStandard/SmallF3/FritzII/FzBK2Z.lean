module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzBU CFSG.OddStandard.SmallF3.HarrisU33

private theorem fzb_xor_lt_four {a b : ℕ} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := by
  have h := Nat.xor_lt_two_pow (n := 2) (x := a) (y := b) (by omega) (by omega)
  change a ^^^ b < 2 ^ 2 at h
  exact h

private theorem fzb_f4mul_lt (a b : ℕ) : f4mul a b < 4 := by
  unfold f4mul
  have h1 : (a % 2 * (b % 2) + a / 2 * (b / 2)) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : (a % 2 * (b / 2) + a / 2 * (b % 2) + a / 2 * (b / 2)) % 2 < 2 :=
    Nat.mod_lt _ (by norm_num)
  omega

theorem fzb_uMul_sq_lt {x : ℕ} (hx : x < 64) : uMul x x < 4 := by
  have h := fzb_f4mul_lt (x / 16) (x / 4 % 4)
  unfold uMul
  simpa using h

theorem fzb_uMul_Z_lt {x y : ℕ} (hx : x < 4) (hy : y < 4) : uMul x y < 4 := by
  have hx16 : x / 16 = 0 := by omega
  have hy16 : y / 16 = 0 := by omega
  have hx4 : x / 4 % 4 = 0 := by omega
  have hy4 : y / 4 % 4 = 0 := by omega
  have hxr : x % 4 = x := Nat.mod_eq_of_lt hx
  have hyr : y % 4 = y := Nat.mod_eq_of_lt hy
  have hf : f4mul 0 0 = 0 := by decide +kernel
  unfold uMul
  simp only [hx16, hy16, hx4, hy4, hxr, hyr, hf, Nat.xor_self, Nat.zero_xor, Nat.xor_zero,
    Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  exact fzb_xor_lt_four hx hy

theorem fzb_uMul_Z_sq {x : ℕ} (hx : x < 4) : uMul x x = 0 := by
  have hx16 : x / 16 = 0 := by omega
  have hx4 : x / 4 % 4 = 0 := by omega
  have hxr : x % 4 = x := Nat.mod_eq_of_lt hx
  have hf : f4mul 0 0 = 0 := by decide +kernel
  unfold uMul
  simp only [hx16, hx4, hxr, hf, Nat.xor_self, Nat.zero_xor, Nat.xor_zero, Nat.mul_zero,
    Nat.add_zero, Nat.zero_add]

theorem fzb_Z_code {G : Type} [Group G] {P : Subgroup G} (C : FzbCoding P) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ P) (hx₂ : x₂ ∈ P) (hcard : Nat.card ↥(fourGrp x₁ x₂) = 4) :
    ∀ p ∈ P, p ∈ fourGrp x₁ x₂ ↔ C.enc p < 4 := by
  let Zc : Subgroup G :=
    { carrier := {p | p ∈ P ∧ C.enc p < 4}
      one_mem' := ⟨P.one_mem, by rw [C.enc_one]; norm_num⟩
      mul_mem' := by
        rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
        exact ⟨P.mul_mem haP hbP, by
          rw [C.enc_mul a haP b hbP]
          exact fzb_uMul_Z_lt ha hb⟩
      inv_mem' := by
        rintro a ⟨haP, ha⟩
        have hmem : a * a ∈ P := P.mul_mem haP haP
        have henc : C.enc (a * a) = C.enc 1 := by
          rw [C.enc_mul a haP a haP, fzb_uMul_Z_sq ha, C.enc_one]
        have haa : a * a = 1 := C.enc_inj hmem P.one_mem henc
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
        exact ⟨by rw [hinv]; exact haP, by rw [hinv]; exact ha⟩ }
  have hle : fourGrp x₁ x₂ ≤ Zc := by
    rw [fourGrp, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · refine ⟨?_, ?_⟩
      · rw [pow_two]
        exact P.mul_mem hx₁ hx₁
      · rw [pow_two, C.enc_mul x₁ hx₁ x₁ hx₁]
        exact fzb_uMul_sq_lt (C.enc_lt x₁ hx₁)
    · refine ⟨?_, ?_⟩
      · rw [pow_two]
        exact P.mul_mem (P.mul_mem hx₁ hx₂) (P.mul_mem hx₁ hx₂)
      · rw [pow_two, C.enc_mul (x₁ * x₂) (P.mul_mem hx₁ hx₂) (x₁ * x₂)
          (P.mul_mem hx₁ hx₂)]
        exact fzb_uMul_sq_lt (C.enc_lt (x₁ * x₂) (P.mul_mem hx₁ hx₂))
  let e : Zc ≃ Fin 4 :=
    { toFun := fun p => ⟨C.enc p.1, p.2.2⟩
      invFun := fun n =>
        ⟨C.dec n.1, ⟨C.dec_mem n.1 (by omega), by
          rw [C.enc_dec n.1 (by omega)]
          exact n.2⟩⟩
      left_inv := by
        rintro ⟨p, ⟨hpP, hp4⟩⟩
        apply Subtype.ext
        simp only
        exact C.dec_enc p hpP
      right_inv := by
        rintro ⟨n, hn⟩
        apply Fin.ext
        simp only
        exact C.enc_dec n (by omega) }
  have hZc : Nat.card ↥Zc = 4 := Nat.card_eq_of_equiv_fin e
  haveI : Finite ↥Zc := Finite.of_equiv (Fin 4) e.symm
  have hcardZ : Nat.card ↥Zc ≤ Nat.card ↥(fourGrp x₁ x₂) := by omega
  have hEq : fourGrp x₁ x₂ = Zc := Subgroup.eq_of_le_of_card_ge hle hcardZ
  intro p hp
  rw [hEq]
  change p ∈ P ∧ C.enc p < 4 ↔ C.enc p < 4
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

end CFSG.OddStandard.SmallF3.FritzII
