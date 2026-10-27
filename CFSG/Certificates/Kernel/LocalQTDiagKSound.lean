module

public import CFSG.Certificates.Kernel.LocalQTLatKSound
public import CFSG.Certificates.Kernel.LocalQTChainMSound
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso
import all CFSG.Certificates.Kernel.LocalQTBfsKSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n₁ n₂ : ℕ}

theorem pk_eq (n a b : ℕ) : pk n a b = a + b * 2 ^ (5 * n) := by
  change a + b <<< (5 * n) = _
  rw [Nat.shiftLeft_eq]

theorem rnc_lt (hn : n₁ ≤ 32) (r : RN n₁) : rnc r < 2 ^ (5 * n₁) := by
  have h32 : (2 : ℕ) ^ (5 * n₁) = 32 ^ n₁ := by
    rw [pow_mul]
    norm_num
  rw [h32]
  unfold rnc
  exact P.E_lt (rdig_lt hn r)

theorem land_pk (n b : ℕ) {a : ℕ} (ha : a < 2 ^ (5 * n)) :
    Nat.land (pk n a b) (Nat.sub (Nat.shiftLeft 1 (Nat.mul 5 n)) 1) = a := by
  change pk n a b &&& (1 <<< (5 * n) - 1) = a
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, pk_eq, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt ha]

theorem shr_pk (n b : ℕ) {a : ℕ} (ha : a < 2 ^ (5 * n)) :
    Nat.shiftRight (pk n a b) (Nat.mul 5 n) = b := by
  change pk n a b >>> (5 * n) = b
  rw [Nat.shiftRight_eq_div_pow, pk_eq, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt ha, Nat.zero_add]

@[expose] noncomputable def pcode (n₁ n₂ : ℕ) (p : RN n₁ × RN n₂) : ℕ := pk n₁ (rnc p.1) (rnc p.2)

theorem pcode_inj (h₁ : n₁ ≤ 32) (h₂ : n₂ ≤ 32) : Function.Injective (pcode n₁ n₂) := by
  intro p q e
  have e1 := congrArg (fun x => Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.mul 5 n₁)) 1)) e
  have e2 := congrArg (fun x => Nat.shiftRight x (Nat.mul 5 n₁)) e
  simp only [pcode] at e1 e2
  rw [land_pk _ _ (rnc_lt h₁ _), land_pk _ _ (rnc_lt h₁ _)] at e1
  rw [shr_pk _ _ (rnc_lt h₁ _), shr_pk _ _ (rnc_lt h₁ _)] at e2
  exact Prod.ext (rnc_inj h₁ e1) (rnc_inj h₂ e2)

theorem pcode_mul (h₁ : n₁ ≤ 32) (h₂ : n₂ ≤ 32) (p q : RN n₁ × RN n₂) :
    pcode n₁ n₂ (p * q) = pairMul n₁ n₂ (pcode n₁ n₂ p) (pcode n₁ n₂ q) := by
  unfold pairMul pcode
  rw [strictN_eq, land_pk _ _ (rnc_lt h₁ _), land_pk _ _ (rnc_lt h₁ _), shr_pk _ _ (rnc_lt h₁ _),
    shr_pk _ _ (rnc_lt h₁ _), ← rnc_mul h₁, ← rnc_mul h₂]
  rfl

theorem pcode_one : pcode n₁ n₂ 1 = pk n₁ (P.one n₁) (P.one n₂) := by
  unfold pcode
  rw [← rnc_one, ← rnc_one]
  rfl

theorem zipK_eq (n : ℕ) : ∀ (A B : List ℕ), zipK n A B = (A.zip B).map fun p => pk n p.1 p.2
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: A, b :: B => by
    change pk n a b :: zipK n A B = _
    rw [zipK_eq n A B, List.zip_cons_cons, List.map_cons]

theorem zipK_code (A : List (Perm (Fin n₁))) (B : List (Perm (Fin n₂))) :
    zipK n₁ (A.map P.code) (B.map P.code) =
      ((A.zip B).map fun p => (RN.enc p.1, RN.enc p.2)).map (pcode n₁ n₂) := by
  rw [zipK_eq, List.zip_map, List.map_map, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, pcode, rnc_enc, Prod.map_fst, Prod.map_snd]

theorem diag_sound (h₁ : n₁ ≤ 32) (h₂ : n₂ ≤ 32) {d N : ℕ}
    (A : List (Perm (Fin n₁))) (B : List (Perm (Fin n₂)))
    (h : diagK n₁ n₂ d (A.map P.code) (B.map P.code) N = true) :
    diagOK (RN.enc : Perm (Fin n₁) → RN n₁)
      (RN.enc : Perm (Fin n₂) → RN n₂) d A B N = true := by
  unfold diagK at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff, and_true] at h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h
  rw [LK.closedK_iff h₁] at c1
  rw [LK.closedK_iff h₂] at c3
  rw [P.beq_iff, LK.sizeK_eq h₁] at c2
  rw [P.beq_iff, LK.sizeK_eq h₂] at c4
  rw [P.beq_iff, LK.lenA_eq, LK.lenA_eq, List.length_map, List.length_map] at c7
  have hR := rep_bfs (pcode_inj h₁ h₂) (pairMul n₁ n₂) (pcode_mul h₁ h₂)
    ((A.zip B).map fun p => (RN.enc p.1, RN.enc p.2)) d
  rw [← zipK_code, pcode_one] at hR
  have e5 := closedG_eq (pcode_inj h₁ h₂) (pairMul n₁ n₂) (pcode_mul h₁ h₂)
    ((A.zip B).map fun p => (RN.enc p.1, RN.enc p.2)) hR
  rw [← zipK_code, pcode_one] at e5
  rw [e5] at c5
  rw [P.beq_iff, rep_size hR] at c6
  unfold diagOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩

end CFSG.KC.LQT.CM

end
