module

public import CFSG.Certificates.Kernel.BabyMonster.Sound

public section

namespace CFSG.KC.BM

open CFSG.KC.BM.SL CFSG.KC.YModel

@[expose] def StripBits (n s a : Nat) : Prop :=
  ∀ q, a.testBit q = true → q < 64 * n ∧ q % 64 < rowsSn n s

theorem stripBits_mulSn {n s : Nat} (Bs : List Nat) {a : Nat} (ha : StripBits n s a) :
    StripBits n s (mulSn n Bs a) := by
  intro q hq
  have ht : q % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hq' : q = 64 * (q / 64) + q % 64 := (Nat.div_add_mod q 64).symm
  have hb := mulSn_bit n Bs a (q / 64) (q % 64) ht
  rw [← hq', hq, bz_true] at hb
  have hj : q / 64 < n := by
    by_contra hj
    rw [decide_eq_false hj, bz_false, mul_zero] at hb
    exact absurd hb (by decide)
  have hr : q % 64 < rowsSn n s := by
    by_contra hr
    have h0 : ∀ k ∈ Finset.range (64 * Bs.length),
        bz (a.testBit (64 * k + q % 64)) * bz ((Bs.getD (k / 64) 0).testBit (64 * (q / 64) + k % 64))
          = 0 := by
      intro k _
      cases hk : a.testBit (64 * k + q % 64)
      · rw [bz_false, zero_mul]
      · have := (ha _ hk).2
        rw [Nat.mul_add_mod_self_left, Nat.mod_mod] at this
        exact absurd this hr
    rw [Finset.sum_eq_zero h0, zero_mul] at hb
    exact absurd hb (by decide)
  refine ⟨?_, hr⟩
  omega

theorem stripBits_mulWn {n s : Nat} : ∀ (Ws : List (List Nat)) {a : Nat}, StripBits n s a →
    StripBits n s (mulWn n Ws a)
  | [], _, ha => ha
  | B :: Ws, a, ha => by
    rw [mulWn_cons]
    exact stripBits_mulWn Ws (stripBits_mulSn B ha)

theorem wfMatn_of_stripBits {n : Nat} {M : List Nat} (hl : M.length = 69)
    (h : ∀ s < 69, StripBits n s (M.getD s 0)) : wfMatn n M = true := by
  change Nat.beq (wfFold (fun T s => Nat.beq (Nat.land T (Nat.mul (SMn n)
    (Nat.sub (Nat.shiftLeft 1 (rowsSn n s)) 1))) T) M 0) 69 = true
  rw [wfFold_of _ M 0 (fun i hi => ?_), Nat.zero_add, hl]
  · exact Nat.beq_refl 69
  · change Nat.beq (Nat.land (M.getD i 0) (Nat.mul (SMn n)
      (Nat.sub (Nat.shiftLeft 1 (rowsSn n (0 + i))) 1))) (M.getD i 0) = true
    rw [Nat.zero_add]
    have e : Nat.land (M.getD i 0) (Nat.mul (SMn n) (Nat.sub (Nat.shiftLeft 1 (rowsSn n i)) 1)) =
        M.getD i 0 := by
      apply Nat.eq_of_testBit_eq
      intro q
      rw [nland, Nat.testBit_and, testBit_mask n _ q (by rw [rowsSn_eq]; omega)]
      cases hq : (M.getD i 0).testBit q
      · rfl
      · obtain ⟨h1, h2⟩ := h i (by omega) q hq
        simp [h1, h2]
    rw [e]
    exact Nat.beq_refl _

theorem wfMat_of_allStrips {Ws : List (List Nat)} {A C : List Nat} (hA : wfMat A = true)
    (h : AllStrips Ws A C) : wfMat C = true := by
  rw [allStrips_spec h]
  rw [wfMat_eq] at hA ⊢
  obtain ⟨hl, hb⟩ := wf_bit hA
  refine wfMatn_of_stripBits (by rw [List.length_map, hl]) (fun s hs => ?_)
  rw [getD_map_of_lt (by omega)]
  apply stripBits_mulWn
  intro q hq
  rw [← lget_eq] at hq
  exact hb s q hq

theorem stripMat_mul1 {A B C : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : stripMat A * stripMat B = stripMat C := by
  have e := stripMat_mul_of_allStrips (Ws := [B]) (by simpa using hB) hA h
  rwa [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e

theorem stripMat_mul1_one {A B : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : stripMat A * stripMat B = 1 := by
  have e := stripMat_mul_eq_one (Ws := [B]) (by simpa using hB) hA h
  rwa [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e

end CFSG.KC.BM

end
