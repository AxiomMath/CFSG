module

public import Certificates.Data.Kernel.Misc.YamakiA6N
public import CFSG.Certificates.Kernel.Misc.YamakiA6Sound

public section

namespace CFSG.KC.YamakiA6

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiCE
  CFSG.KD.YamakiA6 CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiCE
open CFSG.KD.Sp62 (MULF ONE)

theorem cS0_eq (Q : ℕ) : cS0 Q = Q / 32768 % 8 + (8 * (Q / 512 % 8) + (64 * (Q / 8 % 8) +
    (512 * (Q / 64 % 8) + (4096 * (Q / 1 % 8) + 32768 * (Q / 4096 % 8))))) := rfl

theorem cS1_eq (Q : ℕ) : cS1 Q = Q / 32768 % 8 + (8 * (Q / 8 % 8) + (64 * (Q / 64 % 8) +
    (512 * (Q / 1 % 8) + (4096 * (Q / 4096 % 8) + 32768 * (Q / 512 % 8))))) := rfl

theorem decL_enc {a b c d e f : ℕ} (ha : a < 8) (hb : b < 8) (hc : c < 8) (hd : d < 8)
    (he : e < 8) (hf : f < 8) :
    decL (a + (8 * b + (64 * c + (512 * d + (4096 * e + 32768 * f))))) = [a, b, c, d, e, f] := by
  unfold decL
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem mod8 (x : ℕ) : x % 8 < 8 := Nat.mod_lt x (by norm_num)

theorem decL_cS0 (Q : ℕ) : decL (cS0 Q) = compL (decL Q) (sigL 0) := by
  have e : compL (decL Q) (sigL 0) =
      [Q / 32768 % 8, Q / 512 % 8, Q / 8 % 8, Q / 64 % 8, Q % 8, Q / 4096 % 8] := rfl
  rw [e, cS0_eq, decL_enc (mod8 _) (mod8 _) (mod8 _) (mod8 _) (mod8 _) (mod8 _), Nat.div_one]

theorem decL_cS1 (Q : ℕ) : decL (cS1 Q) = compL (decL Q) (sigL 1) := by
  have e : compL (decL Q) (sigL 1) =
      [Q / 32768 % 8, Q / 8 % 8, Q / 64 % 8, Q % 8, Q / 4096 % 8, Q / 512 % 8] := rfl
  rw [e, cS1_eq, decL_enc (mod8 _) (mod8 _) (mod8 _) (mod8 _) (mod8 _) (mod8 _), Nat.div_one]

theorem decL_cS (j Q : ℕ) : decL (cS j Q) = compL (decL Q) (sigL j) := by
  cases h : Nat.beq j 0
  · have e1 : cS j Q = cS1 Q := by rw [cS, h, cond_false]
    have e2 : sigL j = sigL 1 := by rw [sigL, sigL, h]; rfl
    rw [e1, e2, decL_cS1]
  · have e1 : cS j Q = cS0 Q := by rw [cS, h, cond_true]
    have e2 : sigL j = sigL 0 := by rw [sigL, sigL, h]; rfl
    rw [e1, e2, decL_cS0]

theorem decL_eq_one_iff {P : ℕ} (hP : P < 262144) : decL P = [0, 1, 2, 3, 4, 5] ↔ P = 181896 := by
  constructor
  · intro h
    unfold decL at h
    simp only [List.cons.injEq, and_true] at h
    omega
  · rintro rfl
    rfl

theorem code_of_memK {RE RP RV PV PA PB : ℕ → ℕ} {E : Enum}
    (hE : BInvE (fun t => arrN (recX RE 14 t)) PA PB 11520 E) (hv : a6VK RE RP RV PV = true)
    {t : ℕ} (ht : t < 11520) (hm : memK RV 17 32 (recX RE 14 t) = true) : RP t = 181896 := by
  obtain ⟨v, hv32, hvx⟩ := memK_sound hm
  have e := List.all_eq_true.1 hv v (List.mem_range.2 hv32)
  simp only [Bool.and_eq_true] at e
  obtain ⟨⟨hp, hx⟩, hid⟩ := e
  have hp' : PV v < 11520 := Nat.blt_eq.mp hp
  have hpx : recX RE 14 (PV v) = recX RE 14 t := (Nat.eq_of_beq_eq_true hx).trans hvx
  obtain ⟨-, -, -, -, -, -, e7⟩ := hE
  have a := e7 _ hp'
  have b := e7 _ ht
  dsimp only at a b
  rw [hpx, b] at a
  rw [Option.some.inj a]
  exact Nat.eq_of_beq_eq_true hid

theorem a6At_of_N {RE RP RV : ℕ → ℕ} {t : ℕ} (h : a6AtN RE RP RV t = true)
    (hback : memK RV 17 32 (recX RE 14 t) = true → RP t = 181896) : a6At RE RP RV t = true := by
  unfold a6AtN at h
  rw [CFSG.KC.YamakiRepF.strictY_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hb, ht⟩, h0⟩, h1⟩, hk⟩ := h
  have hb' : RP t < 262144 := Nat.blt_eq.mp hb
  unfold a6At
  rw [CFSG.KC.YamakiRepF.strictY_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · cases t with
    | zero =>
      have hz : Nat.beq 0 0 = true := rfl
      rw [hz, cond_true] at ht ⊢
      rw [Nat.eq_of_beq_eq_true ht]
      rfl
    | succ t =>
      have hz : Nat.beq (t + 1) 0 = false := rfl
      rw [hz, cond_false] at ht ⊢
      rw [Nat.eq_of_beq_eq_true ht, decL_cS]
      exact decide_eq_true rfl
  · rw [Nat.eq_of_beq_eq_true h0, decL_cS0]
    exact decide_eq_true rfl
  · rw [Nat.eq_of_beq_eq_true h1, decL_cS1]
    exact decide_eq_true rfl
  · have key : decide (decL (RP t) = [0, 1, 2, 3, 4, 5]) = memK RV 17 32 (recX RE 14 t) := by
      apply Bool.eq_iff_iff.2
      rw [decide_eq_true_eq, decL_eq_one_iff hb']
      constructor
      · intro e
        have e' : Nat.beq (RP t) 181896 = true := Nat.beq_eq.mpr e
        rw [e', cond_true] at hk
        exact hk
      · exact hback
    rw [key]
    exact beq_self_eq_true _

theorem a6Check_ofN {RE RP RV PV PAV PBV : ℕ → ℕ}
    (hE : BInvE (fun t => arrN (recX RE 14 t)) (recF RE 14 0) (recF RE 14 1) 11520 (enumE ()))
    (hB : ∀ i < 11520 - 1, recF RE 14 0 i ≤ i ∧ recF RE 14 1 i < 2)
    (hlt : ∀ t < 11520, recX RE 14 t < 2 ^ 36)
    (hstep : ∀ i < 11520 * 2, recPOS RE 14 2 i < 11520 ∧
      recX RE 14 (recPOS RE 14 2 i) = MULF (recX RE 14 (i / 2)) (RE (12 + i % 2)))
    (hg : ∀ j < 2, (gE ())[j]! = arrN (RE (12 + j)))
    (hV : BInvE (fun t => arrN (recX RV 17 t)) PAV PBV 32 (enumV0 ()))
    (hVlt : ∀ t < 32, recX RV 17 t < 2 ^ 36)
    (hc : ∀ q < 23, a6ChunkN RE RP RV 11520 512 q = true) (hv : a6VK RE RP RV PV = true) :
    a6Check () = true := by
  refine a6Check_of (RP := RP) (RV := RV) hE hB hlt hstep hg hV hVlt fun q hq => ?_
  have hcq := hc q hq
  unfold a6ChunkN at hcq
  unfold a6Chunk
  rw [CFSG.KC.Misc.Clos.allR_iff] at hcq ⊢
  intro t hlo hhi
  have e := hcq t hlo hhi
  by_cases ht : t < 11520
  · rw [Nat.blt_eq.mpr ht, cond_true] at e ⊢
    exact a6At_of_N e (code_of_memK hE hv ht)
  · have hf : Nat.blt t 11520 = false := Bool.eq_false_iff.2 fun h => ht (Nat.blt_eq.mp h)
    rw [hf, cond_false]

end CFSG.KC.YamakiA6

end
