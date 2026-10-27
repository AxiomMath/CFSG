module

public import Certificates.Data.Kernel.Misc.YamakiNAl
public import CFSG.Certificates.Kernel.Misc.YamakiCESound

public section

namespace CFSG.KC.YamakiNA

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiNA
  CFSG.KD.YamakiCE CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0
  CFSG.KC.YamakiA0 CFSG.KC.YamakiCE CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

variable {R : ℕ → ℕ}

theorem commOK_gA0 (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (x : ℕ) :
    commOK (gA0 ()) (arrN x) = comm6 R x := by
  apply Bool.eq_iff_iff.2
  unfold commOK comm6
  rw [allLt_iff, size_gA0, List.all_eq_true]
  constructor
  · intro h j hj
    have hj' := List.mem_range.1 hj
    have e := h j hj'
    rw [gA0_eq hG hj', arrN_mul, arrN_mul,
      decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)] at e
    exact e
  · intro h j hj
    have e := h j (List.mem_range.2 hj)
    rw [gA0_eq hG hj, arrN_mul, arrN_mul,
      decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]
    exact e

theorem centA0Check_of {RA PA PB PAA PBA : ℕ → ℕ} {o : ℕ}
    (hH : BInvE (fun t => arrN (recX R o t)) PA PB 23040 (enumH ()))
    (hA : BInvE (fun t => arrN (recX RA 12 t)) PAA PBA 64 (enumA0 ()))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hc : ∀ q < 45, cA0Chunk R o 23040 RA 512 q = true) : centA0Check () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hH
  simp only [centA0Check, allLt_iff]
  intro i hi
  rw [e1] at hi
  have hq : i / 512 < 45 := by omega
  have hcq := hc _ hq
  unfold cA0Chunk at hcq
  have hlo : Nat.mul 512 (i / 512) ≤ i := Nat.mul_div_le i 512
  have hhi : i < Nat.mul 512 (i / 512) + 512 := by
    change i < 512 * (i / 512) + 512
    omega
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq i hlo hhi
  rw [Nat.blt_eq.mpr hi, cond_true, CFSG.KC.YamakiRepF.strictY_eq] at e
  rw [e4 i hi]
  beta_reduce
  rw [commOK_gA0 hG]
  simp only [Bool.or_eq_true] at e ⊢
  rcases e with h | h
  · exact Or.inl h
  · exact Or.inr (isSome_of_rec hA (memK_sound h))

theorem normA0Check_of {PAA PBA : ℕ → ℕ}
    (hA : BInvE (fun t => arrN (recX R 12 t)) PAA PBA 64 (enumA0 ()))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hn : normA0K R = true) :
    normA0Check () = true := by
  have hN12 : ∀ s ∈ idxN0, s < 12 := by decide
  unfold normA0K at hn
  simp only [normA0Check, List.all_eq_true, allLt_iff] at hn ⊢
  intro s hs j hj
  rw [size_gA0] at hj
  rw [genA_eq12 hG (hN12 s hs), gA0_eq hG hj, arrN_mul, arrN_mul]
  exact isSome_of_rec hA (memK_sound (hn s hs j (List.mem_range.2 hj)))

theorem sevenCheck_of {PAA PBA : ℕ → ℕ}
    (hA : BInvE (fun t => arrN (recX R 12 t)) PAA PBA 64 (enumA0 ()))
    (hlt : ∀ t < 64, recX R 12 t < 2 ^ 36)
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (hs : sevenK R = true) :
    sevenCheck () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hA
  unfold sevenK at hs
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  simp only [sevenCheck, Bool.and_eq_true, allLt_iff]
  rw [wordA_eq hG sevenWord (by decide),
    wordA_eq hG (List.replicate 7 sevenWord).flatten (by decide), ← arrN_one,
    decide_arrN (wordN_lt _) ONE_lt, decide_arrN (wordN_lt _) ONE_lt]
  refine ⟨⟨⟨by decide, h1⟩, h2⟩, fun i hi => ?_⟩
  rw [e1] at hi
  rw [e4 i hi]
  beta_reduce
  rw [arrN_mul, arrN_mul, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _),
    decide_arrN (hlt i hi) ONE_lt]
  exact h3 i hi

theorem alphaClassCheck_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (ha : alphaClassK R = true) : alphaClassCheck () = true := by
  have hw : ∀ c ∈ alphaClassWords, ∀ i ∈ conjWord c [5], i < 12 := by decide
  unfold alphaClassK at ha
  rw [decide_eq_true_eq] at ha
  simp only [alphaClassCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  have e : orbCodes [5] alphaClassWords =
      (alphaClassWords.map fun c => wordN R (conjWord c [5])).map arrN := by
    simp only [orbCodes]
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    exact wordA_eq hG _ (hw c hc)
  rw [e]
  refine ha.map_on fun x hx y hy h => ?_
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hy
  exact arrN_inj (wordN_lt _) (wordN_lt _) h

theorem centAlphaCheck_of {RX PA PB PAX PBX P : ℕ → ℕ} {o oX : ℕ}
    (hN : BInvE (fun t => arrN (recX R o t)) PA PB 10752 (enumN ()))
    (hX : BInvE (fun t => arrN (recX RX oX t)) PAX PBX 1536 (enumX ()))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hlt : ∀ t < 10752, recX R o t < 2 ^ 36) (h5 : R 5 < 2 ^ 36)
    (hc : ∀ q < 21, cAlChunk R o 10752 RX oX 1536 P 512 q = true) : centAlphaCheck () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hN
  simp only [centAlphaCheck, allLt_iff]
  intro i hi
  rw [e1] at hi
  have hq : i / 512 < 21 := by omega
  have hcq := hc _ hq
  unfold cAlChunk at hcq
  rw [CFSG.KC.YamakiRepF.strictY_eq] at hcq
  have hlo : Nat.mul 512 (i / 512) ≤ i := Nat.mul_div_le i 512
  have hhi : i < Nat.mul 512 (i / 512) + 512 := by
    change i < 512 * (i / 512) + 512
    omega
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq i hlo hhi
  rw [Nat.blt_eq.mpr hi, cond_true, CFSG.KC.YamakiRepF.strictY_eq] at e
  rw [e4 i hi]
  beta_reduce
  rw [genA_eq12 hG (by norm_num : 5 < 12), arrN_mul, arrN_mul,
    decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e ⊢
  rcases e with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (isSome_of_rec hX ⟨_, h1, h2⟩)

end CFSG.KC.YamakiNA

end
