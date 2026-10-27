module

public import Certificates.Data.Kernel.Misc.YamakiNO
public import Certificates.Data.Kernel.Misc.YamakiNS
public import CFSG.Certificates.Kernel.Misc.YamakiA6Sound

public section

namespace CFSG.KC.YamakiNO

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiNA
  CFSG.KD.YamakiCE CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0
  CFSG.KC.YamakiA0 CFSG.KC.YamakiCE CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

variable {R : ℕ → ℕ}

theorem orbCodes_eq (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {x : List ℕ}
    {cs : List (List ℕ)} (hw : ∀ c ∈ cs, ∀ i ∈ conjWord c x, i < 12) :
    orbCodes x cs = (orbN R x cs).map arrN := by
  simp only [orbCodes, orbN]
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact wordA_eq hG _ (hw c hc)

theorem orbN_lt (x : List ℕ) (cs : List (List ℕ)) : ∀ y ∈ orbN R x cs, y < 2 ^ 36 := by
  intro y hy
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
  exact wordN_lt _

theorem contains_map_arrN {l : List ℕ} (hl : ∀ y ∈ l, y < 2 ^ 36) {m : ℕ} (hm : m < 2 ^ 36) :
    (l.map arrN).contains (arrN m) = l.contains m := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    rw [← arrN_inj (hl y hy) hm he]
    exact hy
  · intro h
    exact ⟨m, h, rfl⟩

theorem closedN0_map (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {l : List ℕ}
    (hl : ∀ y ∈ l, y < 2 ^ 36) : closedN0 (genA ()) (l.map arrN) = closedN R l := by
  have hN12 : ∀ s ∈ idxN0, s < 12 := by decide
  apply Bool.eq_iff_iff.2
  unfold closedN0 closedN
  simp only [List.all_eq_true, List.mem_map]
  constructor
  · intro h s hs y hy
    have e := h s hs (arrN y) ⟨y, hy, rfl⟩
    rw [genA_eq12 hG (hN12 s hs), arrN_mul, arrN_mul,
      contains_map_arrN hl (CFSG.KC.Sp62.MULF_lt _ _)] at e
    exact e
  · rintro h s hs _ ⟨y, hy, rfl⟩
    rw [genA_eq12 hG (hN12 s hs), arrN_mul, arrN_mul,
      contains_map_arrN hl (CFSG.KC.Sp62.MULF_lt _ _)]
    exact h s hs y hy

theorem orbCheck_of {RA PAA PBA : ℕ → ℕ}
    (hA : BInvE (fun t => arrN (recX RA 12 t)) PAA PBA 64 (enumA0 ()))
    (hlt : ∀ t < 64, recX RA 12 t < 2 ^ 36)
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (ho : orbK R RA = true) :
    orbCheck () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hA
  have ha := orbCodes_eq (R := R) hG (x := [5]) (cs := orbAlphaWords) (by decide)
  have hb := orbCodes_eq (R := R) hG (x := [4]) (cs := orbPi12Words) (by decide)
  have hc := orbCodes_eq (R := R) hG (x := [5, 4]) (cs := orbPi3Words) (by decide)
  have hd := orbCodes_eq (R := R) hG (x := [3, 7]) (cs := orbRhoWords) (by decide)
  have hall : ∀ y ∈ orbN R [5] orbAlphaWords ++ orbN R [4] orbPi12Words ++
      orbN R [5, 4] orbPi3Words ++ orbN R [3, 7] orbRhoWords, y < 2 ^ 36 := by
    intro y hy
    simp only [List.mem_append] at hy
    rcases hy with ((h | h) | h) | h <;> exact orbN_lt _ _ y h
  unfold orbK at ho
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ho
  obtain ⟨⟨⟨⟨⟨hnd, c1⟩, c2⟩, c3⟩, c4⟩, hcov⟩ := ho
  simp only [orbCheck, Bool.and_eq_true, decide_eq_true_eq, allLt_iff]
  rw [ha, hb, hc, hd, ← List.map_append, ← List.map_append, ← List.map_append,
    closedN0_map hG (orbN_lt _ _), closedN0_map hG (orbN_lt _ _), closedN0_map hG (orbN_lt _ _),
    closedN0_map hG (orbN_lt _ _)]
  refine ⟨⟨⟨⟨⟨⟨by decide, hnd.map_on fun x hx y hy h => arrN_inj (hall x hx) (hall y hy) h⟩, c1⟩,
    c2⟩, c3⟩, c4⟩, fun i hi => ?_⟩
  rw [e1] at hi
  rw [e4 i hi]
  beta_reduce
  rw [← arrN_one, decide_arrN (hlt i hi) ONE_lt, contains_map_arrN hall (hlt i hi)]
  exact hcov i hi

theorem e8Check_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (he : e8K R = true) :
    e8Check () = true := by
  have hb := orbCodes_eq (R := R) hG (x := [4]) (cs := orbPi12Words) (by decide)
  have hl := orbN_lt (R := R) [4] orbPi12Words
  unfold e8K at he
  simp only [Bool.and_eq_true, List.all_eq_true] at he
  obtain ⟨h1, h2⟩ := he
  simp only [e8Check, Bool.and_eq_true, List.all_eq_true]
  rw [hb, ← arrN_one, contains_map_arrN hl ONE_lt]
  refine ⟨h1, ?_⟩
  simp only [List.mem_map]
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  rw [arrN_mul, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) ONE_lt,
    contains_map_arrN hl (CFSG.KC.Sp62.MULF_lt _ _)]
  exact h2 y hy z hz

theorem sylMeetCheck_of {S RA PAS PBS PAA PBA : ℕ → ℕ}
    (hS : BInvE (fun t => arrN (recX S 9 t)) PAS PBS 512 (enumS0 ()))
    (hSlt : ∀ t < 512, recX S 9 t < 2 ^ 36)
    (hA : BInvE (fun t => arrN (recX RA 12 t)) PAA PBA 64 (enumA0 ()))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (RA j.val))
    (hc : ∀ q < 16, sylChunk S RA 32 q = true) : sylMeetCheck () = true := by
  have hS' := hS
  obtain ⟨e1, -, -, e4, -⟩ := hS'
  simp only [sylMeetCheck, Bool.and_eq_true, allLt_iff]
  refine ⟨by decide, fun i hi => ?_⟩
  rw [e1] at hi
  have hq : i / 32 < 16 := by omega
  have hcq := hc _ hq
  unfold sylChunk at hcq
  simp only [CFSG.KC.YamakiRepF.strictY_eq] at hcq
  have hlo : Nat.mul 32 (i / 32) ≤ i := Nat.mul_div_le i 32
  have hhi : i < Nat.mul 32 (i / 32) + 32 := by
    change i < 32 * (i / 32) + 32
    omega
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq i hlo hhi
  rw [Nat.blt_eq.mpr hi, cond_true] at e
  rw [e4 i hi]
  beta_reduce
  rw [wordA_eq hG sylMeetWord (by decide), wordA_eq hG sylMeetWord.reverse (by decide), arrN_mul,
    arrN_mul]
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at e ⊢
  rcases e with h | h
  · left
    cases hl : ((enumS0 ()).lookup (arrN (MULF (MULF (wordN RA sylMeetWord.reverse) (recX S 9 i))
        (wordN RA sylMeetWord)))).isSome
    · rfl
    · rw [CFSG.KC.YamakiA6.memK_of_isSome hS hSlt (CFSG.KC.Sp62.MULF_lt _ _) hl] at h
      exact absurd h (by decide)
  · exact Or.inr (isSome_of_rec hA (memK_sound h))

end CFSG.KC.YamakiNO

end
