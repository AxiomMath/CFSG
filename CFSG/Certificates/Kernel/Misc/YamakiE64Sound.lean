module

public import Certificates.Data.Kernel.Misc.YamakiE64
public import CFSG.Certificates.Kernel.Misc.YamakiCESound

public section

namespace CFSG.KC.YamakiE64

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiCE
  CFSG.KD.YamakiE64 CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0 CFSG.KC.YamakiCE
open CFSG.KD.Sp62 (MULF ONE)

variable {R : ℕ → ℕ} {o : ℕ}

theorem coreLen_map (T : List ℕ) (hT : ∀ x ∈ T, x < 2 ^ 36) :
    ((T.map arrN).filter fun x =>
        decide (64 ≤ ((T.map arrN).filter fun y => decide (compA x y = compA y x)).length)).length =
      coreLen T := by
  unfold coreLen
  rw [List.filter_map, List.length_map]
  refine congrArg List.length (List.filter_congr fun x hx => ?_)
  have hin : List.filter ((fun y => decide (compA (arrN x) y = compA y (arrN x))) ∘ arrN) T =
      T.filter fun y => Nat.beq (MULF x y) (MULF y x) := by
    apply List.filter_congr
    intro y hy
    simp only [Function.comp_apply]
    rw [arrN_mul, arrN_mul, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]
  simp only [Function.comp_apply]
  rw [List.filter_map, List.length_map, hin]

theorem cands_eq {PA PB : ℕ → ℕ} {E : Enum} (hE : BInvE (fun t => arrN (recX R o t)) PA PB 512 E)
    (hlt : ∀ t < 512, recX R o t < 2 ^ 36) (b : ℕ) :
    e64Cands E.elems (arrN b) = (candsN R o 512 b).map arrN := by
  obtain ⟨e1, -, -, e4, -⟩ := hE
  simp only [e64Cands, candsN]
  rw [e1]
  have hmap : (List.range 512).map (fun k => E.elems[k]!) =
      ((List.range 512).map (recX R o)).map arrN := by
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    rw [e4 k (List.mem_range.1 hk)]
    rfl
  rw [hmap, List.filter_map]
  refine congrArg (List.map arrN) (List.filter_congr fun x hx => ?_)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  have hx' := hlt k (List.mem_range.1 hk)
  simp only [Function.comp_apply]
  rw [arrN_mul, ← arrN_one, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) ONE_lt, arrN_mul, arrN_mul,
    decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]

theorem core_eq {PA PB : ℕ → ℕ} {E : Enum} (hE : BInvE (fun t => arrN (recX R o t)) PA PB 512 E)
    (hlt : ∀ t < 512, recX R o t < 2 ^ 36) (b : ℕ) :
    (e64Core E.elems (arrN b)).length = coreLen (candsN R o 512 b) := by
  simp only [e64Core]
  rw [cands_eq hE hlt b]
  refine coreLen_map _ fun x hx => ?_
  obtain ⟨hx, -⟩ := List.mem_filter.1 hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact hlt k (List.mem_range.1 hk)

theorem e64Check_of {RA PA PB PAA PBA : ℕ → ℕ}
    (hS : BInvE (fun t => arrN (recX R o t)) PA PB 512 (enumS0 ()))
    (hA : BInvE (fun t => arrN (recX RA 12 t)) PAA PBA 64 (enumA0 ()))
    (hlt : ∀ t < 512, recX R o t < 2 ^ 36) (hc : ∀ q < 16, e64Chunk R o RA 12 32 q = true) :
    e64Check () = true := by
  have hS' := hS
  obtain ⟨e1, -, -, e4, -⟩ := hS'
  simp only [e64Check, allLt_iff]
  intro i hi
  rw [e1] at hi
  have hq : i / 32 < 16 := by omega
  have hcq := hc _ hq
  unfold e64Chunk at hcq
  have hlo : Nat.mul 32 (i / 32) ≤ i := Nat.mul_div_le i 32
  have hhi : i < Nat.mul 32 (i / 32) + 32 := by
    change i < 32 * (i / 32) + 32
    omega
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq i hlo hhi
  rw [Nat.blt_eq.mpr hi, cond_true] at e
  simp only [e64At, CFSG.KC.YamakiRepF.strictY_eq] at e
  rw [e4 i hi]
  beta_reduce
  rw [arrN_mul, ← arrN_one, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) ONE_lt, core_eq hS hlt]
  simp only [Bool.or_eq_true] at e ⊢
  rcases e with (h | h) | h
  · exact Or.inl (Or.inl (isSome_of_rec hA (memK_sound h)))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

end CFSG.KC.YamakiE64

end
