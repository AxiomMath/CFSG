module

public import Certificates.Data.Kernel.Misc.OmegaSixE
public import CFSG.Certificates.Kernel.Misc.OmegaSixClassSound

public section

namespace CFSG.KC.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.OmegaSix
  CFSG.KD.YamakiRep CFSG.KD.YamakiRepF CFSG.KC.YamakiRep CFSG.KC.YamakiRepF
open CFSG.KD.Sp62 (MULF ONE)

variable {R : ℕ → ℕ}

theorem wordF6_lt (g : ℕ → ℕ) : ∀ w, wordF6 g w < 2 ^ 36
  | [] => CFSG.KC.YamakiS0.ONE_lt
  | _ :: _ => CFSG.KC.Sp62.MULF_lt _ _

theorem wordA_arrF (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1)) :
    ∀ w : List ℕ, (∀ i ∈ w, i < 2) → wordA (genA6 ()) w = arrF (wordF6 R w)
  | [], _ => by
    rw [wordA, ← arrF_one]
    rfl
  | i :: w, h => by
    rw [wordA, wordA_arrF hA hB w fun j hj => h j (List.mem_cons_of_mem _ hj),
      genA6_get hA hB i (h i List.mem_cons_self), Nat.zero_add, arrF_mul]
    rfl

theorem relM_of (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (h : ∀ w ∈ relators, Nat.beq (wordF6 R w) ONE = true) : relCheck () = true := by
  have hl : ∀ w ∈ relators, ∀ i ∈ w, i < 2 := by decide
  simp only [relCheck, List.all_eq_true]
  intro w hw
  rw [wordA_arrF hA hB w (hl w hw), ← arrF_one,
    beq_arrF (wordF6_lt R w) CFSG.KC.YamakiS0.ONE_lt]
  exact h w hw

theorem enumM_of (hA : aMat = matF (R 0)) (hB : bMat = matF (R 1))
    (hh : headK R 10 25920 2 = true)
    (hc : ∀ q < 51, chunkF R (rstG R 0) 10 25920 512 q = true) :
    CFSG.CGT.Foote82.OmegaSix.enumCheck () = true := by
  have T := table_invF (gs := genA6 ()) (R := R) (o := 10) (n := 25920) (k := 2) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) (genA6_get hA hB) hh
    (rows_of_chunks (L := 512) (m := 51) (fun q hq => chunkK_of_chunkF (hc q hq)) (by norm_num))
  change (enumOK (bfsEnum (genA6 ()) 25920) (genA6 ()) &&
    (bfsEnum (genA6 ()) 25920).elems.size == 25920) = true
  rw [T.2.1, T.1.1]
  rfl

end CFSG.KC.OmegaSix

end
