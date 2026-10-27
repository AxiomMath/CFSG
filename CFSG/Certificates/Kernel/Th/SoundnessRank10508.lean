module

public import CFSG.Certificates.Kernel.Th.Gen.Max3
public import CFSG.Sporadic.Th.Max3.RankInputs
public import Certificates.Data.Kernel.ThRank10508.Defs
public import CFSG.Certificates.Kernel.Th.Max3S.R10508
import CFSG.Certificates.Kernel.Common.Generalize
public import CFSG.Certificates.Kernel.Th.Max3S.Regs

public section

namespace CFSG.KC.Th.Soundness

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.Rank
open CFSG.KC.Th.Gen CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.Rank
open CFSG.KC.ThRk10508 CFSG.KC.Th.Max3S

#kc_generalize Max3Gen10508 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  ((∀ a b c d : Fin 9, RkCand (rkTup a b c d) →
      ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkPerm i j) ∧
    RkFacts (rkData ()))

set_option maxRecDepth 100000 in
theorem rank_sound10508_gen (sA sB : String) (D : Max3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true)
    (h1 : ∀ a b c d : Fin 9, RkCand (rkTup a b c d) →
      ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkPerm i j)
    (L : ℕ → ℕ) (Ks Es Ws Cl Ts : List ℕ) (Ds : List (List ℕ))
    (hcq : ∀ g < 8, cqChunk D.ThM3_RB D.ThS_c D.ThS_rm Cl g = true)
    (hcc : ∀ j < Cl.length, ccK D.ThM3_RB D.ThS_c D.ThS_rm Cl (getN Cl j) = true)
    (hrow : ∀ i : Fin 12,
      rowI D.ThM3_RB D.ThS_c D.ThS_rm D.ThS_ONE L Ks Es Ws Cl Ds Ts i.val = true)
    (hKs : ∀ i : Fin 12, getN Ks i.val = (rkK0 i).val)
    (hEs : ∀ i : Fin 12, getN Es i.val = encGen (rkWord i))
    (hWs : ∀ i : Fin 12, getN Ws i.val = (rkWord i).length)
    (hTs : ∀ i : Fin 12, rkTypeB i = false → memL Ts i.val = false)
    (h16 : (rkC0 Cl).length = 16)
    (h8 : ∀ i : Fin 12, (rkD0 Cl Ds i).length ≤ 8)
    (h4 : ∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
      rkPerm i * rkPerm j = rkPerm j * rkPerm i → rkPerm j ≠ rkPerm i →
      rkPerm j ≠ rkPerm i * aPerm →
      ((rkD0 Cl Ds i).filter fun k => decide (k ∈ rkD0 Cl Ds j)).length ≤ 4) :
    Max3Gen10508 sA sB := by
  subst _hA _hB
  exact fun _ _ => ⟨h1, rkFacts_of D _h (regOK_of D _h) (CFSG.KC.Th.Spec.wfRows_rowsOf _)
    (CFSG.KC.Th.Spec.wfRows_rowsOf _)
    L Ks Es Ws Cl Ts Ds hcq hcc hrow hKs hEs hWs hTs h16 h8 h4⟩

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.Rank in
theorem rank_sound10508 (D : Max3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true)
    (h1 : ∀ a b c d : Fin 9, RkCand (rkTup a b c d) →
      ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkPerm i j)
    (L : ℕ → ℕ) (Ks Es Ws Cl Ts : List ℕ) (Ds : List (List ℕ))
    (hcq : ∀ g < 8, cqChunk D.ThM3_RB D.ThS_c D.ThS_rm Cl g = true)
    (hcc : ∀ j < Cl.length, ccK D.ThM3_RB D.ThS_c D.ThS_rm Cl (getN Cl j) = true)
    (hrow : ∀ i : Fin 12,
      rowI D.ThM3_RB D.ThS_c D.ThS_rm D.ThS_ONE L Ks Es Ws Cl Ds Ts i.val = true)
    (hKs : ∀ i : Fin 12, getN Ks i.val = (rkK0 i).val)
    (hEs : ∀ i : Fin 12, getN Es i.val = encGen (rkWord i))
    (hWs : ∀ i : Fin 12, getN Ws i.val = (rkWord i).length)
    (hTs : ∀ i : Fin 12, rkTypeB i = false → memL Ts i.val = false)
    (h16 : (rkC0 Cl).length = 16)
    (h8 : ∀ i : Fin 12, (rkD0 Cl Ds i).length ≤ 8)
    (h4 : ∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
      rkPerm i * rkPerm j = rkPerm j * rkPerm i → rkPerm j ≠ rkPerm i →
      rkPerm j ≠ rkPerm i * aPerm →
      ((rkD0 Cl Ds i).filter fun k => decide (k ∈ rkD0 Cl Ds j)).length ≤ 4) :

    (∀ a b c d : Fin 9, RkCand (rkTup a b c d) →
      ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkPerm i j) ∧
    RkFacts (rkData ()) :=
  Max3Gen10508.inst (rank_sound10508_gen _ _ D _hA _hB _h h1 L Ks Es Ws Cl Ts Ds hcq hcc hrow
    hKs hEs hWs hTs h16 h8 h4)

end CFSG.KC.Th.Soundness

end
