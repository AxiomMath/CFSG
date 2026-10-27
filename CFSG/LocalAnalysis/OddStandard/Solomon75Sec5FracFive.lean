module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracPc
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracEnd
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracLu
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracMod
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracZero
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneTrans

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem false_of_fixCount_ge_five (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∈ normalizer (A : Set X)) (M : AhatModel X n A)
    (h5 : 5 ≤ fixCount (M.perm s hsA)) : False := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 8 ≤ n := h.maxdeg.1
  obtain ⟨u, hu, huZ, hu1, hus⟩ := h.exists_witness_Z hs hA hsA
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hs2 : s * s = 1 := hs.sq
  have hsu : s * u = u * s := hus.symm
  obtain ⟨Lu, hLuCu, hELu, hEq, hcovA, hcovLu, -⟩ := hu.exists_Lu hA.2
  set E : Subgroup X := oTwoPrimeOf (A ⊓ centralizer ({u} : Set X)) with hE
  have hEA : E ≤ A := (oTwoPrimeOf_le _).trans inf_le_left
  have huA : u ∈ A := hu.2.1
  have huE : u ∈ E := mem_oTwoPrimeOf_inf_centralizer huA hu2
  have hsE : s ∈ normalizer (E : Set X) := normalizer_oTwoPrimeOf_inf hsA hsu
  have hsLu : s ∈ normalizer (Lu : Set X) :=
    mem_normalizer_of_covers_of_normalizes hsu hLuCu hELu hsE hEq
  let ME : AhatModel X n E := M.transport hEA hcovA
  let MLu : AhatModel X n Lu := ME.transportUp hELu hcovLu
  have hperm : MLu.perm s hsLu = M.perm s hsA := by
    rw [ME.perm_transportUp hn hELu hcovLu hsE hsLu, M.perm_transport hn hEA hcovA hsE hsA]
  have h5' : 5 ≤ fixCount (MLu.perm s hsLu) := by
    rw [hperm]
    exact h5
  obtain ⟨P, hPL, hPn, hPq, hPmem⟩ := exists_piece_of_model MLu hn hsLu hs2 h5'
  have huLu : u ∈ Lu := hELu huE
  have huLc : u ∈ Lu ⊓ centralizer ({s} : Set X) :=
    ⟨huLu, Subgroup.mem_centralizer_singleton_iff.2 hus⟩
  have hEu : E ≤ centralizer ({u} : Set X) := (oTwoPrimeOf_le _).trans inf_le_right
  have hucen : ∀ l ∈ Lu, ⁅l, u⁆ ∈ oddCoreOf Lu := comm_mem_of_cover hELu hEu huLu hcovLu
  have hunO : u ∉ oddCoreOf Lu := by
    intro hO
    have hT : IsPGroup 2 ↥(Subgroup.zpowers u) := isPGroup_zpowers_of_mul_self hu2
    exact hu1 (eq_one_of_mem_pPrimeCoreOf_of_isPGroup hO hT (Subgroup.mem_zpowers u))
  have huP : u ∈ P := hPmem u huLc hu2 hunO hucen
  have hPcomp : IsPCompIn 2 (centralizer ({u} : Set X) ⊓ centralizer ({s} : Set X)) P :=
    isPCompIn_piece hLuCu hPL hPn hPq
  exact false_of_piece h hs huZ hu1 hus hPcomp huP

end CFSG.OddStandard.Solomon75
