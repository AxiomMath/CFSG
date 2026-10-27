module

public import CFSG.Certificates.Kernel.ListBridge.PackSound
public import Certificates.Data.Kernel.ListBridgeComm

public section

namespace CFSG.ClassicalInvolution.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.BfsPin
open CFSG.KC.ListBridge
open scoped commutatorElement

variable {n w : Nat}

theorem prep_pcommutK {X Y : Nat} {x y : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32) (hw : n < 2 ^ w)
    (hX : PRep n w X x) (hY : PRep n w Y y) : PRep n w (pcommutK n w X Y) ⁅x, y⁆ := by
  rw [commutatorElement_def]
  exact prep_pcomp hn (prep_pcomp hn (prep_pcomp hn hX hY) (SporSch.MOC.prep_pinvS hw hX).1)
    (SporSch.MOC.prep_pinvS hw hY).1

section Enum

variable {ng N : Nat} {G T E S : Nat → Nat} {gens : List (Equiv.Perm (Fin n))}

theorem comm_mem_of_K (hk : bfsK n w ng G N T E S = true) (hl : gens.length = ng)
    (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1)) {ngB NB : Nat} {GB TB EB SB : Nat → Nat}
    {gensB : List (Equiv.Perm (Fin n))} (hkB : bfsK n w ngB GB NB TB EB SB = true)
    (hlB : gensB.length = ngB) (hGB : ∀ k < ngB, PRep n w (GB k) (gensB.getD k 1))
    (hc : commPtsK n w N T NB TB = true) :
    ∀ x ∈ Subgroup.closure {s | s ∈ gens}, ∀ y ∈ Subgroup.closure {s | s ∈ gens},
      ⁅x, y⁆ ∈ Subgroup.closure {s | s ∈ gensB} := by
  obtain ⟨hn, hw⟩ := bfsK_sz hk
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := ((enum_closure hk hl hG).1 x).1 hx
  obtain ⟨j, hj, hyj⟩ := ((enum_closure hk hl hG).1 y).1 hy
  obtain ⟨m, hm, e⟩ := inK_spec (allN_spec (allN_spec hc i hi) j hj)
  refine ((enum_closure hkB hlB hGB).1 _).2 ⟨m, hm, ?_⟩
  rw [e]
  exact prep_pcommutK (by omega) (by omega) hxi hyj

theorem abel_of_K (hk : bfsK n w ng G N T E S = true) (hl : gens.length = ng)
    (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1)) (hab : abelPtsK n w N T = true) :
    ∀ x ∈ Subgroup.closure {s | s ∈ gens}, ∀ y ∈ Subgroup.closure {s | s ∈ gens},
      x * y = y * x := by
  obtain ⟨hn, hw⟩ := bfsK_sz hk
  have hn32 : n < 2 ^ 32 := by omega
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := ((enum_closure hk hl hG).1 x).1 hx
  obtain ⟨j, hj, hyj⟩ := ((enum_closure hk hl hG).1 y).1 hy
  have e := Nat.eq_of_beq_eq_true (allN_spec (allN_spec hab i hi) j hj)
  have h1 := prep_pcomp hn32 hxi hyj
  rw [e] at h1
  exact prep_unique h1 (prep_pcomp hn32 hyj hxi)

theorem sq_of_K (hk : bfsK n w ng G N T E S = true) (hl : gens.length = ng)
    (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1)) (hp : powK n w 1 N T = true) :
    ∀ x ∈ Subgroup.closure {s | s ∈ gens}, x ^ 2 = 1 := by
  obtain ⟨hn, hw⟩ := bfsK_sz hk
  intro x hx
  obtain ⟨i, hi, hxi⟩ := ((enum_closure hk hl hG).1 x).1 hx
  have e := Nat.eq_of_beq_eq_true (allN_spec hp i hi)
  have h1 := prep_psqK (by omega) hxi 1
  rw [e] at h1
  simpa using prep_unique h1 (prep_pidn hn hw)

theorem not_mem_of_K (hk : bfsK n w ng G N T E S = true) (hl : gens.length = ng)
    (hG : ∀ k < ng, PRep n w (G k) (gens.getD k 1)) {R : Nat} {r : Equiv.Perm (Fin n)}
    (hR : PRep n w R r) (hRc : canonK n w (mask w) (n * w) R = true)
    (hout : CFSG.KLie.CT.notB (inK N T R) = true) : r ∉ Subgroup.closure {s | s ∈ gens} := by
  intro hr
  obtain ⟨i, hi, hTi⟩ := ((enum_closure hk hl hG).1 r).1 hr
  have e := eq_of_prep (bfsK_canon hk i hi) hRc hTi hR
  have hin : inK N T R = true := by
    unfold inK
    rw [anyN_eq, List.any_eq_true]
    exact ⟨i, List.mem_range.2 hi, by rw [e]; exact Nat.beq_refl R⟩
  rw [hin] at hout
  exact absurd hout (by decide)

end Enum

end CFSG.ClassicalInvolution.ListBridge

end
