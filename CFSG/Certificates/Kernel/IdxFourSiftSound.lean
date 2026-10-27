
module

public import Certificates.Data.Kernel.IdxFourSiftK
public import CFSG.Certificates.Kernel.IdxFourChainSound

public section

namespace CFSG.KC.IF4R

open CFSG.KC.IF4C CFSG.GF2Type.Smith1979.GammaU

theorem recOK_spec {T O : List Nat} {n : Nat} {f : Nat → Nat} {r : Nat} :
    ∀ {p : List Nat}, recOK T O n f r p = true →
      ∃ x < n, ∃ as, pathOK O as = true ∧ mulP (pathP T as) (f x) = r
  | [], h => by simp [recOK] at h
  | x :: as, h => by
    have h' : (Nat.blt x n && pathOK O as && Nat.beq (mulP (pathP T as) (f x)) r) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    exact ⟨x, h'.1.1, as, h'.1.2, h'.2⟩

theorem recsOK_spec {T O : List Nat} {n : Nat} {f : Nat → Nat} :
    ∀ {rs : List Nat} {ps : List (List Nat)}, recsOK T O n f rs ps = true →
      ∀ r ∈ rs, ∃ x < n, ∃ as, pathOK O as = true ∧ mulP (pathP T as) (f x) = r
  | [], _, _, r, hr => absurd hr List.not_mem_nil
  | _ :: _, [], h, _, _ => by simp [recsOK] at h
  | r0 :: rs, p :: ps, h, r, hr => by
    have h' : (recOK T O n f r0 p && recsOK T O n f rs ps) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hr with rfl | hr
    · exact recOK_spec h'.1
    · exact recsOK_spec h'.2 r hr

theorem exists_subP {K : Subgroup (V12 ≃ₗ[ZMod 2] V12)} :
    ∀ (gs : List Nat), (∀ g ∈ gs, ∃ U ∈ K, IsP U g) → ∀ x, ∃ U ∈ K, IsP U (subP gs x)
  | [], _, _ => ⟨1, K.one_mem, IsP.one⟩
  | g :: gs, h, x => by
    obtain ⟨V, hV, hVP⟩ := exists_subP gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) (x / 2)
    change ∃ U ∈ K, IsP U (mulP (bif Nat.beq (Nat.mod x 2) 1 then g else idP) (subP gs (x / 2)))
    cases Nat.beq (Nat.mod x 2) 1
    · exact ⟨1 * V, K.mul_mem K.one_mem hV, IsP.one.mul hVP⟩
    · obtain ⟨U, hU, hUP⟩ := h g List.mem_cons_self
      exact ⟨U * V, K.mul_mem hU hV, hUP.mul hVP⟩

theorem isP_iff_of_rowsP {r : Array Nat} (h : rowsP (packR r) = r) (U : V12 ≃ₗ[ZMod 2] V12) :
    IsP U (packR r) ↔ ∀ v, U v = linOfRows r v := by
  simp only [IsP, linP_eq_of_rowsP h]

end CFSG.KC.IF4R

end
