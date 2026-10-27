module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4C
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

namespace Sp6

def tf (l : List ℕ) (i : Fin 36) : Fin 36 := ⟨l.getD i.val 0 % 36, Nat.mod_lt _ (by norm_num)⟩

def lit (l li : List ℕ) (h1 : ∀ i : Fin 36, tf li (tf l i) = i)
    (h2 : ∀ i : Fin 36, tf l (tf li i) = i) : Equiv.Perm (Fin 36) where
  toFun := tf l
  invFun := tf li
  left_inv := h1
  right_inv := h2

def tR : List ℕ :=
  [0, 28, 27, 19, 16, 24, 31, 7, 14, 33, 10, 23, 12, 20, 8, 32, 4, 17, 18, 3, 13, 21, 35, 11, 5, 25,
    26, 2, 1, 29, 30, 6, 15, 9, 34, 22]

def tRho : List ℕ :=
  [29, 33, 24, 22, 8, 2, 13, 17, 16, 1, 21, 32, 34, 31, 4, 11, 14, 7, 26, 35, 6, 10, 19, 15, 27, 30,
    18, 5, 9, 0, 25, 20, 23, 28, 12, 3]

def tRhoI : List ℕ :=
  [29, 9, 5, 35, 14, 27, 20, 17, 4, 28, 21, 15, 34, 6, 16, 23, 8, 7, 26, 22, 31, 10, 3, 32, 2, 30,
    18, 24, 33, 0, 25, 13, 11, 1, 12, 19]

def tJay : List ℕ :=
  [18, 31, 23, 8, 35, 15, 1, 25, 19, 20, 34, 2, 21, 9, 3, 24, 22, 30, 0, 14, 33, 12, 4, 27, 32, 7,
    29, 11, 6, 26, 17, 28, 5, 13, 10, 16]

def tJayI : List ℕ :=
  [18, 6, 11, 14, 22, 32, 28, 25, 3, 13, 34, 27, 21, 33, 19, 5, 35, 30, 0, 8, 9, 12, 16, 2, 15, 7,
    29, 23, 31, 26, 17, 1, 24, 20, 10, 4]

def tTwin : List ℕ :=
  [18, 32, 33, 19, 4, 20, 23, 7, 8, 27, 12, 31, 10, 24, 14, 28, 16, 17, 0, 3, 5, 21, 22, 6, 13, 30,
    26, 9, 15, 29, 25, 11, 1, 2, 34, 35]

def litR : Equiv.Perm (Fin 36) := lit tR tR (by decide +kernel) (by decide +kernel)

def litRho : Equiv.Perm (Fin 36) := lit tRho tRhoI (by decide +kernel) (by decide +kernel)

def litJay : Equiv.Perm (Fin 36) := lit tJay tJayI (by decide +kernel) (by decide +kernel)

def litTwin : Equiv.Perm (Fin 36) := lit tTwin tTwin (by decide +kernel) (by decide +kernel)

def fixCount (σ : Equiv.Perm (Fin 36)) : ℕ := (Finset.univ.filter fun i => σ i = i).card

theorem fix_litR : fixCount litR = 12 := by decide +kernel

theorem frame_lit : ∀ x ∈ q8Elems litR litRho litJay, ∀ x' ∈ q8Elems litR litRho litJay,
    x * x = litR → x' * x' = litR → fixCount (x * (litTwin * x' * litTwin⁻¹)) = 8 := by
  intro x hx x' hx'
  simp only [q8Elems, List.mem_cons, List.not_mem_nil, or_false] at hx hx'
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def a0 : Equiv.Perm (Fin 36) :=
  (List.formPerm [0, 8] * List.formPerm [2, 9] * List.formPerm [4, 10] *
    List.formPerm [6, 11] * List.formPerm [12, 16] * List.formPerm [14, 18] *
    List.formPerm [20, 24] * List.formPerm [22, 25] * List.formPerm [28, 32] *
    List.formPerm [30, 35])

def b0 : Equiv.Perm (Fin 36) :=
  (List.formPerm [0, 16, 1, 20, 6, 28, 5] * List.formPerm [2, 12, 17, 29, 34, 7, 8] *
    List.formPerm [3, 24, 18, 21, 35, 31, 15] * List.formPerm [4, 32, 19, 13, 23, 30, 26] *
    List.formPerm [10, 22, 11, 25, 14, 33, 27])

theorem sp6A_eq : sp6A = a0 := by unfold sp6A a0; exact tab_eq _
theorem sp6B_eq : sp6B = b0 := by unfold sp6B b0; exact tab_eq _
theorem sp6Gens_eq : sp6Gens = [a0, b0] := by unfold sp6Gens; rw [sp6A_eq, sp6B_eq]

def cg2 : List (Equiv.Perm (Fin 36)) :=
  ([[1, 2], [2, 1, 2, 2, 1, -2, -2, 1, -2], [1, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2]] :
    List (List ℤ)).map (evalCodes [a0, b0])

theorem rho_eq : rho () = litRho := by
  have h1 : rho () = evalCodes cg2 [1, 1, 1] := by
    unfold rho sp6CentGens2 cg2
    rw [tab_eq, sp6Gens_eq]
  have h2 : ∀ i : Fin 36, evalCodes cg2 [1, 1, 1] i = litRho i := by decide +kernel
  rw [h1]
  exact Equiv.ext h2

theorem jay_eq : jay () = litJay := by
  have h1 : jay () = evalCodes cg2 [2, 1, 3, 3, 1, 1, 2] := by
    unfold jay sp6CentGens2 cg2
    rw [tab_eq, sp6Gens_eq]
  have h2 : ∀ i : Fin 36, evalCodes cg2 [2, 1, 3, 3, 1, 1, 2] i = litJay i := by decide +kernel
  rw [h1]
  exact Equiv.ext h2

theorem R_eq : tab sp6Rep2 = litR := by
  have h1 : sp6Rep2 = evalCodes [a0, b0] [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] := by
    unfold sp6Rep2 sp6InvReps sp6InvRepWords
    rw [sp6Gens_eq]
    rfl
  have h2 : ∀ i : Fin 36, evalCodes [a0, b0] [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] i = litR i := by
    decide +kernel
  rw [tab_eq, h1]
  exact Equiv.ext h2

theorem twin_eq : twin () = litTwin := by
  have h1 : twin () = (memberWords.map fun w => evalCodes [a0, b0] w).getD 11 1 := by
    unfold twin ws
    rw [sp6Gens_eq]
    simp only [tab_eq]
  have h2 : ∀ i : Fin 36, ((memberWords.map fun w => evalCodes [a0, b0] w).getD 11 1) i = litTwin i := by
    decide +kernel
  rw [h1]
  exact Equiv.ext h2

theorem L0_eq : L0 () = q8Elems litR litRho litJay := by
  unfold L0
  rw [R_eq, rho_eq, jay_eq]


theorem fixCount_conj (g s : Equiv.Perm (Fin 36)) : fixCount (g * s * g⁻¹) = fixCount s := by
  unfold fixCount
  refine Finset.card_bij (fun a _ => g⁻¹ a) ?_ ?_ ?_
  · intro a ha
    have h1 : g (s (g⁻¹ a)) = a := (Finset.mem_filter.mp ha).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply g.injective
    rw [h1]
    simp
  · intro a₁ _ a₂ _ h
    exact g⁻¹.injective h
  · intro b hb
    have h1 : s b = b := (Finset.mem_filter.mp hb).2
    refine ⟨g b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    show g (s (g⁻¹ (g b))) = g b
    simp [h1]

theorem frame_core {x y : Equiv.Perm (Fin 36)} (hx : x ∈ K0)
    (hy : y ∈ conjSub (twin ()) K0) (hxx : x * x = tab sp6Rep2) (hyy : y * y = tab sp6Rep2) :
    fixCount (x * y) = 8 := by
  have hx' : x ∈ q8Elems litR litRho litJay := by rw [← L0_eq]; exact (mem_K0_iff x).mp hx
  have hxx0 : x * x = litR := by rw [hxx, R_eq]
  have hyy0 : y * y = litR := by rw [hyy, R_eq]
  have hy' : (twin ())⁻¹ * y * twin () ∈ K0 := (mem_conjSub_iff).mp hy
  have hy'' : (twin ())⁻¹ * y * twin () ∈ q8Elems litR litRho litJay := by
    rw [← L0_eq]
    exact (mem_K0_iff _).mp hy'
  rw [twin_eq] at hy''
  have hyx : y = litTwin * (litTwin⁻¹ * y * litTwin) * litTwin⁻¹ := by group
  have hxx' : (litTwin⁻¹ * y * litTwin) * (litTwin⁻¹ * y * litTwin) = litR := by
    have hcomm : litTwin * litR = litR * litTwin := by decide +kernel
    calc (litTwin⁻¹ * y * litTwin) * (litTwin⁻¹ * y * litTwin)
        = litTwin⁻¹ * (y * y) * litTwin := by group
      _ = litTwin⁻¹ * litR * litTwin := by rw [hyy0]
      _ = litR := by rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hyx]
  exact frame_lit x hx' _ hy'' hxx0 hxx'

end Sp6

open Sp6

theorem e4Sp6FrameModel_of_certs :
    E4Sp6FrameModel := by
  intro M _ _ hM K s hq hinv htw K' hK' hne hle u₁ h₁ u₂ h₂ o₁ o₂ g hg
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  obtain ⟨φ, hφ, hrange, hKφ⟩ :=
    TwinThmE.exists_emb_of_ident e (fun K s hd => E4Sp6.ident_ambient hd) hq hinv htw
  have hmem : ∀ m, φ m ∈ co3X36 := fun m => hrange ▸ ⟨m, rfl⟩
  have hs : φ s = sp6Rep2 :=
    E4Sp6.eq_rep_of_isUniqueInvolution (hKφ ▸ TL4.Vtx.isUniqueInvolution_map φ hφ hinv)
  obtain ⟨y, rfl⟩ := hK'
  have hK'φ : (conjSub y K).map φ = conjSub (φ y) K0 := by
    rw [AscQuot.map_conjSub, hKφ]
  have hBK : conjSub (φ y) K0 = conjSub (twin ()) K0 := by
    refine E4Sp6.eq_twin_of_le_normalizer (hmem y) (fun h1 => hne ?_) ?_
    · apply Subgroup.map_injective hφ
      rw [hK'φ, h1, hKφ]
    · rw [← hK'φ, ← hKφ]
      exact (TL4.Vtx.map_le_normalizer_map_iff φ hφ).mpr hle
  have hu₁ : φ u₁ ∈ K0 := hKφ ▸ Subgroup.mem_map_of_mem φ h₁
  have hu₂ : φ u₂ ∈ conjSub (twin ()) K0 := by
    rw [← hBK, ← hK'φ]
    exact Subgroup.mem_map_of_mem φ h₂
  have hsq₁ : φ u₁ * φ u₁ = tab sp6Rep2 := by rw [← map_mul, o₁, hs, tab_eq]
  have hsq₂ : φ u₂ * φ u₂ = tab sp6Rep2 := by rw [← map_mul, o₂, hs, tab_eq]
  have key := frame_core hu₁ hu₂ hsq₁ hsq₂
  have hgs : φ g * φ s * (φ g)⁻¹ = φ u₁ * φ u₂ := by
    rw [← map_inv, ← map_mul, ← map_mul, hg, map_mul]
  rw [← hgs, fixCount_conj, hs, ← tab_eq sp6Rep2, R_eq] at key
  exact absurd key (by rw [fix_litR]; norm_num)


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M
