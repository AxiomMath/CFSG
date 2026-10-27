module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Sp6

open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3
open CFSG.EvenSmallLie.Sp6
open CFSG.ClassicalInvolution.Q3.TL4.E4C CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data

@[expose] def tblA : List ℕ :=
  [8, 1, 9, 3, 10, 5, 11, 7, 0, 2, 4, 6, 16, 13, 18, 15, 12, 17, 14, 19, 24, 21, 25, 23, 20, 22, 26,
    27, 32, 29, 35, 31, 28, 33, 34, 30]

@[expose] def tblB : List ℕ :=
  [16, 20, 12, 24, 32, 0, 28, 8, 2, 9, 22, 25, 17, 23, 33, 3, 1, 29, 21, 13, 6, 35, 11, 30, 18, 14,
    4, 10, 5, 34, 26, 15, 19, 27, 7, 31]

@[expose] def tblFun (t : List ℕ) (i : Fin 36) : Fin 36 :=
  ⟨t.getD i 0 % 36, Nat.mod_lt _ (by norm_num)⟩

@[expose] def tblBi : List ℕ :=
  [5, 16, 8, 15, 26, 28, 20, 34, 7, 9, 27, 22, 2, 19, 25, 31, 0, 12, 24, 32, 1, 18, 10, 13, 3, 11,
    30, 33, 6, 17, 23, 35, 4, 14, 29, 21]

@[expose] def litPerm (t ti : List ℕ) (h1 : ∀ i : Fin 36, tblFun ti (tblFun t i) = i)
    (h2 : ∀ i : Fin 36, tblFun t (tblFun ti i) = i) : Equiv.Perm (Fin 36) where
  toFun := tblFun t
  invFun := tblFun ti
  left_inv := h1
  right_inv := h2

theorem tblA_l : ∀ i : Fin 36, tblFun tblA (tblFun tblA i) = i := by decide +kernel

theorem tblB_l : ∀ i : Fin 36, tblFun tblBi (tblFun tblB i) = i := by decide +kernel

theorem tblB_r : ∀ i : Fin 36, tblFun tblB (tblFun tblBi i) = i := by decide +kernel

@[expose] def litA : Equiv.Perm (Fin 36) := litPerm tblA tblA tblA_l tblA_l

@[expose] def litB : Equiv.Perm (Fin 36) := litPerm tblB tblBi tblB_l tblB_r

theorem sp6A_eq : sp6A = litA := Equiv.ext (by decide +kernel)

theorem sp6B_eq : sp6B = litB := Equiv.ext (by decide +kernel)

theorem sp6Gens_eq : sp6Gens = [litA, litB] := by
  unfold sp6Gens
  rw [sp6A_eq, sp6B_eq]

@[expose] def cg2 (G : List (Equiv.Perm (Fin 36))) : List (Equiv.Perm (Fin 36)) :=
  ([[1, 2], [2, 1, 2, 2, 1, -2, -2, 1, -2], [1, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2]] :
    List (List ℤ)).map (evalCodes G)

@[expose] def rhoG (G : List (Equiv.Perm (Fin 36))) : Equiv.Perm (Fin 36) :=
  tab (evalCodes (cg2 G) [1, 1, 1])

@[expose] def jayG (G : List (Equiv.Perm (Fin 36))) : Equiv.Perm (Fin 36) :=
  tab (evalCodes (cg2 G) [2, 1, 3, 3, 1, 1, 2])

@[expose] def r2G (G : List (Equiv.Perm (Fin 36))) : Equiv.Perm (Fin 36) :=
  tab ((sp6InvRepWords.map (evalCodes G)).getD 1 1)

@[expose] def L0G (G : List (Equiv.Perm (Fin 36))) : List (Equiv.Perm (Fin 36)) :=
  q8Elems (r2G G) (rhoG G) (jayG G)

@[expose] def x3Word : List ℤ :=
  [2, 1, -2, -2, -2, 1, -2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, -2, -2, 1, -2, 1, 2,
    2, 1, 2, 2, -1, 2, 1, -2, -2, 1]

@[expose] def x3G (G : List (Equiv.Perm (Fin 36))) : Equiv.Perm (Fin 36) :=
  tab (evalCodes G x3Word)

@[expose] def x3 (_ : Unit) : Equiv.Perm (Fin 36) := x3G sp6Gens

theorem rho_eq : rho () = rhoG sp6Gens := rfl

theorem jay_eq : jay () = jayG sp6Gens := rfl

theorem r2_eq : tab sp6Rep2 = r2G sp6Gens := rfl

theorem L0_eq : L0 () = L0G sp6Gens := rfl

@[expose] def sig3 (k : ℕ) : ℕ := [0, 1, 5, 4, 6, 7, 3, 2].getD k 0

theorem mem_L0G {G : List (Equiv.Perm (Fin 36))} {y : Equiv.Perm (Fin 36)} (h : y ∈ L0G G) :
    ∃ k : Fin 8, y = (L0G G).getD k 1 := by
  simp only [L0G, q8Elems, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩

theorem getD_mem_L0G (G : List (Equiv.Perm (Fin 36))) (k : ℕ) (hk : k < 8) :
    (L0G G).getD k 1 ∈ L0G G := by
  simp only [L0G, q8Elems]
  interval_cases k <;> simp

theorem sig3_lt (k : Fin 8) : sig3 k < 8 := by
  fin_cases k <;> decide

section Checks

local notation "GL" => ([litA, litB] : List (Equiv.Perm (Fin 36)))

theorem x3_cube_aux : x3G GL * x3G GL * x3G GL = 1 := by decide +kernel

theorem x3_norm_aux : ∀ k : Fin 8,
    x3G GL * (L0G GL).getD k 1 * (x3G GL)⁻¹ = (L0G GL).getD (sig3 k) 1 := by decide +kernel

theorem x3_cent_aux : x3G GL * r2G GL = r2G GL * x3G GL := by decide +kernel

theorem x3_act_aux1 : x3G GL * rhoG GL * (x3G GL)⁻¹ * (rhoG GL)⁻¹ ≠ 1 := by decide +kernel

theorem x3_act_aux2 : x3G GL * rhoG GL * (x3G GL)⁻¹ * (rhoG GL)⁻¹ ≠ r2G GL := by decide +kernel

theorem L0_sq_aux : ∀ k : Fin 8, 2 ≤ k.val →
    (L0G GL).getD k 1 * (L0G GL).getD k 1 ≠ 1 := by decide +kernel

end Checks

theorem x3_cube : x3 () * x3 () * x3 () = 1 := by
  have := x3_cube_aux
  rw [← sp6Gens_eq] at this
  exact this

theorem x3_norm : ∀ y ∈ L0 (), x3 () * y * (x3 ())⁻¹ ∈ L0 () := by
  intro y hy
  rw [L0_eq] at hy ⊢
  obtain ⟨k, rfl⟩ := mem_L0G hy
  have h := x3_norm_aux k
  rw [← sp6Gens_eq] at h
  show x3G sp6Gens * _ * (x3G sp6Gens)⁻¹ ∈ _
  rw [h]
  exact getD_mem_L0G _ _ (sig3_lt k)

theorem x3_cent : x3 () * tab sp6Rep2 = tab sp6Rep2 * x3 () := by
  have := x3_cent_aux
  rw [← sp6Gens_eq] at this
  exact this

theorem x3_act : x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹ ≠ 1 ∧
    x3 () * rho () * (x3 ())⁻¹ * (rho ())⁻¹ ≠ tab sp6Rep2 := by
  have h1 := x3_act_aux1
  have h2 := x3_act_aux2
  rw [← sp6Gens_eq] at h1 h2
  exact ⟨h1, h2⟩

theorem L0_inv : ∀ y ∈ L0 (), y * y = 1 → y = 1 ∨ y = tab sp6Rep2 := by
  intro y hy hyy
  rw [L0_eq] at hy
  obtain ⟨k, rfl⟩ := mem_L0G hy
  by_cases hk : 2 ≤ k.val
  · exfalso
    have h := L0_sq_aux k hk
    rw [← sp6Gens_eq] at h
    exact h hyy
  · have : k.val = 0 ∨ k.val = 1 := by omega
    rcases this with h0 | h1
    · left
      have : k = 0 := Fin.ext h0
      subst this
      rfl
    · right
      have : k = 1 := Fin.ext h1
      subst this
      rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4Sp6
