module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Mog22Gens
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.EndMask

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc CFSG.Quasithin.H.ModChk

@[expose] def mog22EndG : List (List ℕ) := [[0], [1]]

@[expose] def mog22EndH : List (List ℕ) :=
  [[1, 1, 0, 1, 1, 0, 1, 1], [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0]]

@[expose] def mog22EndS : List (List ℕ) :=
  [[], [0], [1], [1, 1], [0, 1], [1, 0], [1, 1, 0], [0, 1, 0], [1, 0, 1], [1, 0, 1, 0],
    [0, 1, 0, 1]]

@[expose] def mog22EndU2 : List ℕ := [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1]

@[expose] def mog22EndU3 : List ℕ := [1, 0]

theorem mog22EndG_lt : ∀ u ∈ mog22EndG, ∀ i ∈ u, i < 2 := by decide +kernel

theorem mog22EndH_lt : ∀ u ∈ mog22EndH, ∀ i ∈ u, i < 2 := by decide +kernel

theorem mog22EndS_lt : ∀ u ∈ mog22EndS, ∀ i ∈ u, i < 2 := by decide +kernel

theorem mog22EndU2_lt : ∀ i ∈ mog22EndU2, i < 2 := by decide +kernel

theorem mog22EndU3_lt : ∀ i ∈ mog22EndU3, i < 2 := by decide +kernel

theorem mog22EndG_fix_t0 : ∀ u ∈ mog22EndG, wAct [mog22ColsA, mog22ColsB] u 95 = 95 := by
  decide +kernel

theorem mog22EndG_fixed : ∀ m < 2 ^ 11,
    (∀ u ∈ mog22EndG, wAct [mog22ColsA, mog22ColsB] u m = m) → m = 0 ∨ m = 95 := by
  decide +kernel

theorem mog22EndH_fix_v0 : ∀ u ∈ mog22EndH, wAct [mog22ColsA, mog22ColsB] u 64 = 64 := by
  decide +kernel

theorem mog22EndH_fixed : ∀ m < 2 ^ 11,
    (∀ u ∈ mog22EndH, wAct [mog22ColsA, mog22ColsB] u m = m) →
      m = 0 ∨ m = 95 ∨ m = 64 ∨ m = 64 ^^^ 95 := by
  decide +kernel

theorem mog22EndU2_fix_t0 : wAct [mog22ColsA, mog22ColsB] mog22EndU2 95 = 95 := by decide +kernel

theorem mog22EndU3_fix_t0 : wAct [mog22ColsA, mog22ColsB] mog22EndU3 95 = 95 := by decide +kernel

theorem mog22End_triangle : 64 ^^^ wAct [mog22ColsA, mog22ColsB] mog22EndU2 64 ^^^
    wAct [mog22ColsA, mog22ColsB] mog22EndU3 64 = 0 := by decide +kernel

theorem mog22End_units : ∀ j < 11, id (2 ^ j) ∈
    combos (mog22EndS.map fun u => wAct [mog22ColsA, mog22ColsB] u 64) := by decide +kernel

theorem mog22End_span : ∀ m < 2 ^ 11,
    m ∈ combos (mog22EndS.map fun u => wAct [mog22ColsA, mog22ColsB] u 64) :=
  mem_combos_of_xorLin (f := id) (fun _ _ => rfl) mog22End_units

theorem equivAut_mog22 :
    ∀ ψ : W11 ≃* W11,
      (∀ (g : ↥mog22) (w : W11), ψ (rho11 mog22 mog22_le_autPerm g w) =
        rho11 mog22 mog22_le_autPerm g (ψ w)) → ψ = MulEquiv.refl W11 := by
  intro ψ hψ
  refine eq_refl_of_words (X := (rho11 mog22 mog22_le_autPerm).range)
    (gs := [mog22RhoA, mog22RhoB]) (cs := [mog22ColsA, mog22ColsB]) ?_ ?_ ?_
    (t0 := 95) (v0 := 64) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (G := mog22EndG) (H := mog22EndH) (S := mog22EndS) (u₂ := mog22EndU2)
    (u₃ := mog22EndU3) mog22EndG_lt mog22EndH_lt mog22EndS_lt mog22EndU2_lt mog22EndU3_lt
    mog22EndG_fix_t0 mog22EndG_fixed mog22EndH_fix_v0 mog22EndH_fixed mog22EndU2_fix_t0
    mog22EndU3_fix_t0
    mog22End_triangle mog22End_span ψ ?_
  · intro i hi
    rcases i with _ | _ | i
    · exact mog22RhoA_mem
    · exact mog22RhoB_mem
    · simp at hi
  · intro i hi
    rcases i with _ | _ | i
    · exact actsBy_mog22RhoA
    · exact actsBy_mog22RhoB
    · simp at hi
  · intro i hi
    rcases i with _ | _ | i
    · exact fun c hc => mog22Cols_lt c (List.mem_append_left _ hc)
    · exact fun c hc => mog22Cols_lt c (List.mem_append_right _ hc)
    · simp at hi
  · rintro _ ⟨g, rfl⟩ w
    exact hψ g w

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
