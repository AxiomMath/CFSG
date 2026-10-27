module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Lin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLatCheck

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Check

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Lin

@[expose] def a1Word : List ℕ := [1, 0]

@[expose] def a2Word : List ℕ := [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1]

@[expose] def wordOf (j : ℕ) : List ℕ := if j = 0 then a1Word else a2Word

@[expose] def aArr (j : ℕ) : Array ℕ := wArr [lzXArr, lzYArr] (wordOf j)

@[expose] def qCols : List ℕ := [15, 1, 2, 4, 8, 0, 0, 0, 0, 0, 0]

theorem wordOf_lt : ∀ j < 2, ∀ g ∈ wordOf j, g < 2 := by decide

theorem qCols_lt : ∀ c ∈ qCols, c < 2 ^ 4 := by decide

theorem actM_qCols_of_mem : ∀ m ∈ combos w0Basis, actM qCols m = 0 := by decide +kernel

theorem mem_combos_of_actM_qCols : ∀ m < 2 ^ 11, actM qCols m = 0 → m ∈ combos w0Basis := by
  decide +kernel

theorem act11_aArr_fix : ∀ j < 2, act11 (aArr j) 32 = 32 ∧ act11 (aArr j) 31 = 31 := by
  decide +kernel

theorem act11_aArr_q_units : ∀ j < 2, ∀ i < 11,
    actM qCols (act11 (aArr j) (2 ^ i)) = actM (mqs.getD j []) (actM qCols (2 ^ i)) := by
  decide +kernel

theorem act11_aArr_q {j : ℕ} (hj : j < 2) : ∀ m < 2 ^ 11,
    actM qCols (act11 (aArr j) m) = actM (mqs.getD j []) (actM qCols m) :=
  xorLin_ext ((actM_xor _).comp (xorLin_act11 _)) ((actM_xor _).comp (actM_xor _)) 11
    (fun i hi => act11_aArr_q_units j hj i hi)

theorem wActM_cPs : ∀ j < 2, ∀ i < 6, wActM (wordOf j) (2 ^ i) = cPs.getD (6 * j + i) 0 := by
  decide +kernel

theorem cArr_central_x : cArr lzXArr r0Arr = cArr (cArr (ksC 34) r0Arr) lzXArr := by
  decide +kernel

theorem cArr_central_y : cArr lzYArr r0Arr = cArr (cArr (ksC 3) r0Arr) lzYArr := by
  decide +kernel

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Check
