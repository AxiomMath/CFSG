module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Slp
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
public import Certificates.Certificate129081
public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Sporadic.Co2Schreier
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit


@[expose] def heisgs : List (Equiv.Perm (Fin 2300)) := aSeeds ++ [locZ, locT, locU]

theorem repTuple_triple {x y z : Array ℕ} {a b c : Equiv.Perm (Fin 2300)} (hx : Rep 2300 x a)
    (hy : Rep 2300 y b) (hz : Rep 2300 z c) : RepTuple 2300 #[x, y, z] [a, b, c] := by
  refine ⟨rfl, fun h hh => ?_⟩
  have hh' : h < 3 := hh
  interval_cases h
  · exact hx
  · exact hy
  · exact hz

theorem heis_triple : RepTuple 2300 #[zArr, tArr, uArr] [locZ, locT, locU] :=
  repTuple_triple rep_z rep_t rep_u

theorem heis_base_rep : RepTuple 2300 (heisBase ()) heisgs :=
  repTuple_a.append heis_triple

theorem heisgs_mem : ∀ g ∈ heisgs, g ∈ co2P := by
  intro g hg
  simp only [heisgs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl | rfl
  · exact aSeeds_mem g hg
  · exact locZ_mem
  · exact locT_mem
  · exact locU_mem

@[expose] def heisVals : List (Equiv.Perm (Fin 2300)) := extendTuple heisgs heisSlp

theorem heis_getD_one_mem' {H : Subgroup (Equiv.Perm (Fin 2300))} {l : List (Equiv.Perm (Fin 2300))}
    (hl : ∀ g ∈ l, g ∈ H) (i : ℕ) : l.getD i 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact H.one_mem
  | some g => exact hl g (List.mem_of_getElem? h)

theorem heisVals_mem (i : ℕ) : heisVals.getD i 1 ∈ co2P :=
  heis_getD_one_mem' (extendTuple_mem co2P heisgs heisSlp heisgs_mem) i

theorem heis_checks : heisCheck () = true := Certificates.certificate129081

theorem heis_stage :
    (∀ e ∈ heisEqs, wordValue heisVals e.1 = wordValue heisVals e.2) ∧
      (∀ e ∈ heisNes, wordValue heisVals e.1 ≠ wordValue heisVals e.2) :=
  slpOK_sound heis_base_rep heis_checks

theorem heis_extendTuple_getD_lt : ∀ (ds : List (List ℤ)) (gs : List (Equiv.Perm (Fin 2300))) (i : ℕ),
    i < gs.length → (extendTuple gs ds).getD i 1 = gs.getD i 1
  | [], gs, i, _ => rfl
  | w :: ds, gs, i, h => by
    rw [extendTuple_cons, heis_extendTuple_getD_lt ds _ i (by simp; omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem heis_z : heisVals.getD 2 1 = locZ := by
  rw [heisVals, heis_extendTuple_getD_lt _ _ _ (by simp [heisgs, aSeeds])]
  simp [heisgs, aSeeds, List.getD_eq_getElem?_getD]

theorem heis_t : heisVals.getD 3 1 = locT := by
  rw [heisVals, heis_extendTuple_getD_lt _ _ _ (by simp [heisgs, aSeeds])]
  simp [heisgs, aSeeds, List.getD_eq_getElem?_getD]

theorem heis_u : heisVals.getD 4 1 = locU := by
  rw [heisVals, heis_extendTuple_getD_lt _ _ _ (by simp [heisgs, aSeeds])]
  simp [heisgs, aSeeds, List.getD_eq_getElem?_getD]

theorem heisCfg_one {G : Type*} [Group G] {p : ℕ} {x y w : G} (hx : x ^ p = 1) (hw : w ^ p = 1)
    (hxw : x * w = w * x) (hyw : y * w = w * y) (hyx : y⁻¹ * x * y = x * w) (hw1 : w ≠ 1) :
    HeisCfg p 1 (fun _ => x) (fun _ => y) w where
  xp _ := hx
  zp := hw
  zx _ := hxw
  zy _ := hyw
  yx _ := hyx
  xx _ _ := rfl
  yy i j h := absurd (Subsingleton.elim i j) h
  xy i j h := absurd (Subsingleton.elim i j) h
  z1 := hw1

theorem heisCfg_two {G : Type*} [Group G] {p : ℕ} {x0 x1 y0 y1 w : G} (hx0 : x0 ^ p = 1)
    (hx1 : x1 ^ p = 1) (hw : w ^ p = 1) (hx0w : x0 * w = w * x0) (hx1w : x1 * w = w * x1)
    (hy0w : y0 * w = w * y0) (hy1w : y1 * w = w * y1) (hy0x : y0⁻¹ * x0 * y0 = x0 * w)
    (hy1x : y1⁻¹ * x1 * y1 = x1 * w) (hxx : x0 * x1 = x1 * x0) (hyy : y0 * y1 = y1 * y0)
    (hx0y1 : x0 * y1 = y1 * x0) (hx1y0 : x1 * y0 = y0 * x1) (hw1 : w ≠ 1) :
    HeisCfg p 2 ![x0, x1] ![y0, y1] w where
  xp i := by fin_cases i <;> simpa
  zp := hw
  zx i := by fin_cases i <;> simpa
  zy i := by fin_cases i <;> simpa
  yx i := by fin_cases i <;> simpa
  xx i j := by
    fin_cases i <;> fin_cases j <;> first | rfl | exact hxx | exact hxx.symm
  yy i j h := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | exact hyy | exact hyy.symm
  xy i j h := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | exact hx0y1 | exact hx1y0
  z1 := hw1

theorem heisA_ambient :
    ∃ (x y : Fin 2 → Equiv.Perm (Fin 2300)) (w : Equiv.Perm (Fin 2300)),
      (∀ i, x i ∈ co2P) ∧ (∀ i, y i ∈ co2P) ∧ w ∈ co2P ∧ HeisCfg 3 2 x y w ∧
      (∀ i, y i ^ 3 = 1) ∧ locZ * x 0 * locZ⁻¹ = (x 0)⁻¹ := by

  have E := heis_stage.1
  have N := heis_stage.2
  have hz := heis_z
  simp only [List.getD_eq_getElem?_getD] at hz

  have htt := E ([3, 3], []) (by simp [heisEqs])
  simp [wordValue, letterValue] at htt

  have hinv := E ([3, 34, 3], [-34]) (by simp [heisEqs])
  simp [wordValue, letterValue] at hinv

  have hne : heisVals.getD 45 1 ≠ 1 := by
    simpa [wordValue, letterValue, List.getD_eq_getElem?_getD] using N ([46], []) (by simp [heisNes])

  refine ⟨![heisVals.getD 33 1, heisVals.getD 37 1], ![heisVals.getD 39 1, heisVals.getD 43 1], heisVals.getD 45 1, ?_, ?_, heisVals_mem _,
    heisCfg_two (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([34, 34, 34], []) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([38, 38, 38], []) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([46, 46, 46], []) (by simp [heisEqs]))
      (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([34, 46], [46, 34]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([38, 46], [46, 38]) (by simp [heisEqs]))
      (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([40, 46], [46, 40]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([44, 46], [46, 44]) (by simp [heisEqs]))
      (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([-40, 34, 40], [34, 46]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([-44, 38, 44], [38, 46]) (by simp [heisEqs]))
      (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([34, 38], [38, 34]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([40, 44], [44, 40]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([34, 44], [44, 34]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([38, 40], [40, 38]) (by simp [heisEqs])) hne,
    ?_, ?_⟩

  · intro i; fin_cases i <;> first | exact heisVals_mem _ | (simp; exact heisVals_mem _)
  · intro i; fin_cases i <;> first | exact heisVals_mem _ | (simp; exact heisVals_mem _)

  · intro i; fin_cases i
    · exact (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([40, 40, 40], []) (by simp [heisEqs]))
    · exact (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([44, 44, 44], []) (by simp [heisEqs]))

  · rw [← hz]
    rw [inv_eq_of_mul_eq_one_right htt]
    simpa [mul_assoc, List.getD_eq_getElem?_getD] using hinv


theorem heisB_ambient :
    ∃ (x y : Fin 1 → Equiv.Perm (Fin 2300)) (w : Equiv.Perm (Fin 2300)),
      (∀ i, x i ∈ co2P) ∧ (∀ i, y i ∈ co2P) ∧ w ∈ co2P ∧ HeisCfg 5 1 x y w ∧
      (∀ i, y i ^ 5 = 1) ∧ locT * x 0 * locT⁻¹ = (x 0)⁻¹ := by

  have E := heis_stage.1
  have N := heis_stage.2
  have hz := heis_t
  simp only [List.getD_eq_getElem?_getD] at hz

  have htt := E ([4, 4], []) (by simp [heisEqs])
  simp [wordValue, letterValue] at htt

  have hinv := E ([4, 77, 4], [-77]) (by simp [heisEqs])
  simp [wordValue, letterValue] at hinv

  have hne : heisVals.getD 80 1 ≠ 1 := by
    simpa [wordValue, letterValue, List.getD_eq_getElem?_getD] using N ([81], []) (by simp [heisNes])

  refine ⟨fun _ => heisVals.getD 76 1, fun _ => heisVals.getD 78 1, heisVals.getD 80 1, fun _ => heisVals_mem _, fun _ => heisVals_mem _, heisVals_mem _,
    heisCfg_one (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([77, 77, 77, 77, 77], []) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([81, 81, 81, 81, 81], []) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([77, 81], [81, 77]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([79, 81], [81, 79]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([-79, 77, 79], [77, 81]) (by simp [heisEqs])) hne, fun _ => (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([79, 79, 79, 79, 79], []) (by simp [heisEqs])), ?_⟩

  · rw [← hz]
    rw [inv_eq_of_mul_eq_one_right htt]
    simpa [mul_assoc, List.getD_eq_getElem?_getD] using hinv


theorem heisC_ambient :
    ∃ (x y : Fin 1 → Equiv.Perm (Fin 2300)) (w : Equiv.Perm (Fin 2300)),
      (∀ i, x i ∈ co2P) ∧ (∀ i, y i ∈ co2P) ∧ w ∈ co2P ∧ HeisCfg 5 1 x y w ∧
      (∀ i, y i ^ 5 = 1) ∧ locU * x 0 * locU⁻¹ = (x 0)⁻¹ := by

  have E := heis_stage.1
  have N := heis_stage.2
  have hz := heis_u
  simp only [List.getD_eq_getElem?_getD] at hz

  have htt := E ([5, 5], []) (by simp [heisEqs])
  simp [wordValue, letterValue] at htt

  have hinv := E ([5, 93, 5], [-93]) (by simp [heisEqs])
  simp [wordValue, letterValue] at hinv

  have hne : heisVals.getD 96 1 ≠ 1 := by
    simpa [wordValue, letterValue, List.getD_eq_getElem?_getD] using N ([97], []) (by simp [heisNes])

  refine ⟨fun _ => heisVals.getD 92 1, fun _ => heisVals.getD 94 1, heisVals.getD 96 1, fun _ => heisVals_mem _, fun _ => heisVals_mem _, heisVals_mem _,
    heisCfg_one (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([93, 93, 93, 93, 93], []) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([97, 97, 97, 97, 97], []) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([93, 97], [97, 93]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([95, 97], [97, 95]) (by simp [heisEqs])) (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([-95, 93, 95], [93, 97]) (by simp [heisEqs])) hne, fun _ => (by simpa [wordValue, letterValue, List.getD_eq_getElem?_getD, mul_assoc, pow_succ] using E ([95, 95, 95, 95, 95], []) (by simp [heisEqs])), ?_⟩

  · rw [← hz]
    rw [inv_eq_of_mul_eq_one_right htt]
    simpa [mul_assoc, List.getD_eq_getElem?_getD] using hinv


end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2
