module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Subgroups
public import Certificates.Certificate450250

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_cons evalWord_nil)
open CFSG.YGroups (yRels ngen)
open CFSG.Sporadic.Recognition.Fi22Multiplier (f332Word)
open CFSG.Sporadic.LevelChain.Native (levelTrees levelLv)

@[expose] def y332Words : List (List ℤ) :=
  (yRels 3 3 2 ++ [f332Word]).map fun w => w.map fun (c : ℕ) => (c : ℤ) + 1

structure Y332Facts (run : Array Table × Bool) (ws : List (List ℤ)) : Prop where
  flag : run.2 = true
  size : run.1.size = 113
  prog : progOK 113 (y332Prog ()) = true
  data : y332DataOK () = true
  gensSize : (y332Gens run.1).size = 71
  nine : y332NineOK ((y332Gens run.1).extract 0 9) ws = true
  trees : y332TreesOK (y332Letters (y332Gens run.1))
    (levelTrees degree (y332Letters (y332Gens run.1)) y332Starts y332Base) = true
  nest : y332NestOK (y332Gens run.1) (y332Lines ()) = true

theorem Y332Facts.of_y332OKAt {run : Array Table × Bool} {ws : List (List ℤ)}
    (h : y332OKAt run ws = true) : Y332Facts run ws := by
  unfold y332OKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem y332OK_eq_true : y332OK y332Words = true :=
  Certificates.certificate450250

theorem y332Facts : Y332Facts (y332Run ()) y332Words :=
  Y332Facts.of_y332OKAt y332OK_eq_true

abbrev y332Tabs : Array Table := (y332Run ()).1

theorem nine_parts {g9 : Array Table} {ws : List (List ℤ)} (h : y332NineOK g9 ws = true) :
    g9.size = 9 ∧ (∀ j < 9, ap g9[j]! 0 = 0 ∧ ap g9[j]! 1479 = 1479) ∧
      relatorsOK degree g9 (g9.map (invT degree)) ws = true := by
  unfold y332NineOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun j hj => ?_, h3⟩
  have := (allIn_eq_true.1 h2) j (Nat.zero_le _) hj
  simpa using this

theorem y332TreesOK_parts {letters : Array Table} {trees : Array CFSG.Perm.Native.Tree}
    (h : y332TreesOK letters trees = true) :
    letters.size = 2 * y332Starts[8]! ∧
      (∀ j < 71, invOK degree letters[2 * j]! letters[2 * j + 1]! = true) ∧
      trees.size = 8 ∧
      (∀ i < 8, CFSG.Perm.Native.treeOK degree y332Base[i]! trees[i]! letters
        (levelLv y332Starts i) = true) ∧
      (∀ i, 1 ≤ i → i < 8 → ∀ j, y332Starts[i]! ≤ j → j < y332Starts[i + 1]! →
        ap letters[2 * j]! y332Base[i - 1]! = y332Base[i - 1]!) ∧
      (∀ i < 8, trees[i]!.pts.size = y332Sizes[i]!) := by
  unfold y332TreesOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, fun j hj => (allIn_eq_true.1 h2) j (Nat.zero_le _) hj, h3,
    fun i hi => (allIn_eq_true.1 h4) i (Nat.zero_le _) hi, ?_,
    fun i hi => by simpa using (allIn_eq_true.1 h6) i (Nat.zero_le _) hi⟩
  intro i hi1 hi j hj1 hj2
  have := (allIn_eq_true.1 ((allIn_eq_true.1 h5) i hi1 hi)) j hj1 hj2
  simpa using this

theorem y332NestOK_parts {gens : Array Table} {lines : Array (List ℤ)}
    (h : y332NestOK gens lines = true) {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 8) {j : ℕ}
    (hj1 : y332Starts[i]! ≤ j) (hj2 : j < y332Starts[i + 1]!) :
    (∀ z ∈ y332Word lines[j + 39]!,
      y332Starts[i - 1]! + 1 ≤ z.natAbs ∧ z.natAbs ≤ y332Starts[i]!) ∧
      eqTab degree (wordT degree (letterTab degree gens (gens.map (invT degree)))
        (y332Word lines[j + 39]!)) gens[j]! = true := by
  simp only [y332NestOK] at h
  have h1 := (allIn_eq_true.1 h) i hi1 hi
  have h2 := (allIn_eq_true.1 h1) j hj1 hj2
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h2
  exact ⟨fun z hz => h2.1 z hz, h2.2⟩

theorem y332Gens_size (tabs : Array Table) : (y332Gens tabs).size = 71 := by
  simp [y332Gens]

theorem y332Gens_get (tabs : Array Table) {j : ℕ} (hj : j < 71) :
    (y332Gens tabs)[j]! = tabs[y332Reg j]! := by
  unfold y332Gens
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

theorem y332Letters_size (gens : Array Table) : (y332Letters gens).size = 142 := by
  simp [y332Letters]

theorem y332Letters_even (gens : Array Table) {j : ℕ} (hj : j < 71) :
    (y332Letters gens)[2 * j]! = gens[j]! := by
  unfold y332Letters
  rw [getElem!_pos _ (2 * j) (by simp; omega), Array.getElem_ofFn]
  have h1 : 2 * j % 2 = 0 := by omega
  have h2 : 2 * j / 2 = j := by omega
  simp [h1, h2]

theorem y332Letters_odd (gens : Array Table) {j : ℕ} (hj : j < 71) :
    (y332Letters gens)[2 * j + 1]! = invT degree gens[j]! := by
  unfold y332Letters
  rw [getElem!_pos _ (2 * j + 1) (by simp; omega), Array.getElem_ofFn]
  have h1 : ¬ (2 * j + 1) % 2 = 0 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [h1, h2]

theorem y332Reg_lt {j : ℕ} (hj : j < 71) : y332Reg j < 113 := by
  unfold y332Reg
  split_ifs <;> omega

theorem extract_get (gens : Array Table) {j : ℕ} (hj : j < 9) (hs : 9 ≤ gens.size) :
    (gens.extract 0 9)[j]! = gens[j]! := by
  rw [getElem!_pos _ j (by simp [Array.size_extract]; omega), getElem!_pos gens j (by omega)]
  simp [Array.getElem_extract]

noncomputable def y332Elt (r : ℕ) : Q3 := runSLPG (y332Prog ()) mQ r

theorem rep_y332Elt {r : ℕ}
    (hr : r < 113) : Rep 920808 y332Tabs[r]! (y332Elt r) := by
  have hprog : ∀ ins ∈ y332Prog (), instrRegsLt (2 + 111) ins :=
    instrRegsLt_of_progOK y332Facts.prog
  have hok : (runSLP 920808 (y332Prog ()) (mTabs () ++ Array.replicate 111 (idT 920808))).2 =
      true := y332Facts.flag
  exact rep_runSLP_m (y332Prog ()) 111 hprog hok r (by omega)

noncomputable def y332Gen (j : ℕ) : Q3 := y332Elt (y332Reg j)

theorem rep_y332Gen_tab {j : ℕ}
    (hj : j < 71) : Rep 920808 y332Tabs[y332Reg j]! (y332Gen j) :=
  rep_y332Elt (y332Reg_lt hj)

theorem rep_y332Gen {j : ℕ}
    (hj : j < 71) : Rep 920808 (y332Gens y332Tabs)[j]! (y332Gen j) := by
  rw [y332Gens_get _ hj]
  exact rep_y332Gen_tab hj

@[expose] noncomputable def y332Perm (j : ℕ) : Perm Ω :=
  rho (y332Gen j)

theorem rep_y332Perm {j : ℕ}
    (hj : j < 71) : Rep 920808 (y332Gens y332Tabs)[j]! (y332Perm j) :=
  rep_iff_rho.1 (rep_y332Gen hj)

theorem invOK_y332Gens {j : ℕ} (hj : j < 71) :
    invOK 920808 (y332Gens y332Tabs)[j]! (invT 920808 (y332Gens y332Tabs)[j]!) = true := by
  have h := (y332TreesOK_parts y332Facts.trees).2.1 j hj
  rwa [y332Letters_even _ hj, y332Letters_odd _ hj] at h

theorem nine_fix {j : ℕ} (hj : j < 9) :
    ap y332Tabs[y332Reg j]! 0 = 0 ∧ ap y332Tabs[y332Reg j]! 1479 = 1479 := by
  obtain ⟨-, hfix, -⟩ := nine_parts y332Facts.nine
  have := hfix j hj
  rwa [extract_get (y332Gens y332Tabs) hj (by rw [y332Gens_size]; omega),
    y332Gens_get y332Tabs (j := j) (by omega)] at this

theorem y332Gen_smul_x0 {j : ℕ}
    (hj : j < 9) : y332Gen j • x0 = x0 := by
  apply Fin.ext
  rw [smul_val_of_rep (rep_y332Gen_tab (j := j) (by omega)) x0, x0_val]
  exact (nine_fix hj).1

theorem y332Gen_smul_x1 {j : ℕ}
    (hj : j < 9) : y332Gen j • x1 = x1 := by
  apply Fin.ext
  rw [smul_val_of_rep (rep_y332Gen_tab (j := j) (by omega)) x1, x1_val]
  exact (nine_fix hj).2

theorem y332Gen_mem_L0
    {j : ℕ} (hj : j < 9) : y332Gen j ∈ L0 := by
  rw [mem_L0_iff, Zp_eq_stabilizer, MulAction.mem_stabilizer_iff]
  exact ⟨y332Gen_smul_x0 hj, y332Gen_smul_x1 hj⟩

theorem letterPerm_succ {G : Type*} [Group G] (π : ℕ → G) {m c : ℕ} (hc : c < m) :
    letterPerm π m ((c : ℤ) + 1) = π c := by
  have h1 : (0 : ℤ) < (c : ℤ) + 1 := by omega
  have h2 : ((c : ℤ) + 1 - 1).toNat = c := by omega
  have hcond : 0 < (c : ℤ) + 1 ∧ ((c : ℤ) + 1 - 1).toNat < m := ⟨h1, by rw [h2]; exact hc⟩
  unfold letterPerm
  rw [if_pos hcond, h2]

theorem evalWord_eq_wordG {G : Type*} [Group G] (π : ℕ → G) {m : ℕ} :
    ∀ w : List ℕ, (∀ c ∈ w, c < m) →
      evalWord π w = wordG (letterPerm π m) (w.map fun (c : ℕ) => (c : ℤ) + 1)
  | [], _ => by simp [wordG]
  | c :: w, h => by
    have hc : c < m := h c List.mem_cons_self
    have ih := evalWord_eq_wordG π w fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    have e : wordG (letterPerm π m) ((c :: w).map fun (c : ℕ) => (c : ℤ) + 1) =
        letterPerm π m ((c : ℤ) + 1) *
          wordG (letterPerm π m) (w.map fun (c : ℕ) => (c : ℤ) + 1) := by
      simp [wordG]
    rw [e, ← ih, letterPerm_succ π hc, evalWord_cons]

theorem y332_rels :
    ∀ w ∈ yRels 3 3 2 ++ [f332Word], evalWord y332Perm w = 1 := by
  intro w hw
  obtain ⟨hsz, -, hrel⟩ := nine_parts y332Facts.nine
  have hlt : ∀ c ∈ w, c < 9 := by
    rcases List.mem_append.1 hw with hw | hw
    · intro c hc
      simpa [ngen] using CFSG.YGroups.lt_ngen_of_mem_yRels hw c hc
    · rw [List.mem_singleton] at hw
      subst hw
      decide
  have hmem : w.map (fun (c : ℕ) => (c : ℤ) + 1) ∈ y332Words := List.mem_map_of_mem hw
  have hgs : ((y332Gens y332Tabs).extract 0 9).size = 9 := hsz
  have hrepE : ∀ l < ((y332Gens y332Tabs).extract 0 9).size,
      Rep 920808 ((y332Gens y332Tabs).extract 0 9)[l]! (y332Perm l) := by
    intro l hl
    rw [hgs] at hl
    rw [extract_get (y332Gens y332Tabs) hl (by rw [y332Gens_size]; omega)]
    exact rep_y332Perm (by omega)
  have hinvE : ∀ l < ((y332Gens y332Tabs).extract 0 9).size,
      invOK 920808 ((y332Gens y332Tabs).extract 0 9)[l]!
        (invT 920808 ((y332Gens y332Tabs).extract 0 9)[l]!) = true := by
    intro l hl
    rw [hgs] at hl
    rw [extract_get (y332Gens y332Tabs) hl (by rw [y332Gens_size]; omega)]
    exact invOK_y332Gens (by omega)
  have h := wordG_eq_one_of_relatorsOK (n := 920808) (by norm_num)
    (gs := (y332Gens y332Tabs).extract 0 9) (π := y332Perm) hrepE hinvE hrel hmem
  rw [hgs] at h
  rw [evalWord_eq_wordG y332Perm (m := 9) w hlt]
  exact h

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
