module

public import Mathlib.Data.List.GetD
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

namespace PSimple

theorem sound_of_props {G : Type*} [Group G] (c : PSimple) (hwf : c.wfB = true) (s : ℕ → G)
    (g1 g2 z : G) (hs0 : s 0 = 1)
    (hpar : ∀ k, 0 < k → k < c.par.length →
      s k = s (c.par.getD k 0) * (if c.gen.getD k false then g2 else g1))
    (hg1 : g1 ^ c.o1 = 1) (hg2 : g2 ^ c.o2 = 1)
    (hsuc : ∀ k, k < c.par.length →
      s k * g1 = s (c.suc1.getD k 0) ∧ s k * g2 = s (c.suc2.getD k 0))
    (hcls : ∀ k, k < c.par.length → match c.cls.getD k none with
      | none => s k = 1
      | some (u, i) => s k * s u = s u * s (c.reps.getD i 0))
    (hnc : ∀ i, i < c.reps.length → ((c.nc.getD i ([], [])).1.map s).prod = g1 ∧
      ((c.nc.getD i ([], [])).2.map s).prod = g2)
    (hnab : g1 * g2 ≠ g2 * g1) (h3 : s c.k3 ^ 3 = 1) (h3' : s c.k3 ≠ 1) (hz : s c.kz = z) :
    IsSimpleGroup ↥(Subgroup.closure ({g1, g2} : Set G)) ∧
      ¬ IsMulCommutative ↥(Subgroup.closure ({g1, g2} : Set G)) ∧
      z ∈ Subgroup.closure ({g1, g2} : Set G) ∧
      3 ∣ Nat.card ↥(Subgroup.closure ({g1, g2} : Set G)) := by
  unfold wfB at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    and_assoc] at hwf
  obtain ⟨hn, -, -, -, -, ho1, ho2, hK, hreps, hI, hk3, hkz⟩ := hwf
  have hpar' : ∀ k, 0 < k → k < c.par.length →
      c.par.getD k 0 < k ∧
        s k = s (c.par.getD k 0) * (if c.gen.getD k false then g2 else g1) := by
    intro k hk0 hk
    exact ⟨((hK k hk).1).resolve_left (by omega), hpar k hk0 hk⟩
  have hsuc' : ∀ k, k < c.par.length → c.suc1.getD k 0 < c.par.length ∧
      c.suc2.getD k 0 < c.par.length ∧ s k * g1 = s (c.suc1.getD k 0) ∧
      s k * g2 = s (c.suc2.getD k 0) := by
    intro k hk
    obtain ⟨-, h1, h2, -⟩ := hK k hk
    exact ⟨h1, h2, (hsuc k hk).1, (hsuc k hk).2⟩
  have hrep : ∀ i, i < c.reps.length → c.reps.getD i 0 < c.par.length := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact hreps _ (List.getElem_mem hi)
  obtain ⟨hA, hB, hC⟩ := simpleGroup_of_cert g1 g2 c.par.length hn s hs0
    (fun k => c.par.getD k 0) (fun k => c.gen.getD k false) hpar' c.o1 c.o2 ho1 ho2 hg1 hg2
    (fun k => c.suc1.getD k 0) (fun k => c.suc2.getD k 0) hsuc' c.reps.length
    (fun i => c.reps.getD i 0) hrep (fun k => c.cls.getD k none)
    (by
      intro k hk
      try dsimp only
      obtain ⟨-, -, -, hm⟩ := hK k hk
      have hc := hcls k hk
      revert hm hc
      generalize c.cls.getD k none = ck
      intro hm hc
      rcases ck with _ | ⟨u, i⟩
      · simpa using hc
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        exact ⟨hm.1, hm.2, hc⟩)
    (fun i j => if j then (c.nc.getD i ([], [])).2 else (c.nc.getD i ([], [])).1)
    (by
      intro i hi j
      obtain ⟨hI1, hI2⟩ := hI i hi
      cases j
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hI1, (hnc i hi).1⟩
      · simp only [↓reduceIte]
        exact ⟨hI2, (hnc i hi).2⟩)
    hnab
  have hz' : z ∈ Subgroup.closure ({g1, g2} : Set G) := by
    rw [← hz]
    exact hC c.kz hkz
  exact ⟨hA, hB, hz', three_dvd_card_of_orderOf_three (hC c.k3 hk3) (orderOf_eq_prime h3 h3')⟩

theorem wfB_spec {c : PSimple} (hwf : c.wfB = true) :
    0 < c.par.length ∧
    (∀ k, k < c.par.length → (k = 0 ∨ c.par.getD k 0 < k) ∧ c.suc1.getD k 0 < c.par.length ∧
      c.suc2.getD k 0 < c.par.length ∧
      ∀ u i, c.cls.getD k none = some (u, i) → u < c.par.length ∧ i < c.reps.length) ∧
    (∀ r ∈ c.reps, r < c.par.length) ∧
    (∀ i, i < c.reps.length → (∀ l ∈ (c.nc.getD i ([], [])).1, l < c.par.length) ∧
      ∀ l ∈ (c.nc.getD i ([], [])).2, l < c.par.length) ∧
    c.k3 < c.par.length ∧ c.kz < c.par.length := by
  unfold wfB at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    and_assoc] at hwf
  obtain ⟨hn, -, -, -, -, -, -, hK, hreps, hI, hk3, hkz⟩ := hwf
  refine ⟨hn, fun k hk => ?_, hreps, fun i hi => ?_, hk3, hkz⟩
  · obtain ⟨h1, h2, h3, hm⟩ := hK k hk
    refine ⟨h1, h2, h3, fun u i hui => ?_⟩
    simp only [hui, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact hm
  · obtain ⟨hI1, hI2⟩ := hI i hi
    exact ⟨fun l hl => (hI1 l hl).1, fun l hl => (hI2 l hl).1⟩

end PSimple

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
