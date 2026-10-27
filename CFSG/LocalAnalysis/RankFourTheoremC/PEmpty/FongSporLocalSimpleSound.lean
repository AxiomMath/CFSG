module

public import Mathlib.Data.List.GetD
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimpleDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

namespace PSimple

variable {G : Type*} [Group G]

theorem elemsAux_length (c : PSimple) (g1 g2 : G) (m : ℕ) :
    (c.elemsAux g1 g2 m).length = m := by
  induction m with
  | zero => simp [elemsAux]
  | succ m ih => simp [elemsAux, ih]

theorem elemsAux_getD_stable (c : PSimple) (g1 g2 : G) {j m m' : ℕ} (hjm : j < m)
    (hmm' : m ≤ m') :
    (c.elemsAux g1 g2 m').getD j 1 = (c.elemsAux g1 g2 m).getD j 1 := by
  induction m', hmm' using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hlt : j < (c.elemsAux g1 g2 k).length := by rw [elemsAux_length]; omega
    rw [elemsAux, List.getD_append _ _ _ _ hlt, ih]

theorem elemsAux_getD_zero (c : PSimple) (g1 g2 : G) {m : ℕ} (hm : 0 < m) :
    (c.elemsAux g1 g2 m).getD 0 1 = 1 := by
  rw [elemsAux_getD_stable (j := 0) (m := 1) (m' := m) c g1 g2 (by omega) (by omega)]
  simp [elemsAux]

theorem elems_length (c : PSimple) (g1 g2 : G) : (c.elems g1 g2).length = c.par.length :=
  elemsAux_length c g1 g2 _

theorem elems_getD_zero (c : PSimple) (g1 g2 : G) (hn : 0 < c.par.length) :
    (c.elems g1 g2).getD 0 1 = 1 :=
  elemsAux_getD_zero c g1 g2 hn

theorem elems_getD_succ (c : PSimple) (g1 g2 : G) {k : ℕ} (hk : k < c.par.length) (hk0 : k ≠ 0)
    (hpk : c.par.getD k 0 < k) :
    (c.elems g1 g2).getD k 1 = (c.elems g1 g2).getD (c.par.getD k 0) 1 *
      (if c.gen.getD k false then g2 else g1) := by
  have hlen : (c.elemsAux g1 g2 k).length = k := elemsAux_length c g1 g2 k
  have h1 : (c.elemsAux g1 g2 c.par.length).getD k 1 = (c.elemsAux g1 g2 (k + 1)).getD k 1 :=
    elemsAux_getD_stable (j := k) (m := k + 1) (m' := c.par.length) c g1 g2 (by omega) (by omega)
  have h2 : (c.elemsAux g1 g2 (k + 1)).getD k 1 =
      (c.elemsAux g1 g2 k).getD (c.par.getD k 0) 1 * (if c.gen.getD k false then g2 else g1) := by
    rw [elemsAux, List.getD_append_right _ _ _ _ (le_of_eq hlen), hlen, Nat.sub_self, if_neg hk0]
    rfl
  have h3 : (c.elemsAux g1 g2 k).getD (c.par.getD k 0) 1 =
      (c.elemsAux g1 g2 c.par.length).getD (c.par.getD k 0) 1 :=
    (elemsAux_getD_stable (j := c.par.getD k 0) (m := k) (m' := c.par.length) c g1 g2 hpk
      (by omega)).symm
  unfold elems
  rw [h1, h2, h3]

theorem sound [DecidableEq G] (c : PSimple) (g1 g2 z : G) (h : c.check g1 g2 z = true) :
    IsSimpleGroup ↥(Subgroup.closure ({g1, g2} : Set G)) ∧
      ¬ IsMulCommutative ↥(Subgroup.closure ({g1, g2} : Set G)) ∧
      z ∈ Subgroup.closure ({g1, g2} : Set G) ∧
      3 ∣ Nat.card ↥(Subgroup.closure ({g1, g2} : Set G)) := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, and_assoc] at h
  obtain ⟨hn, -, -, -, -, ho1, ho2, hh1, hh2, hK, hreps, hI, hnab, hk3p, hk3n, hkz⟩ := h
  have hpar : ∀ k, 0 < k → k < c.par.length →
      c.par.getD k 0 < k ∧ (c.elems g1 g2).getD k 1 =
        (c.elems g1 g2).getD (c.par.getD k 0) 1 * (if c.gen.getD k false then g2 else g1) := by
    intro k hk0 hk
    have hpk : c.par.getD k 0 < k := (hK k hk).1.resolve_left (by omega)
    exact ⟨hpk, elems_getD_succ c g1 g2 hk (by omega) hpk⟩
  have hsuc : ∀ k, k < c.par.length →
      c.suc1.getD k 0 < c.par.length ∧ c.suc2.getD k 0 < c.par.length ∧
      (c.elems g1 g2).getD k 1 * g1 = (c.elems g1 g2).getD (c.suc1.getD k 0) 1 ∧
      (c.elems g1 g2).getD k 1 * g2 = (c.elems g1 g2).getD (c.suc2.getD k 0) 1 := by
    intro k hk
    obtain ⟨-, h1, h2, h3, h4, -⟩ := hK k hk
    exact ⟨h1, h2, h3, h4⟩
  have hrep : ∀ i, i < c.reps.length → c.reps.getD i 0 < c.par.length := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact hreps _ (List.getElem_mem hi)
  obtain ⟨hA, hB, hC⟩ := simpleGroup_of_cert g1 g2 c.par.length hn
    (fun k => (c.elems g1 g2).getD k 1) (elems_getD_zero c g1 g2 hn)
    (fun k => c.par.getD k 0) (fun k => c.gen.getD k false) hpar c.o1 c.o2 ho1 ho2 hh1 hh2
    (fun k => c.suc1.getD k 0) (fun k => c.suc2.getD k 0) hsuc c.reps.length
    (fun i => c.reps.getD i 0) hrep (fun k => c.cls.getD k none)
    (by
      intro k hk
      try dsimp only
      obtain ⟨-, -, -, -, -, hm⟩ := hK k hk
      revert hm
      generalize c.cls.getD k none = ck
      intro hm
      rcases ck with _ | ⟨u, i⟩
      · simpa using hm
      · simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hm
        exact hm)
    (fun i j => if j then (c.nc.getD i ([], [])).2 else (c.nc.getD i ([], [])).1)
    (by
      intro i hi j
      obtain ⟨hI1, hI2, hI3, hI4⟩ := hI i hi
      cases j
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hI1, hI3⟩
      · simp only [↓reduceIte]
        exact ⟨hI2, hI4⟩)
    hnab
  have hall : ∀ k, (c.elems g1 g2).getD k 1 ∈ Subgroup.closure ({g1, g2} : Set G) := by
    intro k
    by_cases hk : k < c.par.length
    · exact hC k hk
    · have hlen : (c.elems g1 g2).length ≤ k := by rw [elems_length]; omega
      rw [List.getD_eq_default _ _ hlen]
      exact Subgroup.one_mem _
  have hz : z ∈ Subgroup.closure ({g1, g2} : Set G) := by
    rw [← hkz]
    exact hall c.kz
  have hord : orderOf ((c.elems g1 g2).getD c.k3 1) = 3 := orderOf_eq_prime hk3p hk3n
  exact ⟨hA, hB, hz, three_dvd_card_of_orderOf_three (hall c.k3) hord⟩

end PSimple

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

end
