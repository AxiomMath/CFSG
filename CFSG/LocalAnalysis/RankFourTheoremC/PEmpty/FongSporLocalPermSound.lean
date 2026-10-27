module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermDefs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open Subgroup

theorem evalPW_mem {G : Type*} [Group G] (a b : G) (w : PW) :
    evalPW a b w ∈ Subgroup.closure ({a, b} : Set G) := by
  induction w with
  | nil =>
    simp only [evalPW]
    exact one_mem _
  | cons x w ih =>
    obtain ⟨c, e⟩ := x
    simp only [evalPW]
    refine mul_mem (pow_mem ?_ e) ih
    cases c
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

@[expose] def evalPWN {G : Type*} [Group G] (a b : G) (w : PW) :
    ↥(Subgroup.closure ({a, b} : Set G)) :=
  ⟨evalPW a b w, evalPW_mem a b w⟩

@[simp] theorem coe_evalPWN {G : Type*} [Group G] (a b : G) (w : PW) :
    ((evalPWN a b w : ↥(Subgroup.closure ({a, b} : Set G))) : G) = evalPW a b w :=
  rfl

theorem PGen.holds_of_check {G : Type*} [Group G] [DecidableEq G] (a b : G) (c : PGen)
    (h : c.check a b = true) : c.holds a b := by
  unfold PGen.check at h
  unfold PGen.holds
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, fun w hw => ⟨(h3 w hw).1.1, (h3 w hw).1.2, (h3 w hw).2⟩,
    fun n hn => h4 n hn, fun m hm => ?_, h6, h7⟩
  obtain ⟨w, hw, hx⟩ := h5 m hm
  exact ⟨w, hw, hx⟩

theorem evalIdx_mem {G : Type*} [Group G] (xs : List G) (T : Subgroup G)
    (hT : ∀ x ∈ xs, x ∈ T) (wd : List (ℕ × ℕ)) : evalIdx xs wd ∈ T := by
  induction wd with
  | nil =>
    simp only [evalIdx]
    exact one_mem _
  | cons ie w ih =>
    obtain ⟨i, e⟩ := ie
    have hx : xs.getD i 1 ∈ T := by
      rw [List.getD_eq_getElem?_getD]
      by_cases hi : i < xs.length
      · rw [List.getElem?_eq_getElem hi]
        exact hT _ (List.getElem_mem hi)
      · have hi' : xs.length ≤ i := by omega
        rw [List.getElem?_eq_none hi']
        exact one_mem _
    simp only [evalIdx]
    exact mul_mem (pow_mem hx e) ih

theorem closure_eq_top_of_le_map {G : Type*} [Group G] (N : Subgroup G) (S : Set ↥N)
    (h : N ≤ (Subgroup.closure S).map N.subtype) : Subgroup.closure S = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp (h g.2)
  obtain rfl : y = g := Subtype.ext hyg
  exact hy

theorem closure_le_of_regs {G : Type*} [Group G] (a b : G) (c : PGen) (U : Subgroup G)
    (hU : ∀ x ∈ c.regs a b, x ∈ U)
    (ha : a = evalIdx (c.regs a b) c.wa) (hb : b = evalIdx (c.regs a b) c.wb) :
    Subgroup.closure ({a, b} : Set G) ≤ U := by
  have ha' : a ∈ U := by
    have := evalIdx_mem (c.regs a b) U hU c.wa
    rwa [← ha] at this
  have hb' : b ∈ U := by
    have := evalIdx_mem (c.regs a b) U hU c.wb
    rwa [← hb] at this
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · rw [hx]
    exact ha'
  · rw [Set.mem_singleton_iff.mp hx]
    exact hb'

@[expose] def genSet {G : Type*} [Group G] (a b : G) (c : PGen) :
    Set ↥(Subgroup.closure ({a, b} : Set G)) :=
  {x | ∃ n ∈ c.ns, x = evalPWN a b n.1} ∪ {x | ∃ m ∈ c.ms, x = evalPWN a b m.1}

theorem mem_genSet_ns {G : Type*} [Group G] (a b : G) (c : PGen) {n : PW × ℕ × ℕ}
    (hn : n ∈ c.ns) : evalPWN a b n.1 ∈ genSet a b c :=
  Or.inl ⟨n, hn, rfl⟩

theorem mem_genSet_ms {G : Type*} [Group G] (a b : G) (c : PGen) {m : PW × ℕ}
    (hm : m ∈ c.ms) : evalPWN a b m.1 ∈ genSet a b c :=
  Or.inr ⟨m, hm, rfl⟩

theorem genW_top {G : Type*} [Group G] (a b : G) (c : PGen)
    (ha : a = evalIdx (c.regs a b) c.wa) (hb : b = evalIdx (c.regs a b) c.wb) :
    Subgroup.closure (genSet a b c) = ⊤ := by
  apply closure_eq_top_of_le_map
  refine closure_le_of_regs a b c _ ?_ ha hb
  intro x hx
  simp only [PGen.regs, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨n, hn, rfl⟩ | ⟨m, hm, rfl⟩
  · exact Subgroup.mem_map.mpr
      ⟨evalPWN a b n.1, Subgroup.subset_closure (mem_genSet_ns a b c hn), rfl⟩
  · exact Subgroup.mem_map.mpr
      ⟨evalPWN a b m.1, Subgroup.subset_closure (mem_genSet_ms a b c hm), rfl⟩

theorem mem_normalizer_zpowers_of {K : Type*} [Group K] (x z : K) (k k' : ℕ)
    (h4 : x * z * x⁻¹ = z ^ k) (h5 : x * z ^ k' * x⁻¹ = z) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers z : Set K) := by
  have hc : ∀ j : ℤ, x * z ^ j * x⁻¹ = z ^ ((k : ℤ) * j) := by
    intro j
    rw [← conj_zpow, h4, ← zpow_natCast, ← zpow_mul]
  have e : x⁻¹ * z * x = z ^ k' := by
    calc x⁻¹ * z * x = x⁻¹ * (x * z ^ k' * x⁻¹) * x := by rw [h5]
      _ = z ^ k' := by group
  have hc' : ∀ j : ℤ, x⁻¹ * z ^ j * x = z ^ ((k' : ℤ) * j) := by
    intro j
    have hj := conj_zpow (i := j) (a := x⁻¹) (b := z)
    rw [inv_inv] at hj
    rw [← hj, e, ← zpow_natCast, ← zpow_mul]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨(k : ℤ) * j, by rw [hc j]⟩
  · rintro ⟨j, hj⟩
    refine ⟨(k' : ℤ) * j, ?_⟩
    rw [← hc' j, hj]
    group

theorem genW_exists_of_holds {G : Type*} [Group G] (a b : G) (c : PGen) (hp : c.p.Prime)
    (h : c.holds a b) :
    ∃ (z₀ : ↥(Subgroup.closure ({a, b} : Set G)))
      (ns ms : Set ↥(Subgroup.closure ({a, b} : Set G))),
      orderOf z₀ = c.p ∧
      (∀ n ∈ ns, n ∈ Subgroup.normalizer (Subgroup.zpowers z₀ : Set ↥(Subgroup.closure ({a, b} : Set G)))) ∧
      (∀ m ∈ ms, ∃ t : ↥(Subgroup.closure ({a, b} : Set G)), t * t = 1 ∧ t ≠ 1 ∧
        z₀ * t = t * z₀ ∧ m * t = t * m) ∧
      Subgroup.closure (ns ∪ ms) = ⊤ := by
  have hfact : Fact c.p.Prime := ⟨hp⟩
  have hz : evalPWN a b c.z ^ c.p = 1 := Subtype.ext (by simpa using h.1)
  have hz1 : evalPWN a b c.z ≠ 1 := fun e => h.2.1 (by simpa using congrArg Subtype.val e)
  refine ⟨evalPWN a b c.z, {x | ∃ n ∈ c.ns, x = evalPWN a b n.1},
    {x | ∃ m ∈ c.ms, x = evalPWN a b m.1}, orderOf_eq_prime hz hz1, ?_, ?_,
    genW_top a b c h.2.2.2.2.2.1 h.2.2.2.2.2.2⟩
  · rintro x ⟨n, hn, rfl⟩
    obtain ⟨h4, h5⟩ := h.2.2.2.1 n hn
    exact mem_normalizer_zpowers_of _ _ n.2.1 n.2.2
      (Subtype.ext (by simpa using h4)) (Subtype.ext (by simpa using h5))
  · rintro x ⟨m, hm, rfl⟩
    obtain ⟨w, hw, hcomm⟩ := h.2.2.2.2.1 m hm
    obtain ⟨hw1, hw2, hw3⟩ := h.2.2.1 w hw
    refine ⟨evalPWN a b w, Subtype.ext (by simpa using hw1),
      fun e => hw2 (by simpa using congrArg Subtype.val e),
      Subtype.ext (by simpa using hw3), Subtype.ext (by simpa using hcomm)⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
