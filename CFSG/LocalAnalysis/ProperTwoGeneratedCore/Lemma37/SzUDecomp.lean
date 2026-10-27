module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

variable {X : Type*} [Group X]

theorem exists_mul_eq_of_le_sup_centralizer [Finite X] (Sb : Sylow 2 X) {J : Subgroup X}
    [J.Normal] (hJK : J ⊓ Subgroup.centralizer (J : Set X) = ⊥)
    (hS : (Sb : Subgroup X) ≤ J ⊔ Subgroup.centralizer (J : Set X)) {w : X}
    (hw : w ∈ (Sb : Subgroup X)) :
    ∃ x ∈ (Sb : Subgroup X) ⊓ J, ∃ k ∈ (Sb : Subgroup X) ⊓ Subgroup.centralizer (J : Set X),
      x * k = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.centralizer (J : Set X) with hKdef
  obtain ⟨x, hxJ, k, hkK, hxk⟩ := Subgroup.mem_sup_of_normal_right.mp (hS hw)
  have hcxk : x * k = k * x := Subgroup.mem_centralizer_iff.mp hkK x hxJ
  have hconj : ∀ y ∈ J, x * y * x⁻¹ = w * y * w⁻¹ := by
    intro y hy
    have hky : y * k = k * y := Subgroup.mem_centralizer_iff.mp hkK y hy
    rw [← hxk]
    calc x * y * x⁻¹ = x * (y * k) * k⁻¹ * x⁻¹ := by group
      _ = x * (k * y) * k⁻¹ * x⁻¹ := by rw [hky]
      _ = x * k * y * (x * k)⁻¹ := by group
  obtain ⟨a, ha⟩ := Sb.isPGroup' ⟨w, hw⟩
  have hwa : w ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hxa : x ^ 2 ^ a = 1 := by
    rw [← hxk, Commute.mul_pow hcxk] at hwa
    have hxK : x ^ 2 ^ a ∈ K := by
      rw [eq_inv_of_mul_eq_one_left hwa]
      exact K.inv_mem (K.pow_mem hkK _)
    have h : x ^ 2 ^ a ∈ J ⊓ K := Subgroup.mem_inf.mpr ⟨J.pow_mem hxJ _, hxK⟩
    rwa [hJK, Subgroup.mem_bot] at h
  set R' := CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal Sb J
  have hR' : ∀ v : J, v ∈ (R' : Subgroup J) ↔ (v : X) ∈ (Sb : Subgroup X) := by
    intro v
    rw [CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
    rfl
  set x' : J := ⟨x, hxJ⟩
  have hxN : x' ∈ Subgroup.normalizer ((R' : Subgroup J) : Set J) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    rw [hR', hR']
    change (v : X) ∈ (Sb : Subgroup X) ↔ x * v * x⁻¹ ∈ (Sb : Subgroup X)
    rw [hconj v v.2]
    constructor
    · intro hv
      exact Sb.mul_mem (Sb.mul_mem hw hv) (Sb.inv_mem hw)
    · intro hv
      have h := Sb.mul_mem (Sb.mul_mem (Sb.inv_mem hw) hv) hw
      rwa [show w⁻¹ * (w * (v : X) * w⁻¹) * w = v by group] at h
  have hx'a : x' ^ 2 ^ a = 1 := Subtype.ext (by simpa [x'] using hxa)
  have hx'P : IsPGroup 2 (Subgroup.zpowers x') := by
    rintro ⟨g, i, rfl⟩
    refine ⟨a, Subtype.ext ?_⟩
    change (x' ^ i) ^ 2 ^ a = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'a, one_zpow]
  have hmem := (hx'P.inf_normalizer_sylow R').le ⟨Subgroup.mem_zpowers x', hxN⟩
  have hxS : x ∈ (Sb : Subgroup X) := (hR' x').mp (Subgroup.mem_inf.mp hmem).2
  refine ⟨x, ⟨hxS, hxJ⟩, k, ⟨?_, hkK⟩, hxk⟩
  rw [eq_inv_mul_of_mul_eq hxk]
  exact Sb.mul_mem (Sb.inv_mem hxS) hw

theorem mem_sup_centralizer_of_odd_outer {J : Subgroup X} [J.Normal]
    (hodd : Odd (Nat.card (Outer J))) {w : X} {a : ℕ} (hw : w ^ 2 ^ a = 1) :
    w ∈ J ⊔ Subgroup.centralizer (J : Set X) := by
  set α : MulAut J := MulAut.conjNormal w
  have hα : α ^ 2 ^ a = 1 := by rw [← map_pow, hw, map_one]
  have hP : IsPGroup 2 (Subgroup.zpowers α) := by
    rintro ⟨g, i, rfl⟩
    refine ⟨a, Subtype.ext ?_⟩
    change (α ^ i) ^ 2 ^ a = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  obtain ⟨j, hj⟩ := HighRankPair.le_inner_of_isPGroup_two hodd _ hP (Subgroup.mem_zpowers α)
  have hc : ∀ y ∈ J, (j : X) * y * (j : X)⁻¹ = w * y * w⁻¹ := by
    intro y hy
    have h := congrArg Subtype.val (DFunLike.congr_fun hj ⟨y, hy⟩)
    simpa [α, MulAut.conjNormal_apply] using h
  have hjw : (j : X)⁻¹ * w ∈ Subgroup.centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hc y hy
    calc y * ((j : X)⁻¹ * w) = (j : X)⁻¹ * ((j : X) * y * (j : X)⁻¹) * w := by group
      _ = (j : X)⁻¹ * (w * y * w⁻¹) * w := by rw [h]
      _ = (j : X)⁻¹ * w * y := by group
  rw [show w = (j : X) * ((j : X)⁻¹ * w) by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left j.2) (Subgroup.mem_sup_right hjw)

theorem odd_card_outer_of_mulEquiv_suzukiMatrixGroup
    {L : Type*} [Group L] {m : ℕ}
    (hm : 1 ≤ m) (e : L ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    Odd (Nat.card (Outer L)) := by
  have h := HighRankPair.suzukiOuterOdd m hm
  change Odd (Nat.card (Outer (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) at h
  rwa [← Nat.card_congr (equivalence e).toEquiv] at h

end CFSG.ProperTwoGeneratedCore.Lemma37
