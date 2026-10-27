module

public import CFSG.Goldschmidt75.Sec41e
public import CFSG.Goldschmidt.Final
public import CFSG.Goldschmidt.Steps.GoldTypeBender

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sq_eq_one_of_mem_omega1 {S : Subgroup G} (hA : IsMulCommutative (Omega1 S)) {x : G}
    (hx : x ∈ Omega1 S) : x ^ 2 = 1 := by
  have hx' : x ∈ closure {t | t ∈ S ∧ t ^ 2 = 1} := hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => simp
  | mul y z hy hz ihy ihz =>
      have hc : y * z = z * y := congrArg Subtype.val (hA.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
      calc (y * z) ^ 2 = y * (z * y) * z := by rw [pow_two]; group
        _ = y * (y * z) * z := by rw [← hc]
        _ = y ^ 2 * z ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [ihy hy, ihz hz, one_mul]
  | inv y hy ihy => rw [inv_pow, ihy hy, inv_one]

theorem exists_conj_normalClosureIn (T : Sylow 2 G) {S H : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) (hSH : S ≤ H) {x : G} (hx : x ∈ H) :
    ∃ m ∈ normalClosureIn H S, conjSub x S = conjSub m S := by
  obtain ⟨PH, hP, -, hc, -⟩ := exists_sylow_subgroupOf T hST hST hS hS (sup_le hSH hSH)
  obtain ⟨m, hm, hmeq⟩ := exists_conj_normalClosure PH hP hc ⟨x, hx⟩
  refine ⟨m, ⟨m, hm, rfl⟩, ?_⟩
  have key : ∀ (a : G) (ha : a ∈ H) (y : G), y ∈ conjSub a S ↔
      ∃ hy : y ∈ H, (⟨y, hy⟩ : H) ∈ conjSub ⟨a, ha⟩ (S.subgroupOf H) := by
    intro a ha y
    rw [mem_conjSub]
    constructor
    · intro h
      have hy : y ∈ H := by
        have : y = a⁻¹ * (a * y * a⁻¹) * a := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem ha) (hSH h)) ha
      exact ⟨hy, mem_conjSub.mpr (mem_subgroupOf.mpr h)⟩
    · rintro ⟨hy, h⟩
      exact mem_subgroupOf.mp (mem_conjSub.mp h)
  ext y
  rw [key x hx, key (m : G) m.2]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, hmeq ▸ h⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, hmeq ▸ h⟩

variable {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.omega1_not_comm
    (h : MinCE G T S₁ S₂) : ¬ IsMulCommutative (Omega1 S₁) := by
  intro hA
  have := h.isSimpleGroup
  have hO := h.oddCore_eq_bot
  have hAS : Omega1 S₁ ≤ S₁ := GoldType.omega1_le S₁
  have hAT : Omega1 S₁ ≤ T := hAS.trans h.le₁
  have hcl : fusionStronglyClosed ((Omega1 S₁ : Subgroup G) : Set G) T := by
    intro a ha g hg
    refine GoldType.mem_omega1 (h.sc₁ a (hAS ha) g hg) ?_
    have e : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by rw [pow_two, pow_two]; group
    rw [e, sq_eq_one_of_mem_omega1 hA ha, mul_one, inv_mul_cancel]
  obtain ⟨z₁, hz₁S, hz₁2, -⟩ := exists_central_involution T h.le₁ h.sc₁ h.ne_bot
  have hz₁A : z₁ ∈ Omega1 S₁ :=
    GoldType.mem_omega1 hz₁S (by rw [← hz₁2]; exact pow_orderOf_eq_one z₁)
  have htop : normalClosure ((Omega1 S₁ : Subgroup G) : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (normalClosure ((Omega1 S₁ : Subgroup G) : Set G)) with h0 | h0
    · exfalso
      have h1 : z₁ ∈ normalClosure ((Omega1 S₁ : Subgroup G) : Set G) := subset_normalClosure hz₁A
      rw [h0, mem_bot] at h1
      exact ne_one_of_orderOf_eq_two hz₁2 h1
    · exact h0
  obtain ⟨h1, h2, -⟩ := CFSG.Goldschmidt.coreStatement G T (Omega1 S₁) hAT hA hcl htop hO
  obtain ⟨z₂, hz₂S, hz₂2, -⟩ := exists_central_involution T h.le₂ h.sc₂ h.symm.ne_bot
  have hz₂sq : z₂ ^ 2 = 1 := by rw [← hz₂2]; exact pow_orderOf_eq_one z₂
  have hz₂A : z₂ ∈ Omega1 S₁ := by
    rw [h2]
    have := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal (G := G) 2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 G) with hP | hP
    · rw [hP, bot_sup_eq] at h1 ⊢
      exact subset_closure ⟨⟨h.le₂ hz₂S, by rw [h1]; exact mem_top z₂⟩, hz₂sq⟩
    · rw [hP]
      exact mem_sup_left (mem_top z₂)
  have h3 : z₂ ∈ S₁ ⊓ S₂ := ⟨hAS hz₂A, hz₂S⟩
  rw [h.disj, mem_bot] at h3
  exact ne_one_of_orderOf_eq_two hz₂2 h3

theorem MinCE.exists_isKleinFour
    (h : MinCE G T S₁ S₂) : ∃ V ≤ S₁, IsKleinFour V := by
  by_contra hno
  push Not at hno
  apply h.omega1_not_comm
  obtain ⟨z, hzS, hz2, hzc⟩ :=
    exists_central_involution_of_isPGroup (T.isPGroup'.to_le h.le₁) h.ne_bot
  have hall : ∀ t ∈ S₁, t ^ 2 = 1 → t ∈ zpowers z := by
    intro t ht ht2
    by_cases ht1 : t = 1
    · rw [ht1]
      exact one_mem _
    by_cases htz : t = z
    · rw [htz]
      exact mem_zpowers z
    exact absurd (isKleinFour_sup (orderOf_eq_prime ht2 ht1) hz2 htz (hzc t ht))
      (hno _ (sup_le (zpowers_le.mpr ht) (zpowers_le.mpr hzS)))
  have hle : Omega1 S₁ ≤ zpowers z := (closure_le _).mpr fun t ht => hall t ht.1 ht.2
  refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hle a.2)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hle b.2)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

end CFSG.Goldschmidt75
