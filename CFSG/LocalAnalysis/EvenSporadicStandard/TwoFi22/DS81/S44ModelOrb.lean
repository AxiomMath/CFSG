module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelOrb
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ModelPerm

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.FrameCd

open Subgroup CFSG.Sporadic.Fi23 FrameJ Gen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section Defs


@[expose] def orbSet (i : Fin 5) : Set ↥Cd :=
  {y | ∃ n ∈ normalizer (E0 : Set ↥Cd), n * evC (clsRep i.succ) * n⁻¹ = y}

end Defs

section Orbits



theorem orbSet_eq (i : Fin 5) :
    orbSet i = {y | ∃ t : Finset (Fin 23), InCls i.succ t ∧ evC t = y} :=
  orbit_clsRep i.succ

theorem mem_orbSet_iff {i : Fin 5} {y : ↥Cd} :
    y ∈ orbSet i ↔ ∃ t : Finset (Fin 23), InCls i.succ t ∧ evC t = y := by
  rw [orbSet_eq]
  rfl

theorem isOrbit_orbSet (i : Fin 5) :
    ∃ x ∈ E0, orbSet i = {y | ∃ n ∈ normalizer (E0 : Set ↥Cd), n * x * n⁻¹ = y} :=
  ⟨evC (clsRep i.succ), evC_mem _, rfl⟩

theorem ncard_orbSet (i : Fin 5) : (orbSet i).ncard = ![22, 22, 231, 231, 1540] i := by
  rw [orbSet_eq]
  have himg : {y : ↥Cd | ∃ t : Finset (Fin 23), InCls i.succ t ∧ evC t = y} =
      evC '' {t | InCls i.succ t} := rfl
  rw [himg, Set.InjOn.ncard_image, ncard_cls]
  · simp
  · intro t ht t' ht' h
    exact evC_inj (ht.1.trans_le (clsCard_le _)) (ht'.1.trans_le (clsCard_le _)) h

theorem disjoint_orbSet {i j : Fin 5} (h : i ≠ j) : Disjoint (orbSet i) (orbSet j) := by
  rw [Set.disjoint_left]
  intro y hyi hyj
  obtain ⟨t, hti, rfl⟩ := mem_orbSet_iff.1 hyi
  obtain ⟨t', htj, hte⟩ := mem_orbSet_iff.1 hyj
  have htt : t' = t :=
    evC_inj (htj.1.trans_le (clsCard_le _)) (hti.1.trans_le (clsCard_le _)) hte
  exact h (Fin.succ_injective _ (cls_unique hti (htt ▸ htj)))

theorem one_notMem_orbSet (i : Fin 5) : (1 : ↥Cd) ∉ orbSet i := by
  intro h
  obtain ⟨t, ht, h1⟩ := mem_orbSet_iff.1 h
  have hs := evC_eq_one (ht.1.trans_le (clsCard_le _)) h1
  have h1' := one_le_clsCard i.succ
  rw [← ht.1, hs] at h1'
  simp at h1'

theorem dCd_notMem_orbSet (i : Fin 5) : dCd ∉ orbSet i := by
  intro h
  obtain ⟨t, ht, h1⟩ := mem_orbSet_iff.1 h
  have h0 : evC {0} = dCd := (evC_singleton 0).trans fjQ_zero
  have htt : t = {0} :=
    evC_inj (ht.1.trans_le (clsCard_le _)) (by simp) (h1.trans h0.symm)
  rw [htt] at ht
  exact Fin.succ_ne_zero _ (cls_unique ht (inCls_rep 0))

theorem cover_orbSet {v : ↥Cd} (hv : v ∈ E0) (hv1 : v ≠ 1) :
    v = dCd ∨ ∃ i : Fin 5, v ∈ orbSet i := by
  obtain ⟨t, ht3, rfl⟩ := exists_evC hv
  have ht1 : 1 ≤ t.card := by
    rcases Nat.eq_zero_or_pos t.card with h | h
    · exact absurd (by rw [Finset.card_eq_zero.1 h, evC_empty]) hv1
    · exact h
  obtain ⟨j, hj⟩ := exists_cls ht1 ht3
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
  · left
    have hc : t.card = 1 ∧ (0 : Fin 23) ∈ t := by simpa [InCls, clsCard, clsZero] using hj
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc.1
    have ha : a = 0 := (Finset.mem_singleton.1 hc.2).symm
    rw [ha, evC_singleton, fjQ_zero]
  · right
    exact ⟨i, mem_orbSet_iff.2 ⟨t, hj, rfl⟩⟩

theorem orbSet_zero_eq : orbSet 0 = {y | ∃ j : Fin 23, j ≠ 0 ∧ y = fjQ j} := by
  rw [orbSet_eq]
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨j, hj, rfl⟩ := inCls_one_iff.1 ht
    exact ⟨j, hj, evC_singleton j⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨{j}, inCls_one_iff.2 ⟨j, hj, rfl⟩, evC_singleton j⟩

theorem orbSet_one_eq : orbSet 1 = {y | ∃ j : Fin 23, j ≠ 0 ∧ y = dCd * fjQ j} := by
  rw [orbSet_eq]
  have hev : ∀ j : Fin 23, j ≠ 0 → evC {0, j} = dCd * fjQ j := by
    intro j hj
    rw [evC_insert (a := 0) (s := {j}) (by simpa using hj.symm), evC_singleton, fjQ_zero]
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨j, hj, rfl⟩ := inCls_two_iff.1 ht
    exact ⟨j, hj, hev j hj⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨{0, j}, inCls_two_iff.2 ⟨j, hj, rfl⟩, hev j hj⟩

theorem swap_orbSet : orbSet 1 = (fun u => dCd * u) '' orbSet 0 := by
  rw [orbSet_one_eq, orbSet_zero_eq]
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨fjQ j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem prod_orbSet {u u' : ↥Cd} (hu : u ∈ orbSet 0) (hu' : u' ∈ orbSet 0) (hne : u ≠ u') :
    u * u' ∈ orbSet 2 := by
  rw [orbSet_zero_eq] at hu hu'
  obtain ⟨i, hi, rfl⟩ := hu
  obtain ⟨j, hj, rfl⟩ := hu'
  have hij : i ≠ j := fun h => hne (by rw [h])
  rw [mem_orbSet_iff]
  refine ⟨{i, j}, ?_, ?_⟩
  · have e : InCls 3 ({i, j} : Finset (Fin 23)) ↔
        ({i, j} : Finset (Fin 23)).card = 2 ∧ (0 : Fin 23) ∉ ({i, j} : Finset (Fin 23)) := by
      simp [InCls, clsCard, clsZero]
    exact e.2 ⟨Finset.card_pair hij, by simp [hi.symm, hj.symm]⟩
  · rw [evC_insert (a := i) (s := {j}) (by simpa using hij), evC_singleton]

theorem insert_orbSet_zero : insert dCd (orbSet 0) = Set.range (fjQ : Fin 23 → ↥Cd) := by
  rw [orbSet_zero_eq]
  ext y
  constructor
  · rintro (rfl | ⟨j, -, rfl⟩)
    · exact ⟨0, fjQ_zero⟩
    · exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    by_cases hj : j = 0
    · left
      rw [hj, fjQ_zero]
    · right
      exact ⟨j, hj, rfl⟩

end Orbits

end CFSG.EvenSporadicStandard.TwoFi22.DS81.FrameCd
