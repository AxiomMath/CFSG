module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {n : ℕ}

theorem pairVec_apply (a b i : Fin n) :
    pairVec a b i = (if i = a then 1 else 0) + (if i = b then 1 else 0) := by
  simp [pairVec, Pi.single_apply]

theorem actPM_pairVec (σ : Perm (Fin n)) (a b : Fin n) :
    actPM σ (pairVec a b) = pairVec (σ a) (σ b) := by
  funext i
  rw [actPM_apply, pairVec_apply, pairVec_apply]
  have h1 : σ⁻¹ i = a ↔ i = σ a := by
    constructor
    · rintro h; rw [← h, perm_apply_inv_apply]
    · rintro rfl; exact perm_inv_apply_apply σ a
  have h2 : σ⁻¹ i = b ↔ i = σ b := by
    constructor
    · rintro h; rw [← h, perm_apply_inv_apply]
    · rintro rfl; exact perm_inv_apply_apply σ b
  simp only [h1, h2]

theorem actPM_allOnes (σ : Perm (Fin n)) : actPM σ (allOnes n) = allOnes n := rfl

theorem pairVec_mem_of_invariant (hn : 3 ≤ n) {Y : AddSubgroup (Fin n → ZMod 2)}
    (hY : ∀ σ ∈ alternatingGroup (Fin n), ∀ y ∈ Y, actPM σ y ∈ Y) {x : Fin n → ZMod 2}
    (hxY : x ∈ Y) (hx0 : x ≠ 0) (hx1 : x ≠ allOnes n) :
    ∃ p q : Fin n, p ≠ q ∧ pairVec p q ∈ Y := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, x a = 1 := by
    by_contra h
    push Not at h
    exact hx0 (funext fun i => (zmod_two_cases (x i)).resolve_right (h i))
  obtain ⟨b, hb⟩ : ∃ b, x b = 0 := by
    by_contra h
    push Not at h
    exact hx1 (funext fun i => (zmod_two_cases (x i)).resolve_left (h i))
  have hab : a ≠ b := fun h => by rw [h, hb] at ha; exact absurd ha (by decide)
  obtain ⟨c, hc⟩ := exists_notMem_of_card_lt ({a, b} : Finset (Fin n))
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb⟩ := hc
  set σ : Perm (Fin n) := swap a b * swap b c with hσ
  have hσA : σ ∈ alternatingGroup (Fin n) := swap_mul_swap_mem _ hab (Ne.symm hcb)
  have hσa : σ⁻¹ a = c := by
    rw [Perm.inv_eq_iff_eq]; exact (swap_mul_swap_apply_right a b c).symm
  have hσb : σ⁻¹ b = a := by
    rw [Perm.inv_eq_iff_eq]; exact (swap_mul_swap_apply_left hab (Ne.symm hca)).symm
  have hσc : σ⁻¹ c = b := by
    rw [Perm.inv_eq_iff_eq]; exact (swap_mul_swap_apply_mid (Ne.symm hca) (Ne.symm hcb)).symm
  have hσi : ∀ i, i ≠ a → i ≠ b → i ≠ c → σ⁻¹ i = i := fun i hia hib hic => by
    rw [Perm.inv_eq_iff_eq, hσ, Perm.mul_apply, swap_apply_of_ne_of_ne hib hic,
      swap_apply_of_ne_of_ne hia hib]
  have hyY : x + actPM σ x ∈ Y := Y.add_mem hxY (hY σ hσA x hxY)
  have hval : ∀ i, (x + actPM σ x) i = x i + x (σ⁻¹ i) := fun i => rfl
  rcases zmod_two_cases (x c) with hxc | hxc
  · refine ⟨a, b, hab, ?_⟩
    convert hyY using 1
    funext i
    rw [hval, pairVec_apply]
    by_cases hia : i = a
    · subst hia; rw [hσa, ha, hxc]; simp [hab]
    by_cases hib : i = b
    · subst hib; rw [hσb, ha, hb]; simp [hia]
    by_cases hic : i = c
    · subst hic; rw [hσc, hxc, hb]; simp [hia, hib]
    · rw [hσi i hia hib hic, zmod2_add_self]; simp [hia, hib]
  · refine ⟨b, c, Ne.symm hcb, ?_⟩
    convert hyY using 1
    funext i
    rw [hval, pairVec_apply]
    by_cases hia : i = a
    · subst hia; rw [hσa, ha, hxc]; simp [hab, Ne.symm hca]; rfl
    by_cases hib : i = b
    · subst hib; rw [hσb, ha, hb]; simp [Ne.symm hcb]
    by_cases hic : i = c
    · subst hic; rw [hσc, hxc, hb]; simp [hib]
    · rw [hσi i hia hib hic, zmod2_add_self]; simp [hib, hic]

theorem all_pairVec_mem (hn : 5 ≤ n) {Y : AddSubgroup (Fin n → ZMod 2)}
    (hY : ∀ σ ∈ alternatingGroup (Fin n), ∀ y ∈ Y, actPM σ y ∈ Y) {p q : Fin n} (hpq : p ≠ q)
    (h : pairVec p q ∈ Y) : ∀ a b : Fin n, a ≠ b → pairVec a b ∈ Y := by
  intro a b hab
  obtain ⟨g, hga, hgb⟩ := exists_alt_apply_eq_apply_eq hn hpq hab
  have := hY g g.2 _ h
  rwa [actPM_pairVec, hga, hgb] at this

theorem sum_pairVec_apply (ω i : Fin n) :
    (∑ j ∈ Finset.univ.erase ω, pairVec ω j) i =
      if i = ω then ((n - 1 : ℕ) : ZMod 2) else 1 := by
  classical
  rw [Finset.sum_apply]
  simp only [pairVec_apply]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ ω),
    Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq]
  by_cases hi : i = ω
  · simp [hi]
  · simp [hi]

theorem exists_fixed_of_invariant (hn : 5 ≤ n) {Y : AddSubgroup (Fin n → ZMod 2)}
    (hY : ∀ σ ∈ alternatingGroup (Fin n), ∀ y ∈ Y, actPM σ y ∈ Y) (hY0 : Y ≠ ⊥) (ω : Fin n) :
    ∃ u ∈ Y, u ≠ 0 ∧ ∀ σ : Perm (Fin n), σ ω = ω → actPM σ u = u := by
  classical
  have hone : allOnes n ≠ 0 := fun h => by
    have := congrFun h ω
    simp [allOnes] at this
  by_cases h1 : allOnes n ∈ Y
  · exact ⟨allOnes n, h1, hone, fun σ _ => actPM_allOnes σ⟩
  obtain ⟨x, hx0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).1 hY0
  have hx1 : (x : Fin n → ZMod 2) ≠ allOnes n := fun h => h1 (h ▸ x.2)
  obtain ⟨p, q, hpq, hpqY⟩ := pairVec_mem_of_invariant (by omega) hY x.2
    (fun h => hx0 (Subtype.ext h)) hx1
  have hall := all_pairVec_mem hn hY hpq hpqY
  refine ⟨∑ j ∈ Finset.univ.erase ω, pairVec ω j, Y.sum_mem fun j hj =>
    hall ω j (Finset.ne_of_mem_erase hj).symm, ?_, fun σ hσ => ?_⟩
  · obtain ⟨j, hj⟩ := exists_notMem_of_card_lt ({ω} : Finset (Fin n)) (by simp; omega)
    rw [Finset.mem_singleton] at hj
    intro h
    have := congrFun h j
    rw [sum_pairVec_apply] at this
    simp [hj] at this
  · funext i
    rw [actPM_apply, sum_pairVec_apply, sum_pairVec_apply]
    have : σ⁻¹ i = ω ↔ i = ω := by
      rw [Perm.inv_eq_iff_eq, hσ, eq_comm]
    simp only [this]

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
