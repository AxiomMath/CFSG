module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open Equiv

@[expose] def IsA7CommutingPair (σ u w : Perm (Fin 7)) : Prop :=
  u ∈ alternatingGroup (Fin 7) ∧ w ∈ alternatingGroup (Fin 7) ∧ u ^ 2 = 1 ∧ w ^ 2 = 1 ∧
    u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧ u * σ = σ * u ∧ w * σ = σ * w

theorem isA7CommutingPair_one :
    IsA7CommutingPair 1 (swap 0 1 * swap 2 3) (swap 0 2 * swap 1 3) := by
  unfold IsA7CommutingPair
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

theorem isA7CommutingPair_one_swap :
    IsA7CommutingPair (swap 0 1) (swap 2 3 * swap 4 5) (swap 2 4 * swap 3 5) := by
  unfold IsA7CommutingPair
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

theorem isA7CommutingPair_two_swaps :
    IsA7CommutingPair (swap 0 1 * swap 2 3) (swap 0 1 * swap 2 3) (swap 0 2 * swap 1 3) := by
  unfold IsA7CommutingPair
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

theorem isA7CommutingPair_three_swaps :
    IsA7CommutingPair (swap 0 1 * swap 2 3 * swap 4 5) (swap 0 1 * swap 2 3)
      (swap 0 1 * swap 4 5) := by
  unfold IsA7CommutingPair
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide

theorem IsA7CommutingPair.conj {σ u w : Perm (Fin 7)} (h : IsA7CommutingPair σ u w)
    (τ : Perm (Fin 7)) : IsA7CommutingPair (τ * σ * τ⁻¹) (τ * u * τ⁻¹) (τ * w * τ⁻¹) := by
  obtain ⟨hu, hw, hu2, hw2, hu1, hw1, huw, hc, huσ, hwσ⟩ := h
  have hA : ∀ x ∈ alternatingGroup (Fin 7), τ * x * τ⁻¹ ∈ alternatingGroup (Fin 7) :=
    fun x hx => (alternatingGroup.normal (α := Fin 7)).conj_mem x hx τ
  refine ⟨hA u hu, hA w hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conj_pow, hu2]; group
  · rw [conj_pow, hw2]; group
  · intro h
    apply hu1
    calc u = τ⁻¹ * (τ * u * τ⁻¹) * τ := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hw1
    calc w = τ⁻¹ * (τ * w * τ⁻¹) * τ := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply huw
    calc u = τ⁻¹ * (τ * u * τ⁻¹) * τ := by group
      _ = τ⁻¹ * (τ * w * τ⁻¹) * τ := by rw [h]
      _ = w := by group
  · calc τ * u * τ⁻¹ * (τ * w * τ⁻¹) = τ * (u * w) * τ⁻¹ := by group
      _ = τ * (w * u) * τ⁻¹ := by rw [hc]
      _ = τ * w * τ⁻¹ * (τ * u * τ⁻¹) := by group
  · calc τ * u * τ⁻¹ * (τ * σ * τ⁻¹) = τ * (u * σ) * τ⁻¹ := by group
      _ = τ * (σ * u) * τ⁻¹ := by rw [huσ]
      _ = τ * σ * τ⁻¹ * (τ * u * τ⁻¹) := by group
  · calc τ * w * τ⁻¹ * (τ * σ * τ⁻¹) = τ * (w * σ) * τ⁻¹ := by group
      _ = τ * (σ * w) * τ⁻¹ := by rw [hwσ]
      _ = τ * σ * τ⁻¹ * (τ * w * τ⁻¹) := by group

theorem cycleType_swap_fin_seven {a b : Fin 7} (h : a ≠ b) : (swap a b).cycleType = {2} := by
  rw [(Perm.isCycle_swap h).cycleType, Perm.card_support_swap h]

theorem cycleType_swap_one : (swap (0 : Fin 7) 1).cycleType = Multiset.replicate 1 2 := by
  rw [cycleType_swap_fin_seven (by decide), Multiset.replicate_one]

theorem cycleType_swap_two :
    (swap (0 : Fin 7) 1 * swap 2 3).cycleType = Multiset.replicate 2 2 := by
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide),
    cycleType_swap_fin_seven (by decide),
    cycleType_swap_fin_seven (by decide)]
  rfl

theorem cycleType_swap_three :
    (swap (0 : Fin 7) 1 * swap 2 3 * swap 4 5).cycleType = Multiset.replicate 3 2 := by
  rw [Perm.Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide), cycleType_swap_two,
    cycleType_swap_fin_seven (by decide)]
  rfl

theorem perm_seven_commuting_pair (σ : Perm (Fin 7)) (hσ : σ ^ 2 = 1) :
    ∃ u w : Perm (Fin 7), IsA7CommutingPair σ u w := by
  by_cases h1 : σ = 1
  · subst h1
    exact ⟨_, _, isA7CommutingPair_one⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime hσ h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsum : (n + 1) * 2 ≤ 7 := by
    have h1 := Perm.sum_cycleType σ
    rw [hn, Multiset.sum_replicate, smul_eq_mul] at h1
    rw [h1]
    exact (Finset.card_le_univ _).trans (by simp)
  have hconj : ∀ ρ : Perm (Fin 7), ρ.cycleType = Multiset.replicate (n + 1) 2 →
      ∃ τ : Perm (Fin 7), τ * ρ * τ⁻¹ = σ := by
    intro ρ hρ
    have : IsConj ρ σ := Perm.isConj_iff_cycleType_eq.mpr (by rw [hρ, hn])
    exact isConj_iff.mp this
  have hn2 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn2 with rfl | rfl | rfl
  · obtain ⟨τ, hτ⟩ := hconj (swap 0 1) cycleType_swap_one
    exact ⟨_, _, hτ ▸ isA7CommutingPair_one_swap.conj τ⟩
  · obtain ⟨τ, hτ⟩ := hconj (swap 0 1 * swap 2 3) cycleType_swap_two
    exact ⟨_, _, hτ ▸ isA7CommutingPair_two_swaps.conj τ⟩
  · obtain ⟨τ, hτ⟩ := hconj (swap 0 1 * swap 2 3 * swap 4 5) cycleType_swap_three
    exact ⟨_, _, hτ ▸ isA7CommutingPair_three_swaps.conj τ⟩

theorem a7_involution_commuting_pair {R : Type*} [Group R] (N : Subgroup R) [N.Normal]
    (e : N ≃* alternatingGroup (Fin 7)) (r : R) (hr : r ^ 2 = 1) :
    ∃ u w : N, u ^ 2 = 1 ∧ w ^ 2 = 1 ∧ u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w ∧ u * w = w * u ∧
      r * u = u * r ∧ r * w = w * r := by
  have hc := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  let β : MulAut N := MulAut.conjNormal r
  have hβ : ∀ n : N, (β n : R) = r * n * r⁻¹ := fun n => MulAut.conjNormal_apply r n
  have hββ : ∀ n, β (β n) = n := by
    intro n
    apply Subtype.ext
    rw [hβ, hβ]
    calc r * (r * (n : R) * r⁻¹) * r⁻¹ = (r * r) * n * (r * r)⁻¹ := by group
      _ = n := by rw [← pow_two, hr]; group
  let α : MulAut (alternatingGroup (Fin 7)) := MulAut.congr e β
  have hα : ∀ b, α b = e (β (e.symm b)) := fun b => rfl
  obtain ⟨σ, hσ⟩ := hc.2 α
  have hσ2 : σ ^ 2 = 1 := by
    apply hc.1
    rw [map_pow, hσ, map_one]
    apply MulEquiv.ext
    intro b
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, hα, hα, MulEquiv.symm_apply_apply, hββ,
      MulEquiv.apply_symm_apply]
  have hσα : ∀ b : alternatingGroup (Fin 7), σ * (b : Perm (Fin 7)) * σ⁻¹ =
      (α b : Perm (Fin 7)) := by
    intro b
    rw [← hσ, MulAut.conjNormal_apply]
  obtain ⟨u, w, hu, hw, hu2, hw2, hu1, hw1, huw, hc', huσ, hwσ⟩ := perm_seven_commuting_pair σ hσ2
  have hpull : ∀ x : Perm (Fin 7), (hx : x ∈ alternatingGroup (Fin 7)) → x * σ = σ * x →
      r * (e.symm ⟨x, hx⟩ : R) = (e.symm ⟨x, hx⟩ : R) * r := by
    intro x hx hxσ
    have h1 : α ⟨x, hx⟩ = ⟨x, hx⟩ := by
      apply Subtype.ext
      rw [← hσα]
      change σ * x * σ⁻¹ = x
      rw [← hxσ]
      group
    rw [hα] at h1
    have h2 : β (e.symm ⟨x, hx⟩) = e.symm ⟨x, hx⟩ := by
      apply e.injective
      rw [h1, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    rw [hβ] at h3
    calc r * (e.symm ⟨x, hx⟩ : R) = r * (e.symm ⟨x, hx⟩ : R) * r⁻¹ * r := by group
      _ = (e.symm ⟨x, hx⟩ : R) * r := by rw [h3]
  have hsq : ∀ x : Perm (Fin 7), (hx : x ∈ alternatingGroup (Fin 7)) → x ^ 2 = 1 →
      (e.symm ⟨x, hx⟩) ^ 2 = 1 := by
    intro x hx hx2
    rw [← map_pow]
    have : (⟨x, hx⟩ : alternatingGroup (Fin 7)) ^ 2 = 1 := Subtype.ext (by simp [hx2])
    rw [this, map_one]
  have hne : ∀ x y : Perm (Fin 7), (hx : x ∈ alternatingGroup (Fin 7)) →
      (hy : y ∈ alternatingGroup (Fin 7)) → x ≠ y → e.symm ⟨x, hx⟩ ≠ e.symm ⟨y, hy⟩ := by
    intro x y hx hy hxy h
    apply hxy
    have := congrArg Subtype.val (e.symm.injective h)
    exact this
  have h1 : (1 : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := Subgroup.one_mem _
  have hone : e.symm ⟨1, h1⟩ = 1 := by
    rw [← map_one e.symm]
    rfl
  refine ⟨e.symm ⟨u, hu⟩, e.symm ⟨w, hw⟩, hsq u hu hu2, hsq w hw hw2, ?_, ?_,
    hne u w hu hw huw, ?_, hpull u hu huσ, hpull w hw hwσ⟩
  · rw [← hone]
    exact hne u 1 hu h1 hu1
  · rw [← hone]
    exact hne w 1 hw h1 hw1
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc'

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
