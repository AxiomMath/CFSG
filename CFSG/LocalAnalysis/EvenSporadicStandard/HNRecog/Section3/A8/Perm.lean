module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma mem_alt_mul_swap (a b c d : Fin 8) (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hcd]
  decide

private lemma cycleType_mul_swap_swap (a b c d : Fin 8) (hab : a ≠ b) (hcd : c ≠ d)
    (hdisj : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c d)) :
    (Equiv.swap a b * Equiv.swap c d).cycleType = {2, 2} := by
  rw [Equiv.Perm.Disjoint.cycleType_mul hdisj, (Equiv.Perm.isCycle_swap hab).cycleType,
    (Equiv.Perm.isCycle_swap hcd).cycleType, Equiv.Perm.card_support_swap hab,
    Equiv.Perm.card_support_swap hcd]
  norm_num [Multiset.replicate_succ]

private lemma commute_swap_self (s : Equiv.Perm (Fin 8)) (hs2 : s ^ 2 = 1) (i : Fin 8) :
    s * Equiv.swap i (s i) = Equiv.swap i (s i) * s := by
  have hss : ∀ y, s (s y) = y := by
    intro y
    have h := congrArg (fun p : Equiv.Perm (Fin 8) => p y) hs2
    simpa [pow_two, Equiv.Perm.coe_mul] using h
  apply Equiv.ext
  intro x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rcases eq_or_ne x i with hx | hx
  · rw [hx, Equiv.swap_apply_left, Equiv.swap_apply_right]
    simpa using hss i
  rcases eq_or_ne x (s i) with hx' | hx'
  · rw [hx', Equiv.swap_apply_right, hss i, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
    have h1 : s x ≠ i := by
      intro h
      apply hx'
      have h' := congrArg s h
      rwa [hss x] at h'
    have h2 : s x ≠ s i := by
      intro h
      exact hx (s.injective h)
    simpa using (Equiv.swap_apply_of_ne_of_ne h1 h2).symm

theorem cycleType_eq_of_sq_eq_one {s : alternatingGroup (Fin 8)} (hs : s ^ 2 = 1) (hne : s ≠ 1) :
    (s : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∨
      (s : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  have h2 : (s : Equiv.Perm (Fin 8)) ^ 2 = 1 := by
    have h := congrArg Subtype.val hs
    simpa using h
  have hct : (s : Equiv.Perm (Fin 8)).cycleType =
      Multiset.replicate (s : Equiv.Perm (Fin 8)).cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  have hcardpos : 0 < (s : Equiv.Perm (Fin 8)).cycleType.card := by
    rw [Equiv.Perm.card_cycleType_pos]
    intro h1
    exact hne (Subtype.ext h1)
  have hle : (s : Equiv.Perm (Fin 8)).cycleType.card ≤ 4 := by
    have h := (s : Equiv.Perm (Fin 8)).sum_cycleType_le
    rw [hct, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h
    omega
  have heven : Even (s : Equiv.Perm (Fin 8)).cycleType.card := by
    have hsign : Equiv.Perm.sign (s : Equiv.Perm (Fin 8)) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp s.2
    rw [Equiv.Perm.sign_of_cycleType, hct, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul] at hsign
    have hsign' : (-1 : ℤˣ) ^ (s : Equiv.Perm (Fin 8)).cycleType.card = 1 := by
      have h3 : (s : Equiv.Perm (Fin 8)).cycleType.card * 2 +
          (s : Equiv.Perm (Fin 8)).cycleType.card =
          3 * (s : Equiv.Perm (Fin 8)).cycleType.card := by ring
      rw [h3, pow_mul] at hsign
      have h3' : (-1 : ℤˣ) ^ 3 = -1 := by decide
      rwa [h3'] at hsign
    exact (neg_one_pow_eq_one_iff_even (by decide)).mp hsign'
  have hcard : (s : Equiv.Perm (Fin 8)).cycleType.card = 2 ∨
      (s : Equiv.Perm (Fin 8)).cycleType.card = 4 := by
    obtain ⟨m, hm⟩ := heven
    omega
  rw [hct]
  rcases hcard with h | h
  · left; rw [h]; norm_num [Multiset.replicate_succ]
  · right; rw [h]; norm_num [Multiset.replicate_succ]

theorem sq_eq_one_of_cycleType_two_two {s : alternatingGroup (Fin 8)}
    (hs : (s : Equiv.Perm (Fin 8)).cycleType = {2, 2}) : s ^ 2 = 1 ∧ s ≠ 1 := by
  have horder : orderOf (s : Equiv.Perm (Fin 8)) = 2 := by
    rw [← Equiv.Perm.lcm_cycleType, hs]
    decide
  have hpow : (s : Equiv.Perm (Fin 8)) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, horder]
  constructor
  · apply Subtype.ext
    simpa using hpow
  · intro h1
    have h1' : (s : Equiv.Perm (Fin 8)) = 1 := by rw [h1]; rfl
    rw [h1', Equiv.Perm.cycleType_one] at hs
    exact (by decide : (0 : Multiset ℕ) ≠ {2, 2}) hs

theorem sq_eq_one_of_cycleType_two_two_two_two {s : alternatingGroup (Fin 8)}
    (hs : (s : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}) : s ^ 2 = 1 ∧ s ≠ 1 := by
  have horder : orderOf (s : Equiv.Perm (Fin 8)) = 2 := by
    rw [← Equiv.Perm.lcm_cycleType, hs]
    decide
  have hpow : (s : Equiv.Perm (Fin 8)) ^ 2 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, horder]
  constructor
  · apply Subtype.ext
    simpa using hpow
  · intro h1
    have h1' : (s : Equiv.Perm (Fin 8)) = 1 := by rw [h1]; rfl
    rw [h1', Equiv.Perm.cycleType_one] at hs
    exact (by decide : (0 : Multiset ℕ) ≠ {2, 2, 2, 2}) hs

theorem isConj_of_cycleType_two_two {s t : alternatingGroup (Fin 8)}
    (hs : (s : Equiv.Perm (Fin 8)).cycleType = {2, 2})
    (ht : (t : Equiv.Perm (Fin 8)).cycleType = {2, 2}) : IsConj s t := by
  apply alternatingGroup.isConj_of
  · exact Equiv.Perm.isConj_iff_cycleType_eq.2 (hs.trans ht.symm)
  · have hcard : (s : Equiv.Perm (Fin 8)).support.card = 4 := by
      rw [← Equiv.Perm.sum_cycleType, hs]
      decide
    rw [hcard]
    decide

theorem isConj_of_cycleType_two_two_two_two {s t : alternatingGroup (Fin 8)}
    (hs : (s : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2})
    (ht : (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}) : IsConj s t := by
  have hs2 : (s : Equiv.Perm (Fin 8)) ^ 2 = 1 := by
    have h := (sq_eq_one_of_cycleType_two_two_two_two hs).1
    simpa using congrArg Subtype.val h
  have hne : (s : Equiv.Perm (Fin 8)) ≠ 1 := by
    intro h1
    exact (sq_eq_one_of_cycleType_two_two_two_two hs).2 (Subtype.ext h1)
  have hc : IsConj (s : Equiv.Perm (Fin 8)) (t : Equiv.Perm (Fin 8)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.2 (hs.trans ht.symm)
  obtain ⟨π, hπ⟩ := isConj_iff.1 hc
  by_cases hsign : Equiv.Perm.sign π = 1
  · refine isConj_iff.2 ⟨⟨π, ?_⟩, ?_⟩
    · rwa [Equiv.Perm.mem_alternatingGroup]
    · apply Subtype.ext
      simpa using hπ
  · have hsign' : Equiv.Perm.sign π = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
      · exact absurd h hsign
      · exact h
    have hex : ∃ i : Fin 8, (s : Equiv.Perm (Fin 8)) i ≠ i := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext fun i => by simpa using h i)
    obtain ⟨i, hi⟩ := hex
    let c : Equiv.Perm (Fin 8) := Equiv.swap i ((s : Equiv.Perm (Fin 8)) i)
    have hcomm : (s : Equiv.Perm (Fin 8)) * c = c * (s : Equiv.Perm (Fin 8)) :=
      commute_swap_self (s : Equiv.Perm (Fin 8)) hs2 i
    have hsc : c * (s : Equiv.Perm (Fin 8)) * c⁻¹ = (s : Equiv.Perm (Fin 8)) := by
      rw [← hcomm]; group
    refine isConj_iff.2 ⟨⟨π * c, ?_⟩, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, hsign', Equiv.Perm.sign_swap hi.symm]
      decide
    · apply Subtype.ext
      have hconj : (π * c) * (s : Equiv.Perm (Fin 8)) * (π * c)⁻¹ =
          (t : Equiv.Perm (Fin 8)) := by
        calc (π * c) * (s : Equiv.Perm (Fin 8)) * (π * c)⁻¹
            = π * (c * (s : Equiv.Perm (Fin 8)) * c⁻¹) * π⁻¹ := by group
          _ = π * (s : Equiv.Perm (Fin 8)) * π⁻¹ := by rw [hsc]
          _ = (t : Equiv.Perm (Fin 8)) := hπ
      simpa using hconj

private def tA : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 5 6, mem_alt_mul_swap 3 4 5 6 (by decide) (by decide)⟩

private def t1A : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, mem_alt_mul_swap 0 1 3 4 (by decide) (by decide)⟩

private def t2A : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 3 4, mem_alt_mul_swap 0 2 3 4 (by decide) (by decide)⟩

theorem exists_triple_cycleType_two_two : ∃ t t₁ t₂ : alternatingGroup (Fin 8),
    (t : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧ (t₁ : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧
    (t₂ : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧
    ((t * t₁ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧
    ((t * t₂ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧
    t * t₁ = t₁ * t ∧ t * t₂ = t₂ * t ∧ orderOf (t₁ * t₂) = 3 := by
  refine ⟨tA, t1A, t2A, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cycleType_mul_swap_swap 3 4 5 6 (by decide) (by decide)
      (Equiv.Perm.disjoint_swap_swap (by decide))
  · exact cycleType_mul_swap_swap 0 1 3 4 (by decide) (by decide)
      (Equiv.Perm.disjoint_swap_swap (by decide))
  · exact cycleType_mul_swap_swap 0 2 3 4 (by decide) (by decide)
      (Equiv.Perm.disjoint_swap_swap (by decide))
  · have h : ((tA * t1A : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        Equiv.swap 5 6 * Equiv.swap 0 1 := by decide +kernel
    rw [h]
    exact cycleType_mul_swap_swap 5 6 0 1 (by decide) (by decide)
      (Equiv.Perm.disjoint_swap_swap (by decide))
  · have h : ((tA * t2A : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        Equiv.swap 5 6 * Equiv.swap 0 2 := by decide +kernel
    rw [h]
    exact cycleType_mul_swap_swap 5 6 0 2 (by decide) (by decide)
      (Equiv.Perm.disjoint_swap_swap (by decide))
  · decide +kernel
  · decide +kernel
  · have h : ((t1A * t2A : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
        Equiv.swap 0 1 * Equiv.swap 0 2 := by decide +kernel
    rw [← Subgroup.orderOf_coe (t1A * t2A), h]
    exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).orderOf

private def e1 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, mem_alt_mul_swap 0 1 2 3 (by decide) (by decide)⟩

private def e2 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, mem_alt_mul_swap 0 2 1 3 (by decide) (by decide)⟩

private def e3 : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 4 5 * Equiv.swap 6 7, mem_alt_mul_swap 4 5 6 7 (by decide) (by decide)⟩

private def eElems : Finset (alternatingGroup (Fin 8)) :=
  {1, e1, e2, e3, e1 * e2, e1 * e3, e2 * e3, e1 * e2 * e3}

private def eSub : Subgroup (alternatingGroup (Fin 8)) where
  carrier := {x | x ∈ eElems}
  one_mem' := by decide +kernel
  inv_mem' := by
    intro a ha
    change a ∈ eElems at ha
    simp only [eElems, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h | h | h | h | h | h | h | h <;> rw [h] <;> decide +kernel
  mul_mem' := by
    intro a b ha hb
    change a ∈ eElems at ha
    change b ∈ eElems at hb
    simp only [eElems, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with h | h | h | h | h | h | h | h <;>
      rcases hb with k | k | k | k | k | k | k | k <;>
      rw [h, k] <;> decide +kernel

private instance instDecidableMemESub : DecidablePred (· ∈ eSub) := fun x => by
  change Decidable (x ∈ eElems)
  infer_instance

theorem exists_isElemTwo_three : ∃ E : Subgroup (alternatingGroup (Fin 8)), IsElemTwo 3 E := by
  refine ⟨eSub, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have ha : a.val ∈ eElems := a.property
    have hb : b.val ∈ eElems := b.property
    simp only [eElems, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with h | h | h | h | h | h | h | h <;>
      rcases hb with k | k | k | k | k | k | k | k <;>
      rw [h, k] <;> decide +kernel
  · intro x hx
    change x ∈ eElems at hx
    simp only [eElems, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;> decide +kernel
  · rw [show Nat.card ↥eSub = Nat.card ↥eElems from rfl]
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    decide +kernel

theorem eq_one_of_forall_commute {t : alternatingGroup (Fin 8)}
    (ht : ∀ s : alternatingGroup (Fin 8), s * t = t * s) : t = 1 := by
  have hmem : t ∈ Subgroup.center (alternatingGroup (Fin 8)) := by
    rw [Subgroup.mem_center_iff]
    exact ht
  have hbot : Subgroup.center (alternatingGroup (Fin 8)) = ⊥ :=
    alternatingGroup.center_eq_bot (α := Fin 8) (by simp)
  rw [hbot] at hmem
  simpa using hmem

theorem isElemTwo_map {A B : Type} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f)
    {n : ℕ} {E : Subgroup A} (hE : IsElemTwo n E) : IsElemTwo n (E.map f) := by
  obtain ⟨⟨hcomm, hexp⟩, hcard⟩ := hE
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsMulCommutative ↥E := hcomm
    exact Subgroup.map_isMulCommutative (H := E) f
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hexp y hy, map_one]
  · have hc : Nat.card ↥(E.map f) = Nat.card ↥E :=
      (Nat.card_congr (Subgroup.equivMapOfInjective E f hf).toEquiv).symm
    rw [hc, hcard]

end CFSG.EvenSporadicStandard.HNRecog.Section3
