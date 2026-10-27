module

public import Certificates.Certificate22260
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxThreeCent
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def EightLiftPermInput : Prop :=
  ∀ (u : Perm (Fin 9)) (v : Fin 4 → Perm (Fin 9)), u * u = 1 → 6 ≤ u.support.card →
    (∀ i, v i * u = u * v i) → (∀ i j, v i * v j = v j * v i) →
    (∀ i, v i * v i = u ∨ (v i * v i = 1 ∧ 5 ≤ (v i).support.card ∧
      5 ≤ (v i * u).support.card)) →
    (∀ i j, i ≠ j → v i * v j ≠ 1 ∧ v i * v j ≠ u) → False

namespace EightPerm

open SixGen ThreeCent

theorem eightPermCaseOK_spec {c : Swaps × List Swaps × Nat}
    (hcard : Nat.card (centralizer {permOf c.1}) = c.2.2) (h : eightPermCaseOK c = true)
    {w : Fin 4 → Perm (Fin 9)} (hwC : ∀ i, w i ∈ centralizer {permOf c.1})
    (hww : ∀ i j, w i * w j = w j * w i)
    (hgood : ∀ i, w i * w i = permOf c.1 ∨ (w i * w i = 1 ∧ 5 ≤ (w i).support.card ∧
      5 ≤ (w i * permOf c.1).support.card))
    (hne : ∀ i j, i ≠ j → w i * w j ≠ 1 ∧ w i * w j ≠ permOf c.1) : False := by
  classical
  simp only [eightPermCaseOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hcg, hok⟩, hsz⟩, hA⟩ := h
  have hEC := enumerates_of_list hok
  have hCle : closure {a | ∃ l ∈ c.2.1, a = permOf l} ≤ centralizer {permOf c.1} := by
    rw [closure_le]
    rintro a ⟨l, hl, rfl⟩
    rw [List.all_toArray, List.all_eq_true] at hcg
    have h1 := hcg (tabOf (permOf l)) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    exact mem_centralizer_singleton_iff.mpr (commute_of_commutes h1)
  have hCeq : closure {a | ∃ l ∈ c.2.1, a = permOf l} = centralizer {permOf c.1} := by
    refine Subgroup.eq_of_le_of_card_ge hCle ?_
    rw [hcard, hEC.card, Array.length_toList]
    rw [beq_iff_eq] at hsz
    rw [hsz]
  have hu : TabRep (tabOf (permOf c.1)) (permOf c.1) := tabRep_tabOf _
  have htab : ∀ i, ∃ t ∈ (enumBFS 9 (c.2.1.map fun l => tabOf (permOf l)).toArray
      c.2.2).tabs.toList, TabRep t (w i) := fun i => by
    have hi := hwC i
    rw [← hCeq] at hi
    exact hEC.complete _ hi
  choose t ht hrep using htab
  have hadm : ∀ i, t i ∈ (enumBFS 9 (c.2.1.map fun l => tabOf (permOf l)).toArray
      c.2.2).tabs.filter (eightAdmissible (tabOf (permOf c.1))) := fun i => by
    rw [Array.mem_filter]
    refine ⟨Array.mem_toList_iff.mp (ht i), ?_⟩
    have h2 : TabRep (comp 9 (t i) (t i)) (w i * w i) := (hrep i).comp (hrep i)
    simp only [eightAdmissible, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rcases hgood i with h1 | ⟨h1, h5, h5'⟩
    · exact Or.inl ((h2.beq_iff hu).mpr h1)
    · refine Or.inr ⟨⟨(h2.beq_iff TabRep.idTab).mpr h1, ?_⟩, ?_⟩
      · rwa [threeCentSupp_eq (hrep i)]
      · rwa [threeCentSupp_eq ((hrep i).comp hu)]
  have hlink : ∀ i j, i ≠ j → eightLinked (tabOf (permOf c.1)) (t i) (t j) = true :=
    fun i j hij => by
    have h2 : TabRep (comp 9 (t i) (t j)) (w i * w j) := (hrep i).comp (hrep j)
    simp only [eightLinked, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [commutes, beq_iff_eq]
      exact h2.tab_eq (by rw [hww i j]; exact (hrep j).comp (hrep i))
    · rw [Bool.eq_false_iff]
      exact fun h3 => (hne i j hij).1 ((h2.beq_iff TabRep.idTab).mp h3)
    · rw [Bool.eq_false_iff]
      exact fun h3 => (hne i j hij).2 ((h2.beq_iff hu).mp h3)
  rw [Array.all_eq_true'] at hA
  have h1 := hA _ (hadm 0)
  rw [Array.all_eq_true'] at h1
  have h2 := h1 _ (hadm 1)
  simp only [hlink 0 1 (by decide), Bool.not_true, Bool.false_or, Array.all_eq_true'] at h2
  have h3 := h2 _ (hadm 2)
  simp only [hlink 0 2 (by decide), hlink 1 2 (by decide), Bool.and_self, Bool.not_true,
    Bool.false_or, Array.all_eq_true'] at h3
  have h4 := h3 _ (hadm 3)
  simp [hlink 0 3 (by decide), hlink 1 3 (by decide), hlink 2 3 (by decide)] at h4

end EightPerm

open EightPerm SixGen

theorem eightLiftPermInput_of_check (hc : eightPermCheck = true) : EightLiftPermInput := by
  classical
  intro u v hu2 hu6 hvu hvv hgood hne
  rw [eightPermCheck, List.all_eq_true] at hc
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at hu6
    omega
  have huo : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := u) (by rw [huo]; exact Nat.prime_two)
  rw [huo] at hn
  have hsum : u.support.card = 2 * (n + 1) := by
    rw [← Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : u.support.card ≤ 9 := by
    have := Finset.card_le_univ u.support
    rwa [Fintype.card_fin] at this
  obtain ⟨c, hcmem, hct, hcard⟩ : ∃ c ∈ eightPermCases, (permOf c.1).cycleType = u.cycleType ∧
      Nat.card (centralizer {permOf c.1}) = c.2.2 := by
    have hn3 : n = 2 ∨ n = 3 := by omega
    rcases hn3 with rfl | rfl
    · have hct : (permOf eightPermCases[0].1).cycleType = Multiset.replicate 3 2 :=
        cycleType_of_mul_self (by decide) (by norm_num) (by decide)
      refine ⟨eightPermCases[0], by simp [eightPermCases], by rw [hct, hn], ?_⟩
      rw [Perm.nat_card_centralizer, hct]
      simp
      decide
    · have hct : (permOf eightPermCases[1].1).cycleType = Multiset.replicate 4 2 :=
        cycleType_of_mul_self (by decide) (by norm_num) (by decide)
      refine ⟨eightPermCases[1], by simp [eightPermCases], by rw [hct, hn], ?_⟩
      rw [Perm.nat_card_centralizer, hct]
      simp
      decide
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct.symm)
  have hmul : ∀ y z : Perm (Fin 9), π * y * π⁻¹ * (π * z * π⁻¹) = π * (y * z) * π⁻¹ :=
    fun y z => by group
  have hinj : ∀ y z : Perm (Fin 9), π * y * π⁻¹ = π * z * π⁻¹ → y = z := fun y z h => by
    have := congrArg (fun x => π⁻¹ * x * π) h
    simpa [mul_assoc] using this
  have hone : π * (1 : Perm (Fin 9)) * π⁻¹ = 1 := by group
  refine eightPermCaseOK_spec hcard (hc c hcmem) (w := fun i => π * v i * π⁻¹) (fun i => ?_)
    (fun i j => ?_) (fun i => ?_) (fun i j hij => ?_)
  · rw [mem_centralizer_singleton_iff, ← hπ, hmul, hmul, hvu i]
  · simp only [hmul, hvv i j]
  · simp only [← hπ, hmul, Perm.card_support_conj]
    rcases hgood i with h1 | ⟨h1, h5, h5'⟩
    · exact Or.inl (by rw [h1])
    · exact Or.inr ⟨by rw [h1, hone], h5, h5'⟩
  · simp only [← hπ, hmul]
    exact ⟨fun h1 => (hne i j hij).1 (hinj _ _ (h1.trans hone.symm)),
      fun h1 => (hne i j hij).2 (hinj _ _ h1)⟩

theorem eightLiftPermInput_holds : EightLiftPermInput :=
  eightLiftPermInput_of_check Certificates.certificate22260

end CFSG.ComponentClassification.SolMax
