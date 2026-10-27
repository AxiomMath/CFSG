module

public import CFSG.CGT.A8S.L2Sub

public section

namespace CFSG.CGT.A8S.L2

open CFSG.CosetTable CFSG.CGT.A8S.N0

@[expose] def fbPre (c : ℕ) : Bool :=
  Nat.beq (cmul c c) 2184 && Nat.beq (cmul c 2698) (cmul 2698 c) && !isTc c &&
    !isTc (cmul 2698 c) && !Nat.beq c 2698

@[expose] def normBy (y c : ℕ) : Bool :=
  [2184, 2698, c, cmul 2698 c].any (fun s => Nat.beq (cmul y 2698) (cmul s y)) &&
    [2184, 2698, c, cmul 2698 c].any (fun s => Nat.beq (cmul y c) (cmul s y))

@[expose] def fbRef (c y : ℕ) : Bool :=
  (Nat.beq (cmul y 2698) (cmul 2698 y) || Nat.beq (cmul y c) (cmul c y) ||
    Nat.beq (cmul y (cmul 2698 c)) (cmul (cmul 2698 c) y)) && !normBy y c

@[expose] def fbRefs : List ℕ := [2128, 2764]

theorem fb_check :
    allCodes.all (fun c => !fbPre c || b0Codes.contains c || fbRefs.any (fbRef c)) = true := by
  decide +kernel

theorem fbRefs_valid : ∀ y ∈ fbRefs, validC y = true := by decide +kernel

theorem commute_of_cmul {x y : PG 5 relsN0A8}
    (h : Nat.beq (cmul (avc x) (avc y)) (cmul (avc y) (avc x)) = true) : x * y = y * x :=
  mul_eq_mul_of_cmul (Nat.eq_of_beq_eq_true h)

theorem any_of_conj_mem {K : Subgroup (PG 5 relsN0A8)}
    {S : List ℕ} (hS : ∀ z ∈ K, avc z ∈ S) {y b : PG 5 relsN0A8} (h : y * b * y⁻¹ ∈ K) :
    S.any (fun s => Nat.beq (cmul (avc y) (avc b)) (cmul s (avc y))) = true := by
  rw [List.any_eq_true]
  refine ⟨_, hS _ h, ?_⟩
  rw [Nat.beq_eq, ← avc_mul, ← avc_mul, inv_mul_cancel_right]

theorem klein_eqA8 (B' : Subgroup (PG 5 relsN0A8))
    (hb0 : b0 ∈ B') (hexp : ∀ x ∈ B', x * x = 1) (hcardB : Nat.card B' = 4)
    (hbot : B' ⊓ T0 = ⊥)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : PG 5 relsN0A8, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set (PG 5 relsN0A8))) : B' = B0 := by
  have hfin := finite_pg_relsN0A8
  have hsq0 : b0 * b0 = 1 := hexp _ hb0
  have hne0 : b0 ≠ 1 := fun h => by
    have := avc_b0
    rw [h, avc_one] at this
    exact absurd this (by decide)
  obtain ⟨c, hcB, hc1, hcb⟩ : ∃ c ∈ B', c ≠ 1 ∧ c ≠ b0 := by
    by_contra hcon
    push Not at hcon
    have hsub : (B' : Set (PG 5 relsN0A8)) ⊆ {1, b0} := by
      intro y hy
      by_cases h1 : y = 1
      · simp [h1]
      · simp [hcon y hy h1]
    have h2 : (B' : Set (PG 5 relsN0A8)).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
        (by rw [Set.ncard_singleton]))
    have h3 : (B' : Set (PG 5 relsN0A8)).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hcardB
    omega
  have hcc : c * c = 1 := hexp c hcB
  have hbcB : b0 * c ∈ B' := B'.mul_mem hb0 hcB
  have hcomm_c : c * b0 = b0 * c := by
    have h1 : (c * b0)⁻¹ = c * b0 := inv_eq_of_mul_eq_one_right (hexp _ (B'.mul_mem hcB hb0))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hcc, inv_eq_of_mul_eq_one_right hsq0] at h1
    exact h1.symm
  have hbc1 : b0 * c ≠ 1 := by
    intro h
    apply hcb
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hsq0]
  have hnT : ∀ y ∈ B', y ≠ 1 → y ∉ T0 := by
    intro y hy hy1 hyT
    have : y ∈ B' ⊓ T0 := ⟨hy, hyT⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hy1 this
  have hbc_ne_b : b0 * c ≠ b0 := fun h => hc1 (by simpa using h)
  have hbc_ne_c : b0 * c ≠ c := fun h => hne0 (by simpa using h)
  have hB' : ∀ y ∈ B', y = 1 ∨ y = b0 ∨ y = c ∨ y = b0 * c := by
    intro y hy
    have hsub : ({1, b0, c, b0 * c} : Set (PG 5 relsN0A8)) ⊆ (B' : Set (PG 5 relsN0A8)) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact B'.one_mem
      · exact hb0
      · exact hcB
      · exact hbcB
    have h4 : ({1, b0, c, b0 * c} : Set (PG 5 relsN0A8)).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hbc_ne_c.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hcb.symm, hbc_ne_b.symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hne0.symm, hc1.symm, hbc1.symm⟩
    have h5 : (B' : Set (PG 5 relsN0A8)).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hcardB
    have := Set.eq_of_subset_of_ncard_le hsub (by omega)
    have hy' : y ∈ (B' : Set (PG 5 relsN0A8)) := hy
    rw [← this] at hy'
    simpa using hy'
  have hS : ∀ z ∈ B', avc z ∈ [2184, 2698, avc c, cmul 2698 (avc c)] := by
    intro z hz
    rcases hB' z hz with rfl | rfl | rfl | rfl
    · rw [avc_one]; simp
    · rw [avc_b0]; simp
    · simp
    · rw [avc_mul, avc_b0]; simp
  have hpre : fbPre (avc c) = true := by
    simp only [fbPre, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true']
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [← avc_mul, hcc, avc_one]
    · rw [← avc_b0, ← avc_mul, ← avc_mul, hcomm_c]
    · rw [Bool.eq_false_iff]
      intro h
      exact hnT c hcB hc1 ((mem_T0_iff c).2 h)
    · rw [Bool.eq_false_iff]
      intro h
      rw [← avc_b0, ← avc_mul] at h
      exact hnT _ hbcB hbc1 ((mem_T0_iff _).2 h)
    · rw [Bool.eq_false_iff]
      intro h
      rw [Nat.beq_eq, ← avc_b0] at h
      exact hcb (avc_inj h)
  have hk := List.all_eq_true.1 fb_check (avc c) (avc_mem_allCodes c)
  rw [hpre] at hk
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true] at hk
  rcases hk with hB | ⟨yc, hy, hr⟩
  ·
    have hcB0 : c ∈ B0 := (mem_B0_iff c).2 (by simpa using hB)
    have hb0B0 : b0 ∈ B0 := Subgroup.subset_closure (by simp)
    have hle : B' ≤ B0 := by
      intro z hz
      rcases hB' z hz with rfl | rfl | rfl | rfl
      · exact B0.one_mem
      · exact hb0B0
      · exact hcB0
      · exact B0.mul_mem hb0B0 hcB0
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardB]; exact card_B0_le)
  ·
    exfalso
    obtain ⟨y, rfl⟩ := exists_avc_eq_of_validC (fbRefs_valid _ hy)
    simp only [fbRef, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hr
    obtain ⟨hc', hn⟩ := hr
    have hyN : y ∈ Subgroup.normalizer (B' : Set (PG 5 relsN0A8)) := by
      rcases hc' with (h' | h') | h'
      · rw [← avc_b0] at h'
        exact hcent _ hb0 hne0 _ (commute_of_cmul h')
      · exact hcent _ hcB hc1 _ (commute_of_cmul h')
      · rw [← avc_b0, ← avc_mul] at h'
        exact hcent _ hbcB hbc1 _ (commute_of_cmul h')
    have h1 := any_of_conj_mem hS ((Subgroup.mem_normalizer_iff.1 hyN b0).1 hb0)
    have h2 := any_of_conj_mem hS ((Subgroup.mem_normalizer_iff.1 hyN c).1 hcB)
    rw [avc_b0] at h1
    have : normBy (avc y) (avc c) = true := by
      simp only [normBy, Bool.and_eq_true]
      exact ⟨h1, h2⟩
    rw [this] at hn
    exact Bool.false_ne_true hn.symm

end CFSG.CGT.A8S.L2
