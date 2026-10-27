module

public import CFSG.CGT.M24R.L2SubB

public section

namespace CFSG.CGT.M24R

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

section FB

variable (hcard : Nat.card N8 = 322560)
include hcard

theorem card_T8_inf {K : Subgroup N8} {p : ℕ → Bool}
    (hp : ∀ k < 16, p k = true ↔ n8 (tw k) ∈ Subgroup.normalizer (K : Set N8)) :
    Nat.card ↥(T8 ⊓ Subgroup.normalizer (K : Set N8)) = (List.range 16).countP p := by
  rw [List.countP_eq_length_filter]
  set L := (List.range 16).filter p with hL
  have hnd : L.Nodup := List.nodup_range.sublist List.filter_sublist
  have hmem : ∀ k ∈ L, k < 16 ∧ p k = true := fun k hk =>
    ⟨List.mem_range.1 (List.mem_filter.1 hk).1, (List.mem_filter.1 hk).2⟩
  let F : Fin L.length → ↥(T8 ⊓ Subgroup.normalizer (K : Set N8)) := fun i =>
    ⟨n8 (tw L[i]), Subgroup.mem_inf.2 ⟨n8_tw_mem _,
      (hp _ (hmem _ (List.getElem_mem _)).1).1 (hmem _ (List.getElem_mem _)).2⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i j hij
      have h1 := tw_inj hcard (hmem _ (List.getElem_mem i.isLt)).1
        (hmem _ (List.getElem_mem j.isLt)).1 (congrArg Subtype.val hij)
      exact Fin.ext ((hnd.getElem_inj_iff).1 h1)
    · rintro ⟨x, hxT, hxN⟩
      obtain ⟨k, hk, rfl⟩ := (mem_T8_iff hcard x).1 hxT
      have hkL : k ∈ L := List.mem_filter.2 ⟨List.mem_range.2 hk, (hp k hk).2 hxN⟩
      obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hkL
      exact ⟨⟨i, hi⟩, Subtype.ext (by simp [F, hik])⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_fin]

theorem klein_eq8 (B' : Subgroup N8) (hb0 : bb0 ∈ B') (hexp : ∀ x ∈ B', x * x = 1)
    (hcardB : Nat.card B' = 4) (hbot : B' ⊓ T8 = ⊥)
    (hA : Nat.card ↥(T8 ⊓ Subgroup.normalizer (B' : Set N8)) = 4)
    (hcomm : ∀ a ∈ T8 ⊓ Subgroup.normalizer (B' : Set N8), ∀ x ∈ B', a * x = x * a)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : N8, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set N8)) : B' = B8 := by
  have hfin : Finite N8 := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨hsq0, -, -, hne0, -, -, -, -, -, -⟩ := bFacts hcard
  obtain ⟨c, hcB, hc1, hcb⟩ : ∃ c ∈ B', c ≠ 1 ∧ c ≠ bb0 := by
    by_contra hcon
    push Not at hcon
    have hsub : (B' : Set N8) ⊆ {1, bb0} := by
      intro y hy
      by_cases h1 : y = 1
      · simp [h1]
      · simp [hcon y hy h1]
    have h2 : (B' : Set N8).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ((Set.ncard_insert_le _ _).trans
        (by rw [Set.ncard_singleton]))
    have h3 : (B' : Set N8).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hcardB
    omega
  have hcc : c * c = 1 := hexp c hcB
  have hbcB : bb0 * c ∈ B' := B'.mul_mem hb0 hcB
  have hcomm_c : c * bb0 = bb0 * c := by
    have h1 : (c * bb0)⁻¹ = c * bb0 := inv_eq_of_mul_eq_one_right (hexp _ (B'.mul_mem hcB hb0))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hcc, inv_eq_of_mul_eq_one_right hsq0] at h1
    exact h1.symm
  have hbc1 : bb0 * c ≠ 1 := by
    intro h
    apply hcb
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hsq0]
  have hnT : ∀ y ∈ B', y ≠ 1 → y ∉ T8 := by
    intro y hy hy1 hyT
    have : y ∈ B' ⊓ T8 := ⟨hy, hyT⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hy1 this
  have hbc_ne_b : bb0 * c ≠ bb0 := fun h => hc1 (by simpa using h)
  have hbc_ne_c : bb0 * c ≠ c := fun h => hne0 (by simpa using h)
  have hB' : ∀ y ∈ B', y = 1 ∨ y = bb0 ∨ y = c ∨ y = bb0 * c := by
    intro y hy
    have hsub : ({1, bb0, c, bb0 * c} : Set N8) ⊆ (B' : Set N8) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact B'.one_mem
      · exact hb0
      · exact hcB
      · exact hbcB
    have h4 : ({1, bb0, c, bb0 * c} : Set N8).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hbc_ne_c.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hcb.symm, hbc_ne_b.symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hne0.symm, hc1.symm, hbc1.symm⟩
    have h5 : (B' : Set N8).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hcardB
    have := Set.eq_of_subset_of_ncard_le hsub (by omega)
    have hy' : y ∈ (B' : Set N8) := hy
    rw [← this] at hy'
    simpa using hy'
  obtain ⟨j, hj, rfl⟩ := el_surj hcard c
  have hcT' := isTab_tab (mem_codes.1 hj).1
  have hXs := tab_size j
  set X := (mkCtx ()).tab j with hXdef
  have hL1 : ∀ Y ∈ kList X, ∃ y ∈ B', IsTab Y y := by
    intro Y hY
    simp only [kList, List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl | rfl
    · exact ⟨1, B'.one_mem, IsTab.one⟩
    · exact ⟨bb0, hb0, isTab_b0T⟩
    · exact ⟨el j, hcB, hcT'⟩
    · exact ⟨bb0 * el j, hbcB, isTab_b0T.mul hcT'⟩
  have hL2 : ∀ y ∈ B', ∃ Y ∈ kList X, IsTab Y y := by
    intro y hy
    rcases hB' y hy with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [kList], IsTab.one⟩
    · exact ⟨_, by simp [kList], isTab_b0T⟩
    · exact ⟨_, by simp [kList], hcT'⟩
    · exact ⟨_, by simp [kList], isTab_b0T.mul hcT'⟩
  have hN : ∀ {Y : Table} {y : N8}, IsTab Y y →
      (normK (kList X) b0T X Y = true ↔ y ∈ Subgroup.normalizer (B' : Set N8)) :=
    fun hY => normK_iff hcard hL1 hL2 isTab_b0T hcT' hY hb0 hcB hB'
  have hpre : (mkCtx ()).kleinPre X = true := by
    simp only [Ctx8.kleinPre, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨⟨((hcT'.mul hcT').beq_iff hcard IsTab.one (compT_size _ _) idT_size).2 hcc,
      (hcT'.commT_iff hcard isTab_b0T).2 hcomm_c⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [Bool.eq_false_iff]
      intro h
      exact hnT _ hcB hc1 ((isTt_iff hcard hcT' hXs).1 h)
    · rw [Bool.eq_false_iff]
      intro h
      exact hnT _ hbcB hbc1 ((isTt_iff hcard (isTab_b0T.mul hcT') (compT_size _ _)).1 h)
    · rw [Bool.eq_false_iff]
      intro h
      exact hcb ((hcT'.beq_iff hcard isTab_b0T hXs (wTab_size _)).1 h)
  have hcheap : (mkCtx ()).kleinCheap X = true := by
    simp only [Ctx8.kleinCheap, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, Bool.not_eq_true']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← card_T8_inf hcard (fun k hk => hN (isTab_tt hk)), hA]
    · intro k hk
      by_cases hik : normK (kList X) b0T X (mkCtx ()).tt[k]! = true
      · right
        have hxA : n8 (tw k) ∈ T8 ⊓ Subgroup.normalizer (B' : Set N8) :=
          ⟨n8_tw_mem k, (hN (isTab_tt hk)).1 hik⟩
        exact ⟨((isTab_tt hk).commT_iff hcard isTab_b0T).2 (hcomm _ hxA _ hb0),
          ((isTab_tt hk).commT_iff hcard hcT').2 (hcomm _ hxA _ hcB)⟩
      · left
        simpa using hik
    · intro k hk
      by_cases hik : (commT (mkCtx ()).tt[k]! b0T || commT (mkCtx ()).tt[k]! X ||
          commT (mkCtx ()).tt[k]! (compT 16 b0T X)) = true
      · right
        simp only [Bool.or_eq_true] at hik
        refine (hN (isTab_tt hk)).2 ?_
        rcases hik with (h | h) | h
        · exact hcent _ hb0 hne0 _ (((isTab_tt hk).commT_iff hcard isTab_b0T).1 h)
        · exact hcent _ hcB hc1 _ (((isTab_tt hk).commT_iff hcard hcT').1 h)
        · exact hcent _ hbcB hbc1 _
            (((isTab_tt hk).commT_iff hcard (isTab_b0T.mul hcT')).1 h)
      · left
        simpa using hik
  have h := Certificates.certificate21193.2.2.2.2.2.2.1
  simp only [fbCheck, List.all_eq_true] at h
  have hk := h j hj
  rw [← hXdef, hpre, hcheap] at hk
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, List.any_eq_true] at hk
  rcases hk with hB | ⟨y, hy, hr⟩
  ·
    have hcB8 : el j ∈ B8 := (isBt_iff hcard hcT' hXs).1 hB
    have hle : B' ≤ B8 := by
      intro z hz
      rcases hB' z hz with rfl | rfl | rfl | rfl
      · exact B8.one_mem
      · exact Subgroup.subset_closure (by simp)
      · exact hcB8
      · exact B8.mul_mem (Subgroup.subset_closure (by simp)) hcB8
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_B8 hcard, hcardB])
  ·
    exfalso
    have hY := isTab_tab (mem_codes.1 hy).1
    simp only [refutes, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hr
    obtain ⟨hc', hn⟩ := hr
    have hyN : el y ∈ Subgroup.normalizer (B' : Set N8) := by
      rcases hc' with (h' | h') | h'
      · exact hcent _ hb0 hne0 _ ((hY.commT_iff hcard isTab_b0T).1 h')
      · exact hcent _ hcB hc1 _ ((hY.commT_iff hcard hcT').1 h')
      · exact hcent _ hbcB hbc1 _ ((hY.commT_iff hcard (isTab_b0T.mul hcT')).1 h')
    rw [← hN hY, hn] at hyN
    exact Bool.false_ne_true hyN

end FB

end CFSG.CGT.M24R
