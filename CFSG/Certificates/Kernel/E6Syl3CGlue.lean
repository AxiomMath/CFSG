module

public import CFSG.Certificates.Kernel.E6Syl3CSound

public section

namespace CFSG.KC.E6Syl3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3 CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Steinberg.Adjoint


theorem three_dvd_root (k : ℕ) : (3 : ℤ) ∣ e6Certificate.root k 3 ↔ n3 k % 3 = 0 :=
  three_dvd_iff rfl

theorem a2div_of {α β : Fin Tag.E6.rank → ℤ} (ha : (3 : ℤ) ∣ α 3) (hb : (3 : ℤ) ∣ β 3)
    (hd : (3 : ℤ) ∣ (α + β) 3) : ∀ γ ∈ a2Roots α β, (3 : ℤ) ∣ γ 3 := by
  intro γ hγ
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [Pi.neg_apply] <;> omega

theorem a2none_of {α β : Fin Tag.E6.rank → ℤ} (ha : ¬ (3 : ℤ) ∣ α 3) (hb : ¬ (3 : ℤ) ∣ β 3)
    (hd : ¬ (3 : ℤ) ∣ (α + β) 3) : ∀ γ ∈ a2Roots α β, ¬ (3 : ℤ) ∣ γ 3 := by
  intro γ hγ
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [Pi.neg_apply] <;> omega

theorem sum_of_k2B {t : List ℕ} {a b d m : ℕ} (h : k2B t a b d m = true) :
    a < 72 ∧ b < 72 ∧ d < 72 ∧
      e6Certificate.root d = e6Certificate.root a + e6Certificate.root b := by
  simp only [k2B, Bool.and_eq_true] at h
  exact sumB_sound h.1.1.1.1.1.1

theorem div_of_divB {a b d : ℕ} (hs : e6Certificate.root d = e6Certificate.root a +
    e6Certificate.root b) (h : divB a b d = true) :
    ∀ γ ∈ a2Roots (e6Certificate.root a) (e6Certificate.root b), (3 : ℤ) ∣ γ 3 := by
  simp only [divB, Bool.and_eq_true, beq_iff_eq] at h
  refine a2div_of ((three_dvd_root a).2 h.1.1) ((three_dvd_root b).2 h.1.2) ?_
  rw [← hs]
  exact (three_dvd_root d).2 h.2

theorem none_of_noneB {a b d : ℕ} (hs : e6Certificate.root d = e6Certificate.root a +
    e6Certificate.root b) (h : noneB a b d = true) :
    ∀ γ ∈ a2Roots (e6Certificate.root a) (e6Certificate.root b), ¬ (3 : ℤ) ∣ γ 3 := by
  simp only [noneB, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  refine a2none_of (fun e => h.1.1 ((three_dvd_root a).1 e))
    (fun e => h.1.2 ((three_dvd_root b).1 e)) ?_
  rw [← hs]
  exact fun e => h.2 ((three_dvd_root d).1 e)

theorem caseI_of_witness {t c : List ℕ} {w : WeylGroup Tag.E6}
    (hrep : e6Certificate.Represents t w) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hk : kindOK t c = true) (hc : caseIEl t c = true) :
    E6KindA2 w ∨ E6Kind3A2 w ∨
    (∃ γ₁ γ₂, E6Kind2A2 w γ₁ γ₂ ∧ ∀ γ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ γ 3) ∨
    (∃ γ₁ γ₂, E6Kind2A2 w γ₁ γ₂ ∧ (∀ γ ∈ a2Roots γ₁ γ₂, ¬ (3 : ℤ) ∣ γ 3) ∧
      E6TauChars w γ₁) := by
  unfold kindOK at hk
  split at hk
  · exact (notOrd3_sound hrep hw3 hw1 hk).elim
  · exact Or.inr (Or.inl (k3B_sound hrep hk))
  · exact Or.inl (kA2B_sound hrep hk)
  · rename_i a b d m
    have h2 := k2B_sound hrep hk
    obtain ⟨ha, -, -, hs⟩ := sum_of_k2B hk
    simp only [caseIEl, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hd | ⟨hn, ht⟩
    · exact Or.inr (Or.inr (Or.inl ⟨_, _, h2, div_of_divB hs hd⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨_, _, h2, none_of_noneB hs hn, tauB_sound hrep ha ht⟩))
  · exact absurd hk (by simp)

theorem caseIEl_getD {Q W : List (List ℕ)} (h : caseIElems Q W = true) {x : ℕ}
    (hx : x < Q.length) : caseIEl (Q.getD x []) (W.getD x []) = true := by
  simp only [caseIElems, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  have hxW : x < W.length := h.1 ▸ hx
  rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hxW]
  refine h.2 (Q[x], W[x]) ?_
  rw [List.mem_iff_getElem]
  exact ⟨x, by rw [List.length_zip, ← h.1, Nat.min_self]; exact hx, by rw [List.getElem_zip]⟩

theorem is2Div_sound {gw wd lt : List (List ℕ)} (hF : QFacts gw wd lt) {kw : List (List ℕ)}
    (hk : kindsCheck (qTups gw) kw = true) {x : ℕ} (hx : x < 81) (h : is2Div kw x = true) :
    ∃ γ₁ γ₂, E6Kind2A2 (yI gw wd x) γ₁ γ₂ ∧ ∀ δ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ δ 3 := by
  have hc := kindOK_getD hk (x := x) (by rw [hF.len]; exact hx)
  unfold is2Div at h
  split at h
  · rename_i a b d m e
    rw [e] at hc
    obtain ⟨-, -, -, hs⟩ := sum_of_k2B hc
    exact ⟨_, _, k2B_sound (rep_yI hF hx) hc, div_of_divB hs h⟩
  · exact absurd h (by simp)

theorem pairC_of_check {gw wd lt : List (List ℕ)} (hF : QFacts gw wd lt) {kw cw : List (List ℕ)}
    {o3 : List ℕ} (hk : kindsCheck (qTups gw) kw = true) (ho : o3OK lt wd o3 = true)
    (hp : caseIPairs (qTups gw) kw lt wd o3 cw = true) {i j : ℕ} (hi : i ∈ o3) (hj : j ∈ o3)
    (hc : Commute (yI gw wd i) (yI gw wd j)) (hji : j ≠ i) (hj2 : j ≠ powI lt wd i 2) :
    (∃ a b : ℕ, E6Kind3A2 (yI gw wd i ^ a * yI gw wd j ^ b)) ∨
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ (3 : ℤ) ∣ γ 3 ∧ yI gw wd i • γ = γ ∧
      yI gw wd j • γ = γ ∧ ∃ a b c d : ℕ, ¬ (3 : ℤ) ∣ ((a * d : ℕ) : ℤ) - ((b * c : ℕ) : ℤ) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (yI gw wd i ^ a * yI gw wd j ^ b) γ₁ γ₂ ∧
          ∀ δ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ δ 3) ∧
        (∃ γ₁ γ₂, E6Kind2A2 (yI gw wd i ^ c * yI gw wd j ^ d) γ₁ γ₂ ∧
          ∀ δ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ δ 3) := by
  have hi81 := lt_of_mem_o3 ho hi
  have hj81 := lt_of_mem_o3 ho hj
  have hA : commI lt wd i j = true := by
    obtain ⟨h1, h2⟩ := mulI_spec hF hi81 hj81
    obtain ⟨h3, h4⟩ := mulI_spec hF hj81 hi81
    simp only [commI, beq_iff_eq]
    exact yI_inj hF h1 h3 (by rw [h2, h4, hc.eq])
  have hB : (j != i) = true := by simpa using hji
  have hC : (j != powI lt wd i 2) = true := by simpa using hj2
  simp only [caseIPairs, List.all_eq_true] at hp
  have h := hp i hi j hj
  simp only [hA, hB, hC, Bool.true_and, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    List.any_eq_true] at h
  rcases h with h | ⟨e, -, he⟩
  · left
    simp only [has3, List.any_eq_true, List.mem_range] at h
    obtain ⟨a, -, b, -, hab⟩ := h
    obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 a b
    exact ⟨a, b, hy ▸ is3A2_sound hF hk hx hab⟩
  · right
    unfold badC at he
    split at he
    · rename_i i' j' r a b c d
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at he
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hr⟩, hr3⟩, hfi⟩, hfj⟩, hdet⟩, h2a⟩, h2b⟩ := he
      rw [actV_rvL (rep_yI hF hi81), rvL_eq] at hfi
      rw [actV_rvL (rep_yI hF hj81), rvL_eq] at hfj
      refine ⟨_, isRoot_root72 hr, (three_dvd_root r).2 hr3, ofFn_inj' hfi, ofFn_inj' hfj,
        a, b, c, d, ?_, ?_, ?_⟩
      · generalize a * d = X at hdet ⊢
        generalize b * c = Y at hdet ⊢
        omega
      · obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 a b
        exact hy ▸ is2Div_sound hF hk hx h2a
      · obtain ⟨hx, hy⟩ := gEl_spec hF hi81 hj81 c d
        exact hy ▸ is2Div_sound hF hk hx h2b
    · exact absurd he (by simp)

theorem e6CaseITable_of_checks {gw wd lt kw cw : List (List ℕ)} {o3 : List ℕ}
    (hq : qCheckWith gw (qTups gw) = true) (hwd : wdOK gw (qTups gw) wd = true)
    (hlt : ltOK gw (qTups gw) lt = true) (hk : kindsCheck (qTups gw) kw = true)
    (ho : o3OK lt wd o3 = true) (hg : genN3 gw = true)
    (hce : caseIElems (qTups gw) kw = true) (hcp : caseIPairs (qTups gw) kw lt wd o3 cw = true) :
    E6CaseITable := by
  have hF := qFacts_of_checks hq hwd hlt
  have hcard := (exists_subgroup_of_qCheck hq).1
  have hQN := qSub_le_nodeSub hF.letters hg
  refine ⟨fun w h3 h1 hN => ?_, fun w₁ w₂ h13 h11 h23 hc12 hn hN1 hN2 => ?_⟩
  · obtain ⟨g, hgN, hgx⟩ := exists_conj_yIN hF hcard hQN (s := {w})
      (Set.singleton_subset_iff.2 (mem_nodeSub.2 hN)) (by simp) (by simpa using h3)
    obtain ⟨x, hx, hw⟩ := hgx w rfl
    have hy3 : yI gw wd x ^ 3 = 1 := (MulAut.conj g).injective (by rw [map_pow, hw, h3, map_one])
    have hy1 : yI gw wd x ≠ 1 := fun e => h1 (by rw [← hw, e, map_one])
    have hkx := kindOK_getD hk (x := x) (by rw [hF.len]; exact hx)
    have hcx := caseIEl_getD hce (x := x) (by rw [hF.len]; exact hx)
    rcases caseI_of_witness (rep_yI hF hx) hy3 hy1 hkx hcx with
      hA | h3A | ⟨γ₁, γ₂, h2, hd⟩ | ⟨γ₁, γ₂, h2, hd, ht⟩
    · have e := kindA2_conj hA g
      rw [← MulAut.conj_apply, hw] at e
      exact Or.inl e
    · have e := kind3_conj h3A g
      rw [← MulAut.conj_apply, hw] at e
      exact Or.inr (Or.inl e)
    · have e := kind2_conj h2 g
      rw [← MulAut.conj_apply, hw] at e
      exact Or.inr (Or.inr (Or.inl ⟨_, _, e, div_conj hgN h2.1 hd⟩))
    · have e := kind2_conj h2 g
      have et := tauChars_conj hgN ht
      rw [← MulAut.conj_apply, hw] at e et
      exact Or.inr (Or.inr (Or.inr ⟨_, _, e, none_conj hgN h2.1 hd, et⟩))
  · have h21 : w₂ ≠ 1 := fun h => hn (h ▸ Subgroup.one_mem _)
    have pair_s : ∀ a ∈ ({w₁, w₂} : Set (WeylGroup Tag.E6)),
        ∀ b ∈ ({w₁, w₂} : Set (WeylGroup Tag.E6)), Commute a b := by
      intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      exacts [Commute.refl _, hc12, hc12.symm, Commute.refl _]
    have pair_3 : ∀ a ∈ ({w₁, w₂} : Set (WeylGroup Tag.E6)), a ^ 3 = 1 := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      exacts [h13, h23]
    have pair_N : ({w₁, w₂} : Set (WeylGroup Tag.E6)) ⊆ nodeSub := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      exacts [mem_nodeSub.2 hN1, mem_nodeSub.2 hN2]
    obtain ⟨g, hgN, hgx⟩ := exists_conj_yIN hF hcard hQN pair_N pair_s pair_3
    obtain ⟨i, hi, hw1⟩ := hgx w₁ (by simp)
    obtain ⟨j, hj, hw2⟩ := hgx w₂ (by simp)
    obtain ⟨hji, hj2⟩ := ne_of_not_mem_zpowers hF hi hw1 hw2 hn
    have key := pairC_of_check hF hk ho hcp (mem_o3_conj hF ho hi hw1 h13 h11)
      (mem_o3_conj hF ho hj hw2 h23 h21) (commute_conj hw1 hw2 hc12) hji hj2
    have prod_eq : ∀ a b : ℕ,
        MulAut.conj g (yI gw wd i ^ a * yI gw wd j ^ b) = w₁ ^ a * w₂ ^ b :=
      fun a b => by rw [map_mul, map_pow, map_pow, hw1, hw2]
    rcases key with ⟨a, b, h⟩ | ⟨γ, hγ, hγ3, f1, f2, a, b, c, d, hdet, ⟨γ₁, γ₂, h2a, hda⟩,
        ⟨δ₁, δ₂, h2b, hdb⟩⟩
    · left
      refine ⟨a, b, ?_⟩
      have e := kind3_conj h g
      rwa [← MulAut.conj_apply, prod_eq] at e
    · right
      refine ⟨g • γ, IsRoot.smul hγ g, (three_dvd_smul hgN hγ).2 hγ3, ?_, ?_, a, b, c, d, hdet,
        ?_, ?_⟩
      · rw [← hw1, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul, f1]
      · rw [← hw2, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul, f2]
      · have e := kind2_conj h2a g
        rw [← MulAut.conj_apply, prod_eq] at e
        exact ⟨_, _, e, div_conj hgN h2a.1 hda⟩
      · have e := kind2_conj h2b g
        rw [← MulAut.conj_apply, prod_eq] at e
        exact ⟨_, _, e, div_conj hgN h2b.1 hdb⟩

end CFSG.KC.E6Syl3
