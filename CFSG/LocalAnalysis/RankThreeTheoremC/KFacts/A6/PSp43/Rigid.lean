module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.TwoL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.Open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

@[expose] def IsEquivariant (π : Equiv.Perm (Fin 45)) : Prop :=
  ∀ j, π * tauPerm j * π⁻¹ = tauPerm (π j)

theorem isEquivariant_of_mem_P {g : Equiv.Perm (Fin 45)} (hg : g ∈ P) : IsEquivariant g :=
  conj_tauPerm hg

theorem IsEquivariant.mul {π σ : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π)
    (hσ : IsEquivariant σ) : IsEquivariant (π * σ) := by
  intro j
  calc π * σ * tauPerm j * (π * σ)⁻¹ = π * (σ * tauPerm j * σ⁻¹) * π⁻¹ := by group
    _ = tauPerm ((π * σ) j) := by rw [hσ j, hπ]; rfl

theorem IsEquivariant.inv {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) :
    IsEquivariant π⁻¹ := by
  intro j
  have h := hπ (π⁻¹ j)
  rw [show π (π⁻¹ j) = j by simp] at h
  rw [← h]
  group

theorem IsEquivariant.zpow {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) :
    ∀ n : ℤ, IsEquivariant (π ^ n) := by
  intro n
  induction n using Int.induction_on with
  | zero => simpa using isEquivariant_of_mem_P (one_mem P)
  | succ n ih => rw [zpow_add_one]; exact ih.mul hπ
  | pred n ih => rw [zpow_sub_one]; exact ih.mul hπ.inv

theorem IsEquivariant.comm_tau {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) {j : Fin 45}
    (hj : π j = j) : π * tauPerm j = tauPerm j * π := by
  have h := hπ j
  rw [hj] at h
  calc π * tauPerm j = π * tauPerm j * π⁻¹ * π := by group
    _ = tauPerm j * π := by rw [h]

theorem IsEquivariant.fix_tau {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) {j k : Fin 45}
    (hj : π j = j) (hk : π k = k) : π (tauPerm j k) = tauPerm j k := by
  have h := congrArg (fun σ : Equiv.Perm (Fin 45) => σ k) (hπ.comm_tau hj)
  simp only [Equiv.Perm.mul_apply, hk] at h
  exact h

@[expose] def closeStep (S : List ℕ) : List ℕ :=
  (List.range 45).filter fun l => S.contains l ||
    S.any fun j => S.any fun k => (tauTab.getD j []).getD k 0 == l

@[expose] def closeIter : ℕ → List ℕ → List ℕ
  | 0, S => S
  | n + 1, S => closeIter n (closeStep S)

theorem lt_of_mem_closeStep {S : List ℕ} {l : ℕ} (h : l ∈ closeStep S) : l < 45 := by
  simp only [closeStep, List.mem_filter, List.mem_range] at h
  exact h.1

theorem fix_of_closeStep {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) {S : List ℕ}
    (h45 : ∀ j ∈ S, j < 45) (hS : ∀ j (hj : j < 45), j ∈ S → π ⟨j, hj⟩ = ⟨j, hj⟩) :
    ∀ l (hl : l < 45), l ∈ closeStep S → π ⟨l, hl⟩ = ⟨l, hl⟩ := by
  intro l hl hmem
  simp only [closeStep, List.mem_filter, List.mem_range, Bool.or_eq_true, List.contains_iff_mem,
    List.any_eq_true, beq_iff_eq] at hmem
  obtain ⟨-, hmem | ⟨j, hjS, k, hkS, hjk⟩⟩ := hmem
  · exact hS l hl hmem
  · have hj := h45 j hjS
    have hk := h45 k hkS
    have e : tauPerm ⟨j, hj⟩ ⟨k, hk⟩ = ⟨l, hl⟩ := Fin.ext (by
      rw [(rep_tauPerm ⟨j, hj⟩).2 k hk]; exact hjk)
    have h := hπ.fix_tau (hS j hj hjS) (hS k hk hkS)
    rwa [e] at h

theorem fix_of_closeIter {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) :
    ∀ (n : ℕ) {S : List ℕ}, (∀ j ∈ S, j < 45) →
      (∀ j (hj : j < 45), j ∈ S → π ⟨j, hj⟩ = ⟨j, hj⟩) →
      ∀ l (hl : l < 45), l ∈ closeIter n S → π ⟨l, hl⟩ = ⟨l, hl⟩
  | 0, _, _, hS => hS
  | n + 1, S, h45, hS => fix_of_closeIter hπ n (fun _ h => lt_of_mem_closeStep h)
      (fix_of_closeStep hπ h45 hS)

theorem eq_one_of_closeIter {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) {n : ℕ}
    {S : List ℕ} (h45 : ∀ j ∈ S, j < 45) (hS : ∀ j (hj : j < 45), j ∈ S → π ⟨j, hj⟩ = ⟨j, hj⟩)
    (hall : (List.range 45).all (closeIter n S).contains = true) : π = 1 := by
  ext ⟨l, hl⟩
  have hm := List.all_eq_true.1 hall l (List.mem_range.2 hl)
  rw [List.contains_iff_mem] at hm
  rw [fix_of_closeIter hπ n h45 hS l hl hm]
  rfl

@[expose] def rigOK (elems : List Tab) (r : ℕ × List ℕ × List ℕ × ℕ × List (Fin 45)) : Bool :=
  decide (r.1 < 45) && decide (r.2.2.2.1 < 45) &&
  ((List.range 45).all fun j => r.2.1.contains j ==
    ((tauTab.getD r.1 []).getD j 0 == j && elems.all fun u => u == tid || u.getD j 0 != j)) &&
  (r.2.1.all fun b => r.2.1.all fun j => elems.any fun u => u.getD b 0 == j) &&
  (r.2.2.1.all fun c => (closeIter 1 (r.1 :: r.2.1)).contains c) &&
  (r.2.2.1.all fun c => decide (c < 45) && (tauTab.getD r.1 []).getD c 0 == c) &&
  (r.2.2.2.2.all fun l => r.2.2.1.contains l.1) &&
  ((wtab r.2.2.2.2).getD r.2.2.2.1 0 == r.2.2.2.1) && !r.2.2.1.contains r.2.2.2.1 &&
  ((List.range 45).all fun j => !((wtab r.2.2.2.2).getD j 0 == j) || r.2.2.1.contains j ||
    j == r.2.2.2.1 || j == (tauTab.getD r.1 []).getD r.2.2.2.1 0) &&
  (List.range 45).all
    (closeIter 2 (r.2.2.1 ++ elems.map fun u => u.getD r.2.2.2.1 0)).contains

theorem rig1_OK : rig1.all (rigOK U1elems) = true := by decide +kernel
theorem rig2_OK : rig2.all (rigOK U2elems) = true := by decide +kernel
theorem rig1_cov : rig1.map (·.1) = U1fix := by decide
theorem rig2_cov : rig2.map (·.1) = U2fix := by decide

theorem rig1_card : ∀ r ∈ rig1, Nat.card {j : Fin 45 // j.1 ∈ r.2.1} = 9 := by
  intro r hr
  simp only [rig1, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    (rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide)

theorem rig2_card : ∀ r ∈ rig2, Nat.card {j : Fin 45 // j.1 ∈ r.2.1} = 9 := by
  intro r hr
  simp only [rig2, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    (rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; decide)

theorem comm_of_gen {ws : List (List (Fin 45))} {π : Equiv.Perm (Fin 45)}
    (h : ∀ w ∈ ws, π * wperm w = wperm w * π) :
    ∀ u ∈ gen (ws.map wperm), π * u = u * π := by
  have hle : gen (ws.map wperm) ≤ centralizer ({π} : Set (Equiv.Perm (Fin 45))) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq, List.mem_map] at hg
    obtain ⟨w, hw, rfl⟩ := hg
    exact mem_centralizer_singleton_iff.2 (h w hw).symm
  intro u hu
  exact (mem_centralizer_singleton_iff.1 (hle hu)).symm

theorem mem_P_of_equivariant {ws : List (List (Fin 45))} {elems : List Tab}
    {par : List (ℕ × ℕ)} {act : List (List ℕ)} {fixl : List ℕ}
    {rig : List (ℕ × List ℕ × List ℕ × ℕ × List (Fin 45))}
    (henum : enumOK (ws.map wtab) elems par act = true) (hfix : fixOK ws fixl = true)
    (hfixc : Nat.card {j : Fin 45 // j.1 ∈ fixl} = 3) (hrig : rig.all (rigOK elems) = true)
    (hcov : rig.map (·.1) = fixl) (hcardO : ∀ r ∈ rig, Nat.card {j : Fin 45 // j.1 ∈ r.2.1} = 9)
    {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) (hcomm : ∀ w ∈ ws, π * wperm w = wperm w * π)
    (h2 : IsPGroup 2 (zpowers π)) : π ∈ P := by
  set U := gen (ws.map wperm)
  have hUc := comm_of_gen hcomm
  have hV : ∀ v ∈ zpowers π, IsEquivariant v ∧ ∀ u ∈ U, v * u = u * v := by
    intro v hv
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hv
    exact ⟨hπ.zpow n, fun u hu => ((Commute.zpow_left (hUc u hu) n).eq)⟩
  obtain ⟨i, hi, hπi⟩ := exists_fixed_of_invariant h2 (fun j : Fin 45 => j.1 ∈ fixl)
    (by
      intro v hv j hj
      rw [fix_iff hfix] at hj ⊢
      intro w hw
      have h1 := (hV v hv).2 _ (wperm_mem_gen hw)
      have h2 := congrArg (fun σ : Equiv.Perm (Fin 45) => σ j) h1
      simp only [Equiv.Perm.mul_apply, hj w hw] at h2
      exact h2.symm)
    (by rw [hfixc]; norm_num)
  obtain ⟨r, hr, hri⟩ : ∃ r ∈ rig, r.1 = i.1 := by
    rw [← hcov] at hi
    obtain ⟨r, hr, e⟩ := List.mem_map.1 hi
    exact ⟨r, hr, e⟩
  have hok := List.all_eq_true.1 hrig r hr
  simp only [rigOK, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hb45⟩, hO⟩, horb⟩, hCcl⟩, hCfix⟩, hsl⟩, hsb⟩, hbC⟩, hsfix⟩, hall⟩ := hok
  rw [decide_eq_true_eq] at hb45
  set O := r.2.1
  set C := r.2.2.1
  set b0 := r.2.2.2.1
  set s := r.2.2.2.2
  have htab_i : tauTab.getD r.1 [] = tauTab.getD i.1 [] := by rw [hri]
  have hmemU : ∀ u ∈ elems, ∃ g ∈ U, Rep g u := by
    intro u hu
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
    obtain ⟨g, hgU, hgr⟩ := exists_mem_rep_of_enumOK (length_words ws) (rep_words ws) henum k hk
    rw [List.getD_eq_getElem _ _ hk] at hgr
    exact ⟨g, hgU, hgr⟩
  have htau_i : ∀ j : Fin 45, (tauTab.getD r.1 []).getD j.1 0 = (tauPerm i j : ℕ) := by
    intro j
    rw [htab_i, (rep_tauPerm i).2 j.1 j.2]
  have hOchar : ∀ j : Fin 45, j.1 ∈ O ↔ (tauPerm i j = j ∧ ∀ g ∈ U, g ≠ 1 → g j ≠ j) := by
    intro j
    have h1 := List.all_eq_true.1 hO j.1 (List.mem_range.2 j.2)
    rw [beq_iff_eq] at h1
    rw [← List.contains_iff_mem, h1, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, htau_i]
    constructor
    · rintro ⟨hτ, hu⟩
      refine ⟨Fin.ext hτ, fun g hg hg1 hgj => ?_⟩
      obtain ⟨t, ht, hgr⟩ := exists_mem_tab henum hg
      have h2 := hu t ht
      rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h2
      rcases h2 with h2 | h2
      · exact hg1 (rep_unique (h2 ▸ hgr) rep_one)
      · exact h2 (by rw [← hgr.2 j.1 j.2]; exact congrArg Fin.val hgj)
    · rintro ⟨hτ, hu⟩
      refine ⟨congrArg Fin.val hτ, fun t ht => ?_⟩
      rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
      obtain ⟨g, hgU, hgr⟩ := hmemU t ht
      by_cases hg1 : g = 1
      · left
        subst hg1
        exact rep_eq_tab hgr rep_one
      · right
        intro h
        exact hu g hgU hg1 (Fin.ext (by rw [hgr.2 j.1 j.2]; exact h))
  obtain ⟨b, hbO, hπb⟩ := exists_fixed_of_invariant h2 (fun j : Fin 45 => j.1 ∈ O)
    (by
      intro v hv j hj
      obtain ⟨hve, hvU⟩ := hV v hv
      have hvi : v i = i := hπi v hv
      rw [hOchar] at hj ⊢
      obtain ⟨hτ, hu⟩ := hj
      refine ⟨?_, fun g hg hg1 hgj => ?_⟩
      · have h1 := congrArg (fun σ : Equiv.Perm (Fin 45) => σ j) (hve.comm_tau hvi)
        simp only [Equiv.Perm.mul_apply, hτ] at h1
        exact h1.symm
      · have h1 := congrArg (fun σ : Equiv.Perm (Fin 45) => σ j) (hvU g hg)
        simp only [Equiv.Perm.mul_apply] at h1
        exact hu g hg hg1 (v.injective (h1.trans hgj)))
    (by rw [hcardO r hr]; norm_num)
  have hπb' : π b = b := hπb π (mem_zpowers π)
  have hπi' : π i = i := hπi π (mem_zpowers π)
  have hfixO : ∀ j : Fin 45, j.1 ∈ O → π j = j := by
    intro j hj
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 horb b.1 hbO) j.1 hj
    obtain ⟨t, ht, htj⟩ := List.any_eq_true.1 h1
    rw [beq_iff_eq] at htj
    obtain ⟨g, hgU, hgr⟩ := hmemU t ht
    have hgb : g b = j := Fin.ext (by rw [hgr.2 b.1 b.2]; exact htj)
    rw [← hgb]
    have h2 := congrArg (fun σ : Equiv.Perm (Fin 45) => σ b) (hUc g hgU)
    simp only [Equiv.Perm.mul_apply, hπb'] at h2
    exact h2
  have hS1 : ∀ j (hj : j < 45), j ∈ r.1 :: O → π ⟨j, hj⟩ = ⟨j, hj⟩ := by
    intro j hj hm
    rcases List.mem_cons.1 hm with h | h
    · have : (⟨j, hj⟩ : Fin 45) = i := Fin.ext (h.trans hri)
      rw [this, hπi']
    · exact hfixO ⟨j, hj⟩ h
  have h45O : ∀ j ∈ r.1 :: O, j < 45 := by
    intro j hm
    rcases List.mem_cons.1 hm with h | h
    · rw [h, hri]; exact i.2
    · by_contra hj
      have h1 := List.all_eq_true.1 (List.all_eq_true.1 horb j h) j h
      obtain ⟨t, ht, htj⟩ := List.any_eq_true.1 h1
      rw [beq_iff_eq] at htj
      obtain ⟨g, -, hgr⟩ := hmemU t ht
      rw [List.getD_eq_default _ _ (by rw [hgr.1]; omega)] at htj
      exact hj (by rw [← htj]; norm_num)
  have hC45 : ∀ c ∈ C, c < 45 := fun c hc => by
    have h1 := List.all_eq_true.1 hCfix c hc
    rw [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1
  have hfixC : ∀ c (hc : c < 45), c ∈ C → π ⟨c, hc⟩ = ⟨c, hc⟩ := by
    intro c hc hm
    have h1 := List.all_eq_true.1 hCcl c hm
    rw [List.contains_iff_mem] at h1
    exact fix_of_closeIter hπ 1 h45O hS1 c hc h1
  have hτC : ∀ c (hc : c < 45), c ∈ C → tauPerm i ⟨c, hc⟩ = ⟨c, hc⟩ := by
    intro c hc hm
    have h1 := List.all_eq_true.1 hCfix c hm
    rw [Bool.and_eq_true, beq_iff_eq] at h1
    exact Fin.ext (by rw [← htau_i ⟨c, hc⟩]; exact h1.2)
  have hsC : ∀ l ∈ s, l.1 ∈ C := fun l hl => by
    have h1 := List.all_eq_true.1 hsl l hl
    rwa [List.contains_iff_mem] at h1
  have hπs : π * wperm s = wperm s * π := by
    have hle : ∀ w : List (Fin 45), (∀ l ∈ w, l.1 ∈ C) → π * wperm w = wperm w * π := by
      intro w
      induction w with
      | nil => intro _; simp [wperm]
      | cons l w ih =>
        intro hw
        have h1 := hπ.comm_tau (hfixC l.1 l.2 (hw l List.mem_cons_self))
        have h2 := ih fun l' hl' => hw l' (List.mem_cons_of_mem l hl')
        have e : wperm (l :: w) = tauPerm l * wperm w := by simp [wperm]
        rw [e, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]
    exact hle s hsC
  set b0' : Fin 45 := ⟨b0, hb45⟩
  have hsb0 : wperm s b0' = b0' := by
    rw [beq_iff_eq] at hsb
    exact Fin.ext (by rw [(rep_wperm s).2 b0 hb45]; exact hsb)
  have hspb : wperm s (π b0') = π b0' := by
    have h1 := congrArg (fun σ : Equiv.Perm (Fin 45) => σ b0') hπs
    simp only [Equiv.Perm.mul_apply, hsb0] at h1
    exact h1.symm
  have hcase : π b0' = b0' ∨ π b0' = tauPerm i b0' := by
    have h1 := List.all_eq_true.1 hsfix (π b0').1 (List.mem_range.2 (π b0').2)
    have e1 : (wtab s).getD (π b0').1 0 = (π b0').1 := by
      rw [← (rep_wperm s).2 _ (π b0').2]
      exact congrArg Fin.val hspb
    rw [e1, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.or_eq_true,
      beq_iff_eq, beq_iff_eq, List.contains_iff_mem] at h1
    rcases h1 with (h1 | h1) | h1
    · exfalso
      have h2 : π (π b0') = π b0' := by
        have := hfixC _ (π b0').2 h1
        simpa using this
      have h3 : π b0' = b0' := π.injective h2
      have hb0C : b0 ∈ C := by
        have e := congrArg Fin.val h3
        rw [e] at h1
        exact h1
      rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at hbC
      exact hbC hb0C
    · exact Or.inl (Fin.ext h1)
    · right
      apply Fin.ext
      rw [h1, ← htau_i b0']
  have hUb : ∀ σ : Equiv.Perm (Fin 45), IsEquivariant σ → (∀ u ∈ U, σ * u = u * σ) →
      (∀ c (hc : c < 45), c ∈ C → σ ⟨c, hc⟩ = ⟨c, hc⟩) → σ b0' = b0' → σ = 1 := by
    intro σ hσ hσU hσC hσb
    refine eq_one_of_closeIter hσ (n := 2) ?_ ?_ (by
      have := hall
      exact this)
    · intro j hj
      rcases List.mem_append.1 hj with h | h
      · exact hC45 j h
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
        obtain ⟨g, -, hgr⟩ := hmemU t ht
        rw [← hgr.2 b0 hb45]
        exact (g b0').2
    · intro j hj hm
      rcases List.mem_append.1 hm with h | h
      · exact hσC j hj h
      · obtain ⟨t, ht, htj⟩ := List.mem_map.1 h
        obtain ⟨g, hgU, hgr⟩ := hmemU t ht
        have hgb : g b0' = ⟨j, hj⟩ := Fin.ext ((hgr.2 b0 hb45).trans htj)
        rw [← hgb]
        have h2 := congrArg (fun σ' : Equiv.Perm (Fin 45) => σ' b0') (hσU g hgU)
        simp only [Equiv.Perm.mul_apply, hσb] at h2
        exact h2
  have hiU : ∀ u ∈ U, tauPerm i * u = u * tauPerm i := by
    intro u hu
    have hui : u i = i := fix_of_mem_gen hfix (by rw [← hri]; exact (hri ▸ hi :)) hu
    have h1 := conj_tauPerm (gen_words_le_P ws hu) i
    rw [hui] at h1
    calc tauPerm i * u = u * tauPerm i * u⁻¹ * u := by rw [h1]
      _ = u * tauPerm i := by group
  rcases hcase with h | h
  · rw [hUb π hπ hUc hfixC h]
    exact one_mem P
  · have hτ2 : tauPerm i * tauPerm i = 1 := tauPerm_mul_self i
    have h1 := hUb (tauPerm i * π) ((isEquivariant_of_mem_P (tauPerm_mem i)).mul hπ)
      (fun u hu => by rw [mul_assoc, hUc u hu, ← mul_assoc, hiU u hu, mul_assoc])
      (fun c hc hm => by rw [Equiv.Perm.mul_apply, hfixC c hc hm, hτC c hc hm])
      (by rw [Equiv.Perm.mul_apply, h, ← Equiv.Perm.mul_apply, hτ2, Equiv.Perm.one_apply])
    have : π = tauPerm i := by
      calc π = tauPerm i * (tauPerm i * π) := by rw [← mul_assoc, hτ2, one_mul]
        _ = tauPerm i := by rw [h1, mul_one]
    rw [this]
    exact tauPerm_mem i

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43
