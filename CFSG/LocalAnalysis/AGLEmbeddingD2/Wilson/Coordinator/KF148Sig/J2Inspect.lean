module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2Core

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2

open Subgroup CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
  CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2 CFSG.GH74.GLS
  CFSG.RankThree.Asc83Table

set_option linter.unusedSectionVars false


theorem zJ_comm_xJ : Commute zJ xJ := by rw [z_eq]; exact z_comm_x

theorem Ej_zero : Ej 0 = closure ({zJ, xJ} : Set GJ) := by
  rw [Ej, E9Basis.sub, z_eq]
  rfl

theorem pow_mul_pow_mul_pow_mul_pow {i j k l : ℕ} :
    zJ ^ i * xJ ^ j * (zJ ^ k * xJ ^ l) = zJ ^ ((i + k) % 3) * xJ ^ ((j + l) % 3) := by
  have hc : Commute (xJ ^ j) (zJ ^ k) := (zJ_comm_xJ.symm.pow_left j).pow_right k
  rw [← pow_eq_pow_mod _ z_cube, ← pow_eq_pow_mod _ x_cube, pow_add, pow_add, mul_assoc,
    ← mul_assoc (xJ ^ j), hc.eq, mul_assoc, mul_assoc]

theorem mem_E0 {g : GJ} (hg : g ∈ Ej 0) : ∃ i < 3, ∃ j < 3, g = zJ ^ i * xJ ^ j := by
  rw [Ej_zero] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨1, by norm_num, 0, by norm_num, by simp⟩
    · exact ⟨0, by norm_num, 1, by norm_num, by simp⟩
  | one => exact ⟨0, by norm_num, 0, by norm_num, by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨i, -, j, -, rfl⟩ := iha
    obtain ⟨k, -, l, -, rfl⟩ := ihb
    exact ⟨_, Nat.mod_lt _ (by norm_num), _, Nat.mod_lt _ (by norm_num),
      pow_mul_pow_mul_pow_mul_pow⟩
  | inv a _ iha =>
    obtain ⟨i, -, j, -, rfl⟩ := iha
    have h3 : (zJ ^ i * xJ ^ j) ^ 3 = 1 := by
      rw [(zJ_comm_xJ.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j,
        pow_mul, pow_mul, z_cube, x_cube, one_pow, one_pow, one_mul]
    have hinv : (zJ ^ i * xJ ^ j)⁻¹ = (zJ ^ i * xJ ^ j) * (zJ ^ i * xJ ^ j) := by
      rw [inv_eq_of_mul_eq_one_right]
      rw [← pow_three]
      exact h3
    rw [hinv, pow_mul_pow_mul_pow_mul_pow]
    exact ⟨_, Nat.mod_lt _ (by norm_num), _, Nat.mod_lt _ (by norm_num), rfl⟩

theorem centralizer_sq_eq {G : Type*} [Group G] {w : G} (h : w ^ 3 = 1) :
    centralizer ({w ^ 2} : Set G) = centralizer ({w} : Set G) := by
  ext g
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hc : Commute g (w ^ 2) := hg
    have h4 : (w ^ 2) ^ 2 = w := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, h, one_mul]
    have := hc.pow_right 2
    rw [h4] at this
    exact this
  · intro hg
    exact (Commute.pow_right (hg : Commute g w) 2 : Commute g (w ^ 2))

theorem wJ_cube (k : ℕ) : wJ k ^ 3 = 1 := by
  rw [wJ, ((zJ_comm_xJ.pow_left k)).mul_pow, ← pow_mul, mul_comm k, pow_mul, z_cube, one_pow,
    x_cube, one_mul]

theorem wJ_sq (k : ℕ) : wJ k ^ 2 = zJ ^ ((2 * k) % 3) * xJ ^ 2 := by
  rw [wJ, ((zJ_comm_xJ.pow_left k)).mul_pow, ← pow_mul, mul_comm k, ← pow_eq_pow_mod _ z_cube]

theorem centralizer_of_mem_E0 {g : GJ} (hg : g ∈ Ej 0) (hg1 : g ≠ 1) :
    centralizer ({g} : Set GJ) = centralizer ({zJ} : Set GJ) ∨
      ∃ k < 3, centralizer ({g} : Set GJ) = centralizer ({wJ k} : Set GJ) := by
  obtain ⟨i, hi, j, hj, rfl⟩ := mem_E0 hg
  interval_cases i <;> interval_cases j
  · exact absurd (by simp) hg1
  · exact Or.inr ⟨0, by norm_num, by simp [wJ]⟩
  · refine Or.inr ⟨0, by norm_num, ?_⟩
    rw [← centralizer_sq_eq (wJ_cube 0), wJ_sq]
  · exact Or.inl (by simp)
  · exact Or.inr ⟨1, by norm_num, by simp [wJ]⟩
  · refine Or.inr ⟨2, by norm_num, ?_⟩
    rw [← centralizer_sq_eq (wJ_cube 2), wJ_sq]
  · refine Or.inl ?_
    rw [pow_zero, mul_one, centralizer_sq_eq z_cube]
  · exact Or.inr ⟨2, by norm_num, by simp [wJ]⟩
  · refine Or.inr ⟨1, by norm_num, ?_⟩
    rw [← centralizer_sq_eq (wJ_cube 1), wJ_sq]

theorem conj_mem_core {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) {v : G} (hv : v ∈ pPrimeCoreOf 3 H) :
    g * v * g⁻¹ ∈ pPrimeCoreOf 3 H := by
  have hH : H.map (MulAut.conj g).toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp hg
  have h := pPrimeCoreOf_map_mulEquiv (MulAut.conj g) 3 H
  rw [hH] at h
  rw [h]
  exact ⟨v, hv, by simp⟩

theorem xJ_mem_E0 : xJ ∈ Ej 0 := by rw [Ej_zero]; exact subset_closure (by simp)

theorem zJ_mem_E0 : zJ ∈ Ej 0 := by rw [Ej_zero]; exact subset_closure (by simp)

theorem actJ_mem_E0 (j : ℕ) : actJ j ∈ Ej 0 := by
  unfold actJ
  split_ifs
  · exact zJ_mem_E0
  · exact xJ_mem_E0

theorem eq_top_of_E0 {K : Subgroup GJ} (hN : Ej 0 ≤ normalizer (K : Set GJ))
    (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (hgen : K ≤ ⨆ (g : GJ) (_ : g ∈ Ej 0) (_ : g ≠ 1),
      pPrimeCoreOf 3 (K ⊓ centralizer ({g} : Set GJ))) : K = ⊤ := by
  set U : ℕ → Subgroup GJ := fun k => pPrimeCoreOf 3 (K ⊓ centralizer ({wJ k} : Set GJ)) with hUdef
  set Uz := pPrimeCoreOf 3 (K ⊓ centralizer ({zJ} : Set GJ)) with hUzdef
  have hKU : K ≤ U 0 ⊔ U 1 ⊔ U 2 ⊔ Uz := by
    refine hgen.trans (iSup_le fun g => iSup_le fun hg => iSup_le fun hg1 => ?_)
    rcases centralizer_of_mem_E0 hg hg1 with h | ⟨k, hk, h⟩
    · rw [h]
      exact le_sup_right
    · rw [h]
      interval_cases k
      · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
      · exact le_sup_right.trans le_sup_left
  have hxN : xJ ∈ normalizer ((K ⊓ centralizer ({zJ} : Set GJ) : Subgroup GJ) : Set GJ) := by
    rw [mem_normalizer_iff]
    intro v
    have hK := mem_normalizer_iff.1 (hN xJ_mem_E0) v
    have e3 : xJ * zJ * xJ⁻¹ = zJ := by rw [← zJ_comm_xJ.eq, mul_inv_cancel_right]
    have hc : v * zJ = zJ * v ↔ xJ * v * xJ⁻¹ * zJ = zJ * (xJ * v * xJ⁻¹) := by
      constructor
      · intro h
        calc xJ * v * xJ⁻¹ * zJ = xJ * v * xJ⁻¹ * (xJ * zJ * xJ⁻¹) := by rw [e3]
          _ = xJ * (v * zJ) * xJ⁻¹ := by group
          _ = xJ * (zJ * v) * xJ⁻¹ := by rw [h]
          _ = (xJ * zJ * xJ⁻¹) * (xJ * v * xJ⁻¹) := by group
          _ = zJ * (xJ * v * xJ⁻¹) := by rw [e3]
      · intro h
        calc v * zJ = xJ⁻¹ * ((xJ * v * xJ⁻¹) * (xJ * zJ * xJ⁻¹)) * xJ := by group
          _ = xJ⁻¹ * ((xJ * v * xJ⁻¹) * zJ) * xJ := by rw [e3]
          _ = xJ⁻¹ * (zJ * (xJ * v * xJ⁻¹)) * xJ := by rw [h]
          _ = xJ⁻¹ * ((xJ * zJ * xJ⁻¹) * (xJ * v * xJ⁻¹)) * xJ := by rw [e3]
          _ = zJ * v := by group
    simp only [mem_inf, mem_centralizer_singleton_iff]
    exact and_congr hK hc
  have hUz : ∀ v ∈ Uz, xJ * v * xJ⁻¹ ∈ Uz := fun v hv => conj_mem_core hxN hv
  obtain ⟨j0, hj03, hj06, hZc⟩ := core_z_single hUz
  have hWc : ∀ k < 3, ∀ u ∈ U k, u = 1 ∨ ∃ p < 3, u = tJ (3 * k + p) :=
    fun k hk u hu => core_w hk hu
  have hUK : ∀ {H : Subgroup GJ} {u : GJ}, u ∈ pPrimeCoreOf 3 (K ⊓ H) → u ∈ K :=
    fun hu => (mem_inf.1 (mem_of_mem_pPrimeCoreOf hu)).1
  have hW : ∀ k < 3, (∀ u ∈ U k, u = 1) ∨ ∀ q < 3, tJ (3 * k + q) ∈ K := by
    intro k hk
    by_cases h : ∀ u ∈ U k, u = 1
    · exact Or.inl h
    · right
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U k, u ≠ 1 := by
        by_contra hc
        exact h fun u hu => by_contra fun hne => hc ⟨u, hu, hne⟩
      rcases hWc k hk u hu with h1 | ⟨p, hp, rfl⟩
      · exact absurd h1 hu1
      · exact all_mem (by omega) hp (hN (actJ_mem_E0 k)) (hUK hu)
  have hZ : (∀ u ∈ Uz, u = 1) ∨ ∀ q < 3, tJ (3 * j0 + q) ∈ K := by
    by_cases h : ∀ u ∈ Uz, u = 1
    · exact Or.inl h
    · right
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ Uz, u ≠ 1 := by
        by_contra hc
        exact h fun u hu => by_contra fun hne => hc ⟨u, hu, hne⟩
      rcases hZc u hu with h1 | ⟨p, hp, rfl⟩
      · exact absurd h1 hu1
      · exact all_mem hj06 hp (hN (actJ_mem_E0 j0)) (hUK hu)
  have gen : ∀ s < 4, (∀ j ∈ genSets.getD s [], ∀ q < 3, tJ (3 * j + q) ∈ K) → K = ⊤ :=
    fun s hs h => eq_top_of_gen hs h
  have two : ∀ s < 6, (∀ k < 3, (∀ u ∈ U k, u = 1) ∨ k ∈ twoSets.getD s []) →
      ((∀ u ∈ Uz, u = 1) ∨ j0 ∈ twoSets.getD s []) → False := by
    intro s hs hk hz
    apply false_of_le_two hKp hK1 hs
    refine hKU.trans (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_)
    rotate_right
    · intro u hu
      rcases hz with h | h
      · rw [h u hu]; exact one_mem _
      · rcases hZc u hu with h1 | ⟨p, hp, rfl⟩
        · rw [h1]; exact one_mem _
        · exact tJ_mem_two hs h hp
    all_goals
      first
      | (intro u hu
         rcases hk 0 (by norm_num) with h | h
         · rw [h u hu]; exact one_mem _
         · rcases hWc 0 (by norm_num) u hu with h1 | ⟨p, hp, rfl⟩
           · rw [h1]; exact one_mem _
           · exact tJ_mem_two hs h hp)
      | (intro u hu
         rcases hk 1 (by norm_num) with h | h
         · rw [h u hu]; exact one_mem _
         · rcases hWc 1 (by norm_num) u hu with h1 | ⟨p, hp, rfl⟩
           · rw [h1]; exact one_mem _
           · exact tJ_mem_two hs h hp)
      | (intro u hu
         rcases hk 2 (by norm_num) with h | h
         · rw [h u hu]; exact one_mem _
         · rcases hWc 2 (by norm_num) u hu with h1 | ⟨p, hp, rfl⟩
           · rw [h1]; exact one_mem _
           · exact tJ_mem_two hs h hp)
  by_cases hB : ∀ u ∈ Uz, u = 1
  · rcases hW 0 (by norm_num) with h0 | h0
    · exact (two 2 (by norm_num) (fun k hk => by
        interval_cases k
        exacts [Or.inl h0, Or.inr (by decide), Or.inr (by decide)]) (Or.inl hB)).elim
    rcases hW 1 (by norm_num) with h1 | h1
    · exact (two 1 (by norm_num) (fun k hk => by
        interval_cases k
        exacts [Or.inr (by decide), Or.inl h1, Or.inr (by decide)]) (Or.inl hB)).elim
    rcases hW 2 (by norm_num) with h2 | h2
    · exact (two 0 (by norm_num) (fun k hk => by
        interval_cases k
        exacts [Or.inr (by decide), Or.inr (by decide), Or.inl h2]) (Or.inl hB)).elim
    refine gen 3 (by norm_num) fun j hj => ?_
    simp only [genSets, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    exacts [h0, h1, h2]
  · have hz := hZ.resolve_left hB
    have hj0 : j0 = 3 ∨ j0 = 4 ∨ j0 = 5 := by omega
    rcases hj0 with rfl | rfl | rfl
    · rcases hW 2 (by norm_num) with h2 | h2
      · exact (two 3 (by norm_num) (fun k hk => by
          interval_cases k
          exacts [Or.inr (by decide), Or.inr (by decide), Or.inl h2]) (Or.inr (by decide))).elim
      · refine gen 0 (by norm_num) fun j hj => ?_
        simp only [genSets, List.getD_cons_zero, List.mem_cons, List.not_mem_nil,
          or_false] at hj
        rcases hj with rfl | rfl
        exacts [h2, hz]
    · rcases hW 0 (by norm_num) with h0 | h0
      · exact (two 4 (by norm_num) (fun k hk => by
          interval_cases k
          exacts [Or.inl h0, Or.inr (by decide), Or.inr (by decide)]) (Or.inr (by decide))).elim
      · refine gen 2 (by norm_num) fun j hj => ?_
        simp only [genSets, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
          List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        exacts [h0, hz]
    · rcases hW 1 (by norm_num) with h1 | h1
      · exact (two 5 (by norm_num) (fun k hk => by
          interval_cases k
          exacts [Or.inr (by decide), Or.inl h1, Or.inr (by decide)]) (Or.inr (by decide))).elim
      · refine gen 1 (by norm_num) fun j hj => ?_
        simp only [genSets, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
          List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        exacts [h1, hz]

theorem coe_smul_sylow {G : Type*} [Group G] {p : ℕ} (g : G) (S : Sylow p G) :
    ((g • S : Sylow p G) : Subgroup G) = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul]
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map]
  constructor
  · intro hy
    exact ⟨_, hy, by rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, smul_inv_smul]⟩
  · rintro ⟨z, hz, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, inv_smul_smul]

theorem exists_map_conj_eq_E0 {E : Subgroup GJ} (hE : Nat.card E = 9) :
    ∃ g : GJ, E.map (MulAut.conj g).toMonoidHom = Ej 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  obtain ⟨S, hS⟩ := hEp.exists_le_sylow
  have hP3p : IsPGroup 3 P3 := IsPGroup.of_card (n := 3) (by rw [card_P3]; norm_num)
  let P3s : Sylow 3 GJ := hP3p.toSylow (by
    have h1 := Subgroup.card_mul_index P3
    rw [card_P3, card_GJ] at h1
    omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GJ S P3s
  have hP : (P3 : Subgroup GJ) = (S : Subgroup GJ).map (MulAut.conj g).toMonoidHom := by
    rw [← coe_smul_sylow, hg]
    rfl
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ P3 := by
    rw [hP]
    exact map_mono hS
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [card_map_of_injective (MulAut.conj g).injective, hE]
  have hmem : E.map (MulAut.conj g).toMonoidHom ∈ Set.range Ej := by
    rw [← nine_eq]
    exact ⟨hle, hcard⟩
  obtain ⟨j, hj⟩ := hmem
  obtain ⟨n, -, hn⟩ := exists_conj_E0 j
  refine ⟨n * g, ?_⟩
  have h1 : (Ej j).map (MulAut.conj n).toMonoidHom = Ej 0 := by
    rw [← hn, CFSG.conjugate, Subgroup.map_map]
    convert Subgroup.map_id (Ej 0)
    ext y
    simp
  rw [← h1, hj, Subgroup.map_map]
  congr 1

theorem inspectSig148_GJ : InspectSig148 GJ (· = ⊤) := by
  rw [inspectSig148_iff]
  intro E K hEK
  obtain ⟨g, hg⟩ := exists_map_conj_eq_E0 hEK.1
  have h := hEK.map (MulAut.conj g)
  rw [hg] at h
  have htop := eq_top_of_E0 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  rw [eq_top_iff]
  intro x _
  have hx : (MulAut.conj g) x ∈ K.map (MulAut.conj g).toMonoidHom := by
    rw [htop]; exact mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← (MulAut.conj g).injective hyx]

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.J2
