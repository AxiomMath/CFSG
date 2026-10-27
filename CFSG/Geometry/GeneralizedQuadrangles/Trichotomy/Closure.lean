module

public import CFSG.Geometry.GeneralizedQuadrangles.Trichotomy.Spans4
public import CFSG.Geometry.GeneralizedQuadrangles.Subquadrangle

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

theorem spanOrLine_inter_neighborSet_left
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {A B a b : V} (hA : c A = 1) (hAa : Γ.Adj A a) (hB : c B = 1) (hBb : Γ.Adj B b)
    (hAB : Γ.dist A B = 4) :
    spanOrLine hP a b ∩ Γ.neighborSet A ⊆ {a} := by
  classical
  intro u hu
  obtain ⟨huS, huA⟩ := hu
  by_cases h4 : Γ.dist a b = 4
  · rw [spanOrLine_of_dist_eq_four hP h4] at huS
    have hle : (spanSet Γ a b ∩ Γ.neighborSet A).ncard ≤ 1 :=
      ncard_spanSet_inter_neighborSet_le_one hP hT h4 A
    have haS : a ∈ spanSet Γ a b := left_mem_spanSet h4
    have haA : a ∈ Γ.neighborSet A := by simpa using hAa
    have hsub : ({a, u} : Set V) ⊆ spanSet Γ a b ∩ Γ.neighborSet A := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨haS, haA⟩
      · exact ⟨huS, huA⟩
    have hpair : ({a, u} : Set V).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hle
    simp only [Set.mem_singleton_iff]
    by_contra hne
    rw [Set.ncard_pair (Ne.symm hne)] at hpair
    omega
  · by_cases h2 : Γ.dist a b = 2
    · rw [spanOrLine_of_dist_eq_two hP h2] at huS
      let W := commonNeighbor hP h2
      have haW : Γ.Adj a W := commonNeighbor_adj_left hP h2
      have hbW : Γ.Adj b W := commonNeighbor_adj_right hP h2
      have huW : Γ.Adj W u := huS
      by_contra hne
      have hAW : A = W :=
        eq_of_two_common_points hP (Ne.symm hne) hAa huA haW.symm huW
      have hbA : Γ.Adj b A := hAW.symm ▸ hbW
      have h1 : Γ.dist A b = 1 := by
        rw [SimpleGraph.dist_comm]
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hbA
      have h2' : Γ.dist b B = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hBb.symm
      have htri := hP.connected.dist_triangle (u := A) (v := b) (w := B)
      omega
    · have hnil : spanOrLine hP a b = ∅ := by
        rw [spanOrLine, if_neg h4, dif_neg h2]
      rw [hnil] at huS
      exact huS.elim

theorem spanOrLine_inter_neighborSet_right
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {A B a b : V} (hA : c A = 1) (hAa : Γ.Adj A a) (hB : c B = 1) (hBb : Γ.Adj B b)
    (hAB : Γ.dist A B = 4) :
    spanOrLine hP a b ∩ Γ.neighborSet B ⊆ {b} := by
  have h := spanOrLine_inter_neighborSet_left hP hT c hB hBb hA hAa (by rwa [dist_comm])
  simpa [spanOrLine_comm hP a b] using h

theorem existsUnique_adj_dist_two_of_mem_neighborSet
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {A B a : V} (hA : c A = 1) (hAa : Γ.Adj A a) (hB : c B = 1) (hAB : Γ.dist A B = 4) :
    ∃! b, Γ.Adj B b ∧ Γ.dist a b = 2 := by
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hA hAa
  have hnot : ¬ Γ.Adj a B := by
    intro h
    have h1 : Γ.dist A a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hAa
    have h2 : Γ.dist a B = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    have htri := hP.connected.dist_triangle (u := A) (v := a) (w := B)
    omega
  have h3 : Γ.dist a B = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hnot (by rw [ha0, hB]; decide)
  exact existsUnique_proj hP h3

theorem dist_eq_four_of_mem_neighborSet_of_ne_proj
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {A B a b b0 : V} (hA : c A = 1) (hAa : Γ.Adj A a) (hB : c B = 1)
    (hAB : Γ.dist A B = 4) (hbB : Γ.Adj B b) (hb0B : Γ.Adj B b0)
    (hb0 : Γ.dist a b0 = 2) (hne : b ≠ b0) : Γ.dist a b = 4 := by
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hA hAa
  have hb0' : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hB hbB
  have hne0 : Γ.dist a b ≠ 0 := by
    intro h
    have hab : a = b := (hP.connected.dist_eq_zero_iff).mp h
    have h1 : Γ.dist A b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr (hab ▸ hAa)
    have h2 : Γ.dist b B = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hbB.symm
    have htri := hP.connected.dist_triangle (u := A) (v := b) (w := B)
    omega
  have heven : Even (Γ.dist a b) :=
    (hP.eq_iff_even_dist c a b).1 (by rw [ha0, hb0'])
  have hle : Γ.dist a b ≤ 4 := hP.dist_le (by norm_num) a b
  by_contra h4
  have hd2 : Γ.dist a b = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have huniq := existsUnique_adj_dist_two_of_mem_neighborSet hP c hA hAa hB hAB
  exact hne (huniq.unique ⟨hbB, hd2⟩ ⟨hb0B, hb0⟩)

theorem ncard_spanOrLine_of_dist_four
    (hP : IsGeneralizedPolygon Γ 4) {c : Γ.Coloring (Fin 2)} {p : ℕ}
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {a b : V} (h4 : Γ.dist a b = 4) (ha : c a = 0) :
    (spanOrLine hP a b).ncard = p + 1 := by
  rw [spanOrLine_of_dist_eq_four hP h4]
  exact hp a b ha h4

theorem ncard_spanOrLine_of_dist_two
    (hP : IsGeneralizedPolygon Γ 4) {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    {a b : V} (h2 : Γ.dist a b = 2) (ha : c a = 0) :
    (spanOrLine hP a b).ncard = s + 1 := by
  rw [spanOrLine_of_dist_eq_two hP h2]
  have hW : c (commonNeighbor hP h2) = 1 :=
    color_eq_one_of_adj_of_color_eq_zero ha (commonNeighbor_adj_left hP h2)
  rw [ncard_neighborSet, hdeg, if_neg (by rw [hW]; decide)]


private theorem mem_spanOrLine_right (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {a b : V} (ha : c a = 0) (hb : c b = 0) (hne : a ≠ b) :
    b ∈ spanOrLine hP a b := by
  have heven : Even (Γ.dist a b) :=
    (hP.eq_iff_even_dist c a b).1 (by rw [ha, hb])
  have hle : Γ.dist a b ≤ 4 := hP.dist_le (by norm_num) a b
  have hne0 : Γ.dist a b ≠ 0 := by
    intro h
    exact hne ((hP.connected.dist_eq_zero_iff).mp h)
  obtain ⟨k, hk⟩ := heven
  have hcases : Γ.dist a b = 2 ∨ Γ.dist a b = 4 := by omega
  rcases hcases with h2 | h4
  · rw [spanOrLine_of_dist_eq_two hP h2]
    exact (commonNeighbor_adj_right hP h2).symm
  · rw [spanOrLine_of_dist_eq_four hP h4]
    exact right_mem_spanSet h4

private theorem mem_spanOrLine_left (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {a b : V} (ha : c a = 0) (hb : c b = 0) (hne : a ≠ b) :
    a ∈ spanOrLine hP a b := by
  have h := mem_spanOrLine_right hP c hb ha (Ne.symm hne)
  rw [spanOrLine_comm hP a b]
  exact h

noncomputable def fan (hP : IsGeneralizedPolygon Γ 4) (a B : V) : Finset V := by
  classical
  exact (Γ.neighborFinset B).biUnion fun b => (spanOrLine hP a b).toFinset

private theorem fan_arith (s p : ℕ) (hs : 1 ≤ s) (hp : 1 ≤ p) :
    (s + 1) + 1 + (s - 1 + (s + 1 - 1) * (p - 1)) = s * p + s + 1 := by
  have h1 : s + 1 - 1 = s := by omega
  rw [h1]
  have h2 : s * (p - 1) = s * p - s := by rw [Nat.mul_sub, mul_one]
  rw [h2]
  have hsp : s ≤ s * p := Nat.le_mul_of_pos_right s (by omega)
  omega

theorem card_fan
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t p : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {A B : V} (hA : c A = 1) (hB : c B = 1) (hAB : Γ.dist A B = 4) {a : V}
    (hAa : Γ.Adj A a) :
    (fan hP a B).card = s * p + s + 1 := by
  classical
  let Bf : Finset V := Γ.neighborFinset B
  let S : V → Finset V := fun b => (spanOrLine hP a b).toFinset
  let U : V → Finset V := fun b => S b \ (Bf ∪ {a})
  obtain ⟨b0, hb0spec, huniq⟩ := existsUnique_adj_dist_two_of_mem_neighborSet hP c hA hAa hB hAB
  obtain ⟨hb0B, hb0d⟩ := hb0spec
  have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hA hAa
  have hb0Bf : b0 ∈ Bf := by simpa [Bf] using hb0B
  have haBf : a ∉ Bf := by
    intro ha
    have haB : Γ.Adj a B := (by simpa [Bf] using ha : Γ.Adj B a).symm
    have h1 : Γ.dist A a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hAa
    have h2 : Γ.dist a B = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr haB
    have htri := hP.connected.dist_triangle (u := A) (v := a) (w := B)
    omega
  have hBfcard : Bf.card = s + 1 := by
    rw [show Bf.card = Γ.degree B by
      rw [show Bf = Γ.neighborFinset B from rfl, card_neighborFinset_eq_degree]]
    rw [hdeg B, if_neg (by rw [hB]; decide)]
  have hInter : ∀ b ∈ Bf, S b ∩ (Bf ∪ {a}) = {a, b} := by
    intro b hb
    have hbB : Γ.Adj B b := by simpa [Bf] using hb
    have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hB hbB
    have hmem_a : a ∈ S b := by
      simpa [S] using mem_spanOrLine_left hP c ha0 hb0 (by
        intro hab
        exact haBf (hab ▸ hb))
    have hmem_b : b ∈ S b := by
      simpa [S] using mem_spanOrLine_right hP c ha0 hb0 (by
        intro hab
        exact haBf (hab ▸ hb))
    apply Finset.Subset.antisymm
    · intro u hu
      rw [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton] at hu
      obtain ⟨huS, huB | hua⟩ := hu
      · have huNB : u ∈ Γ.neighborSet B := by simpa [Bf] using huB
        have hmem := spanOrLine_inter_neighborSet_right hP hT c hA hAa hB hbB hAB
          ⟨by simpa [S] using huS, huNB⟩
        simp only [Set.mem_singleton_iff] at hmem
        rw [hmem]
        simp
      · rw [hua]
        simp
    · intro u hu
      rw [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hmem_a, Finset.mem_union_right _ (by simp)⟩
      · exact Finset.mem_inter.mpr ⟨hmem_b, Finset.mem_union_left _ hb⟩
  have hScard : ∀ b ∈ Bf, (S b).card = if b = b0 then s + 1 else p + 1 := by
    intro b hb
    have hbB : Γ.Adj B b := by simpa [Bf] using hb
    by_cases hb0 : b = b0
    · rw [if_pos hb0]
      rw [show (S b).card = (spanOrLine hP a b).ncard by
        rw [Set.ncard_eq_toFinset_card']]
      rw [hb0]
      exact ncard_spanOrLine_of_dist_two hP hdeg hb0d ha0
    · rw [if_neg hb0]
      have h4 : Γ.dist a b = 4 :=
        dist_eq_four_of_mem_neighborSet_of_ne_proj hP c hA hAa hB hAB hbB hb0B hb0d hb0
      rw [show (S b).card = (spanOrLine hP a b).ncard by
        rw [Set.ncard_eq_toFinset_card']]
      exact ncard_spanOrLine_of_dist_four hP hp h4 ha0
  have hUcard : ∀ b ∈ Bf, (U b).card = if b = b0 then s - 1 else p - 1 := by
    intro b hb
    have hinter := hInter b hb
    have hab : a ≠ b := by
      intro hab
      exact haBf (hab ▸ hb)
    have hcard2 : ({a, b} : Finset V).card = 2 := by
      rw [Finset.card_pair hab]
    calc
      (U b).card = (S b \ (Bf ∪ {a})).card := rfl
      _ = (S b).card - ((Bf ∪ {a}) ∩ S b).card := Finset.card_sdiff
      _ = (S b).card - ({a, b} : Finset V).card := by
        rw [Finset.inter_comm, hinter]
      _ = (S b).card - 2 := by rw [hcard2]
      _ = if b = b0 then s - 1 else p - 1 := by
        rw [hScard b hb]
        split <;> omega
  have hfan_eq : (fan hP a B) = Bf ∪ {a} ∪ Bf.biUnion U := by
    ext u
    simp only [fan, S, U, Finset.mem_biUnion, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_sdiff]
    constructor
    · rintro ⟨b, hb, huS⟩
      by_cases hu : u ∈ Bf ∨ u = a
      · simp [hu]
      · exact Or.inr ⟨b, hb, huS, hu⟩
    · intro hu
      rcases hu with (hu | hua) | ⟨b, hb, huS, -⟩
      · have huB : Γ.Adj B u := by simpa [Bf] using hu
        have hu0 : c u = 0 := color_eq_zero_of_adj_of_color_eq_one hB huB
        refine ⟨u, hu, ?_⟩
        simpa [S] using mem_spanOrLine_right hP c ha0 hu0 (by
          intro hau
          exact haBf (hau ▸ hu))
      · rw [hua]
        have hb00 : c b0 = 0 := color_eq_zero_of_adj_of_color_eq_one hB hb0B
        exact ⟨b0, hb0Bf, by
          simpa [S] using mem_spanOrLine_left hP c ha0 hb00 (by
            intro hab
            exact haBf (hab ▸ hb0Bf))⟩
      · exact ⟨b, hb, huS⟩
  have hdisj1 : Disjoint Bf ({a} : Finset V) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_singleton] at hu'
    exact haBf (hu' ▸ hu)
  have hdisjU : (Bf : Set V).PairwiseDisjoint U := by
    intro b hb b' hb' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_sdiff] at hu hu'
    obtain ⟨huS, huNot⟩ := hu
    obtain ⟨huS', -⟩ := hu'
    have hbB : Γ.Adj B b := by simpa [Bf] using hb
    have hb'B : Γ.Adj B b' := by simpa [Bf] using hb'
    have hpair : (a, b) ≠ (a, b') := by
      intro h
      exact hne (congrArg Prod.snd h)
    have hinter := spanOrLine_inter_subset hP hT c hA hB hAB hAa hAa hbB hb'B hpair
    have huSet : u ∈ Γ.neighborSet A ∪ Γ.neighborSet B := by
      apply hinter
      constructor
      · simpa [S] using huS
      · simpa [S] using huS'
    rcases huSet with huA | huB
    · have hmem := spanOrLine_inter_neighborSet_left hP hT c hA hAa hB hbB hAB
        ⟨by simpa [S] using huS, huA⟩
      simp only [Set.mem_singleton_iff] at hmem
      exact huNot (by rw [Finset.mem_union]; exact Or.inr (by simp [hmem]))
    · exact huNot (by rw [Finset.mem_union]; exact Or.inl (by simpa [Bf] using huB))
  have hdisj2 : Disjoint (Bf ∪ {a}) (Bf.biUnion U) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_biUnion] at hu'
    obtain ⟨b, hb, hub⟩ := hu'
    rw [Finset.mem_sdiff] at hub
    exact hub.2 hu
  have hsumU : ∑ b ∈ Bf, (U b).card = (s - 1) + (Bf.card - 1) * (p - 1) := by
    rw [← Finset.add_sum_erase Bf (fun b => (U b).card) hb0Bf]
    have hb0card : (U b0).card = s - 1 := by
      rw [hUcard b0 hb0Bf]
      simp
    have hrest : ∑ b ∈ Bf.erase b0, (U b).card = (Bf.erase b0).card * (p - 1) := by
      rw [Finset.sum_congr rfl ?_, Finset.sum_const, smul_eq_mul]
      intro b hb
      have hb' := Finset.mem_of_mem_erase hb
      rw [Finset.mem_erase] at hb
      obtain ⟨hbne, -⟩ := hb
      rw [hUcard b hb']
      simp [hbne]
    rw [hb0card, hrest, Finset.card_erase_of_mem hb0Bf, hBfcard]
  have hp1 : 1 ≤ p := by
    have hs2 : 2 ≤ s := two_le_s hP hT c hdeg
    have hBf3 : 3 ≤ Bf.card := by rw [hBfcard]; omega
    have hpos : 0 < (Bf.erase b0).card := by
      rw [Finset.card_erase_of_mem hb0Bf]
      omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_erase] at hb
    have hbB : Γ.Adj B b := by simpa [Bf] using hb.2
    have hbne : b ≠ b0 := hb.1
    have h4 : Γ.dist a b = 4 :=
      dist_eq_four_of_mem_neighborSet_of_ne_proj hP c hA hAa hB hAB hbB hb0B hb0d hbne
    have hspan : (spanSet Γ a b).ncard = p + 1 := hp a b ha0 h4
    have hne : a ≠ b := by
      intro hab
      rw [hab, SimpleGraph.dist_self] at h4
      omega
    have h2 : 2 ≤ (spanSet Γ a b).ncard := by
      have hlt : 1 < (spanSet Γ a b).ncard :=
        (Set.one_lt_ncard (s := spanSet Γ a b)).mpr
          ⟨a, left_mem_spanSet h4, b, right_mem_spanSet h4, hne⟩
      omega
    omega
  calc
    (fan hP a B).card = (Bf ∪ {a} ∪ Bf.biUnion U).card := by rw [hfan_eq]
    _ = (Bf ∪ {a}).card + (Bf.biUnion U).card :=
      Finset.card_union_of_disjoint hdisj2
    _ = Bf.card + 1 + (Bf.biUnion U).card := by
      rw [Finset.card_union_of_disjoint hdisj1, Finset.card_singleton]
    _ = Bf.card + 1 + ∑ b ∈ Bf, (U b).card := by rw [Finset.card_biUnion hdisjU]
    _ = s * p + s + 1 := by
      rw [hsumU, hBfcard]
      exact fan_arith s p (by
        have := two_le_s hP hT c hdeg
        omega) hp1


theorem ncard_spanUnion
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t p : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {A B : V} (hA : c A = 1) (hB : c B = 1) (hAB : Γ.dist A B = 4) :
    (spanUnion hP A B).ncard = (s + 1) * (s * p + 1) := by
  classical
  let Af : Finset V := Γ.neighborFinset A
  let Bf : Finset V := Γ.neighborFinset B
  let F : V → Finset V := fun a => fan hP a B
  have hAfcard : Af.card = s + 1 := by
    rw [show Af.card = Γ.degree A by
      rw [show Af = Γ.neighborFinset A from rfl, card_neighborFinset_eq_degree]]
    rw [hdeg A, if_neg (by rw [hA]; decide)]
  have hBfcard : Bf.card = s + 1 := by
    rw [show Bf.card = Γ.degree B by
      rw [show Bf = Γ.neighborFinset B from rfl, card_neighborFinset_eq_degree]]
    rw [hdeg B, if_neg (by rw [hB]; decide)]
  have hane : ∀ a ∈ Af, a ∉ Bf := by
    intro a ha haB
    have haA : Γ.Adj A a := by simpa [Af] using ha
    have haB' : Γ.Adj B a := by simpa [Bf] using haB
    have h1 : Γ.dist A a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr haA
    have h2 : Γ.dist a B = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr haB'.symm
    have htri := hP.connected.dist_triangle (u := A) (v := a) (w := B)
    omega
  have hFcard : ∀ a ∈ Af, (F a).card = s * p + s + 1 := by
    intro a ha
    have haA : Γ.Adj A a := by simpa [Af] using ha
    exact card_fan hP hT c hdeg hp hA hB hAB haA
  have hBfsub : ∀ a ∈ Af, Bf ⊆ F a := by
    intro a ha b hb
    have haA : Γ.Adj A a := by simpa [Af] using ha
    have hbB : Γ.Adj B b := by simpa [Bf] using hb
    have ha0 : c a = 0 := color_eq_zero_of_adj_of_color_eq_one hA haA
    have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hB hbB
    have hne : a ≠ b := by
      intro hab
      exact hane a ha (hab ▸ hb)
    rw [show F a = fan hP a B from rfl, fan, Finset.mem_biUnion]
    exact ⟨b, hb, by simpa using mem_spanOrLine_right hP c ha0 hb0 hne⟩
  have hInterAf : ∀ a ∈ Af, F a ∩ Af ⊆ {a} := by
    intro a ha u hu
    rw [Finset.mem_inter] at hu
    obtain ⟨huF, huAf⟩ := hu
    rw [show F a = fan hP a B from rfl, fan, Finset.mem_biUnion] at huF
    obtain ⟨b, hb, huS⟩ := huF
    have haA : Γ.Adj A a := by simpa [Af] using ha
    have hbB : Γ.Adj B b := by simpa [Bf] using hb
    have hmem := spanOrLine_inter_neighborSet_left hP hT c hA haA hB hbB hAB
      ⟨by simpa using huS, by simpa [Af] using huAf⟩
    simpa using hmem
  have hInter : ∀ a ∈ Af, ∀ a' ∈ Af, a ≠ a' → F a ∩ F a' = Bf := by
    intro a ha a' ha' hne
    apply Finset.Subset.antisymm
    · intro u hu
      have huF : u ∈ F a := (Finset.mem_inter.mp hu).1
      have huF2 : u ∈ F a' := (Finset.mem_inter.mp hu).2
      rw [show F a = fan hP a B from rfl, fan, Finset.mem_biUnion] at huF
      have huF2' : u ∈ F a' := huF2
      rw [show F a' = fan hP a' B from rfl, fan, Finset.mem_biUnion] at huF2'
      obtain ⟨b, hb, huS⟩ := huF
      obtain ⟨b', hb', huS'⟩ := huF2' 
      have haA : Γ.Adj A a := by simpa [Af] using ha
      have ha'A : Γ.Adj A a' := by simpa [Af] using ha'
      have hbB : Γ.Adj B b := by simpa [Bf] using hb
      have hb'B : Γ.Adj B b' := by simpa [Bf] using hb'
      have hpair : (a, b) ≠ (a', b') := by
        intro h
        exact hne (congrArg Prod.fst h)
      have hinter := spanOrLine_inter_subset hP hT c hA hB hAB haA ha'A hbB hb'B hpair
      have huSet : u ∈ Γ.neighborSet A ∪ Γ.neighborSet B :=
        hinter ⟨by simpa using huS, by simpa using huS'⟩
      rcases huSet with huA | huB
      · have hmem := spanOrLine_inter_neighborSet_left hP hT c hA haA hB hbB hAB
          ⟨by simpa using huS, huA⟩
        simp only [Set.mem_singleton_iff] at hmem
        have haF' : a ∈ F a' := hmem.symm ▸ huF2
        have hmem' := hInterAf a' ha' (Finset.mem_inter.mpr ⟨haF', by simpa [Af] using ha⟩)
        simp only [Finset.mem_singleton] at hmem'
        exact absurd hmem' hne
      · simpa [Bf] using huB
    · intro u hu
      exact Finset.mem_inter.mpr ⟨hBfsub a ha hu, hBfsub a' ha' hu⟩
  have hsetEq : spanUnion hP A B = (↑(Af.biUnion F) : Set V) := by
    ext u
    constructor
    · rintro ⟨a, b, ha, hb, hu⟩
      refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨a, by simpa [Af] using ha, ?_⟩)
      exact Finset.mem_biUnion.mpr ⟨b, by simpa [Bf] using hb, by simpa using hu⟩
    · intro hu
      rw [Finset.mem_coe, Finset.mem_biUnion] at hu
      obtain ⟨a, ha, hu⟩ := hu
      rw [show F a = fan hP a B from rfl, fan, Finset.mem_biUnion] at hu
      obtain ⟨b, hb, hu⟩ := hu
      exact ⟨a, b, by simpa [Af] using ha, by simpa [Bf] using hb, by simpa using hu⟩
  have hdisj : (Af : Set V).PairwiseDisjoint (fun a => F a \ Bf) := by
    intro a ha a' ha' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_sdiff] at hu hu'
    have hmem : u ∈ F a ∩ F a' := Finset.mem_inter.mpr ⟨hu.1, hu'.1⟩
    rw [hInter a ha a' ha' hne] at hmem
    exact hu.2 hmem
  have hunion : Af.biUnion F = Bf ∪ Af.biUnion (fun a => F a \ Bf) := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨a, ha, hua⟩
      by_cases huB : u ∈ Bf
      · exact Or.inl huB
      · exact Or.inr ⟨a, ha, hua, huB⟩
    · rintro (huB | ⟨a, ha, hua, -⟩)
      · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hAfcard]; omega)
        exact ⟨a, ha, hBfsub a ha huB⟩
      · exact ⟨a, ha, hua⟩
  have hdisjB : Disjoint Bf (Af.biUnion (fun a => F a \ Bf)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_biUnion] at hu'
    obtain ⟨a, ha, hua⟩ := hu'
    rw [Finset.mem_sdiff] at hua
    exact hua.2 hu
  have hFdiff : ∀ a ∈ Af, (F a \ Bf).card = s * p := by
    intro a ha
    rw [Finset.card_sdiff_of_subset (hBfsub a ha), hFcard a ha, hBfcard]
    have hs : 1 ≤ s := by
      have := two_le_s hP hT c hdeg
      omega
    omega
  calc
    (spanUnion hP A B).ncard = (Af.biUnion F).card := by
      rw [hsetEq, Set.ncard_coe_finset]
    _ = (Bf ∪ Af.biUnion (fun a => F a \ Bf)).card := by rw [hunion]
    _ = Bf.card + (Af.biUnion (fun a => F a \ Bf)).card :=
      Finset.card_union_of_disjoint hdisjB
    _ = Bf.card + ∑ a ∈ Af, (F a \ Bf).card := by rw [Finset.card_biUnion hdisj]
    _ = (s + 1) * (s * p + 1) := by
      rw [Finset.sum_congr rfl hFdiff, Finset.sum_const, smul_eq_mul, hAfcard, hBfcard]
      ring


theorem neighborSet_subset_spanUnion_left
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L M : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4) :
    Γ.neighborSet L ⊆ spanUnion hP L M := by
  classical
  have hpos : 0 < (Γ.neighborFinset M).card := by
    rw [card_neighborFinset_eq_degree]
    have := hT M
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  have hbM : Γ.Adj M b := by simpa using hb
  intro l hl
  have hl0 : c l = 0 := color_eq_zero_of_adj_of_color_eq_one hL hl
  have hb0 : c b = 0 := color_eq_zero_of_adj_of_color_eq_one hM hbM
  have hne : l ≠ b := by
    intro h
    have hLMne : L ≠ M := by
      intro hEq
      rw [hEq, SimpleGraph.dist_self] at hLM
      omega
    have h2 : Γ.dist L M = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hl (h ▸ hbM).symm hLMne
    omega
  exact ⟨l, b, hl, hbM, by simpa using mem_spanOrLine_left hP c hl0 hb0 hne⟩

theorem neighborSet_subset_spanUnion_right
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L M : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4) :
    Γ.neighborSet M ⊆ spanUnion hP L M := by
  have h := neighborSet_subset_spanUnion_left hP hT c hM hL (by rwa [dist_comm])
  intro b hb
  rw [spanUnion_comm hP L M]
  exact h hb

theorem color_zero_of_mem_spanUnion
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {L M z : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hz : z ∈ spanUnion hP L M) : c z = 0 := by
  obtain ⟨x, y, hxL, hyM, hz⟩ := hz
  have hx0 : c x = 0 := color_eq_zero_of_adj_of_color_eq_one hL hxL
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hyM
  by_cases h4 : Γ.dist x y = 4
  · rw [spanOrLine_of_dist_eq_four hP h4] at hz
    rw [color_eq_of_mem_span hP hT c h4 hz, hx0]
  · by_cases h2 : Γ.dist x y = 2
    · rw [spanOrLine_of_dist_eq_two hP h2] at hz
      have hV : c (commonNeighbor hP h2) = 1 :=
        color_eq_one_of_adj_of_color_eq_zero hx0 (commonNeighbor_adj_left hP h2)
      exact color_eq_zero_of_adj_of_color_eq_one hV hz
    · have hnil : spanOrLine hP x y = ∅ := by
        rw [spanOrLine, if_neg h4, dif_neg h2]
      rw [hnil] at hz
      exact hz.elim


theorem spanUnion_eq_of_block
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M N W x y z1 z2 : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hLx : Γ.Adj L x) (hxW : Γ.Adj x W) (hWy : Γ.Adj W y) (hMy : Γ.Adj M y)
    (hz1W : Γ.Adj W z1) (hz1y : z1 ≠ y) (hz2M : Γ.Adj M z2) (hz2y : z2 ≠ y)
    (hz1z2 : Γ.dist z1 z2 = 4) (hN : c N = 1)
    (hNsub : Γ.neighborSet N ⊆ spanBlock Γ y z1 z2) (hNW : N ≠ W) (hNM : N ≠ M) :
    spanUnion hP N L = spanUnion hP L M := by
  classical
  have hy0 : c y = 0 := color_eq_zero_of_adj_of_color_eq_one hM hMy
  have hNy : Γ.Adj N y := adj_of_neighborSet_subset_spanBlock hP hT c hy0 hN hNsub
  have hNL : Γ.dist N L = 4 :=
    dist_eq_four_of_adj_line_of_ne hP c hL hM hLM hLx hxW hWy hMy hN hNy hNW
  have hcard1 : (spanUnion hP N L).ncard = (s + 1) * (s * p + 1) :=
    ncard_spanUnion hP hT c hdeg hp hN hL hNL
  have hcard2 : (spanUnion hP L M).ncard = (s + 1) * (s * p + 1) :=
    ncard_spanUnion hP hT c hdeg hp hL hM hLM
  have hsub : spanUnion hP N L ⊆ spanUnion hP L M :=
    spanUnion_subset_spanUnion hP hT c hH hp hdeg hL hM hLM hLx hxW hWy hMy
      hz1W hz1y hz2M hz2y hz1z2 hN hNsub hNW hNM
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [hcard2, hcard1])

theorem spanUnion_eq_of_block_symm
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M N W x y z1 z2 : V}
    (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hMx : Γ.Adj M x) (hxW : Γ.Adj x W) (hWy : Γ.Adj W y) (hLy : Γ.Adj L y)
    (hz1W : Γ.Adj W z1) (hz1y : z1 ≠ y) (hz2L : Γ.Adj L z2) (hz2y : z2 ≠ y)
    (hz1z2 : Γ.dist z1 z2 = 4) (hN : c N = 1)
    (hNsub : Γ.neighborSet N ⊆ spanBlock Γ y z1 z2) (hNW : N ≠ W) (hNL : N ≠ L) :
    spanUnion hP N M = spanUnion hP L M := by
  have h := spanUnion_eq_of_block hP hT c hH hdeg hp hM hL (by rwa [SimpleGraph.dist_comm])
    hMx hxW hWy hLy hz1W hz1y hz2L hz2y hz1z2 hN hNsub hNW hNL
  rw [spanUnion_comm hP L M]
  exact h


theorem eq_of_dist_two_of_mem_neighborSet
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2)) {L y z1 z2 : V}
    (hL : c L = 1) (hz1 : Γ.Adj L z1) (hyz1 : Γ.dist y z1 = 2)
    (hz2 : Γ.Adj L z2) (hyz2 : Γ.dist y z2 = 2) (hyL : ¬ Γ.Adj L y) :
    z1 = z2 := by
  have hz10 : c z1 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hz1
  have hy0 : c y = 0 := by
    rw [show c y = c z1 from (hP.eq_iff_even_dist c y z1).2 (by rw [hyz1]; norm_num), hz10]
  have hyL3 : Γ.dist y L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c (fun h => hyL h.symm) (by rw [hy0, hL]; decide)
  exact (existsUnique_proj hP hyL3).unique ⟨hz1, hyz1⟩ ⟨hz2, hyz2⟩


theorem dist_eq_four_of_mem_two_lines
    (hP : IsGeneralizedPolygon Γ 4) (c : Γ.Coloring (Fin 2))
    {L W z z1 z2 : V} (hLW : L ≠ W) (hL : c L = 1) (hW : c W = 1)
    (hzL : Γ.Adj L z) (hzW : Γ.Adj W z) (hz1W : Γ.Adj W z1) (hz1 : z1 ≠ z)
    (hz2L : Γ.Adj L z2) (hz2 : z2 ≠ z) : Γ.dist z1 z2 = 4 := by
  classical
  have hz10 : c z1 = 0 := color_eq_zero_of_adj_of_color_eq_one hW hz1W
  have hz20 : c z2 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hz2L
  have hz1z2 : z1 ≠ z2 := by
    intro h
    exact hLW (eq_of_two_common_points hP (Ne.symm hz1) hzW hz1W hzL (h ▸ hz2L)).symm
  have heven : Even (Γ.dist z1 z2) :=
    (hP.eq_iff_even_dist c z1 z2).1 (by rw [hz10, hz20])
  have hle : Γ.dist z1 z2 ≤ 4 := hP.dist_le (by norm_num) z1 z2
  have hne0 : Γ.dist z1 z2 ≠ 0 := by
    intro h0
    exact hz1z2 ((hP.connected.dist_eq_zero_iff).mp h0)
  by_contra h4
  have h2 : Γ.dist z1 z2 = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hTW : commonNeighbor hP h2 ≠ W := by
    intro hEq
    have hWz2 : Γ.Adj W z2 := (hEq ▸ commonNeighbor_adj_right hP h2).symm
    exact hLW (eq_of_two_common_points hP hz2 hWz2 hzW hz2L hzL).symm
  have hres := eq_left_or_eq_right_of_three_lines hP
    (M := commonNeighbor hP h2) (A := W) (B := L)
    (pA := z1) (pB := z2) (u := z) (Ne.symm hLW) hTW
    (commonNeighbor_adj_left hP h2).symm (commonNeighbor_adj_right hP h2).symm
    hz1W hzW hz2L hzL
  rcases hres with h | h
  · exact hz1 h
  · exact hz2 h


theorem spanOrLine_subset_spanUnion (hP : IsGeneralizedPolygon Γ 4) {L M x y : V}
    (hx : Γ.Adj L x) (hy : Γ.Adj M y) : spanOrLine hP x y ⊆ spanUnion hP L M := by
  intro u hu
  exact ⟨x, y, hx, hy, hu⟩

theorem neighborSet_commonNeighbor_subset_spanUnion_of_span
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M x y y1 y2 : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hxL : Γ.Adj L x) (hy1L : Γ.Adj L y1) (hy2M : Γ.Adj M y2)
    (h4 : Γ.dist y1 y2 = 4) (hy4 : y ∈ spanSet Γ y1 y2) (hyne1 : y ≠ y1)
    (hyne2 : y ≠ y2) (hxy : Γ.dist x y = 2) :
    Γ.neighborSet (commonNeighbor hP hxy) ⊆ spanUnion hP L M := by
  classical
  have hy0 : c y = 0 := by
    rw [color_eq_of_mem_span hP hT c h4 hy4]
    exact color_eq_zero_of_adj_of_color_eq_one hL hy1L
  have hy1_0 : c y1 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hy1L
  have hy2_0 : c y2 = 0 := color_eq_zero_of_adj_of_color_eq_one hM hy2M
  have hyNotL : ¬ Γ.Adj L y := by
    intro hyL
    have hle : (spanSet Γ y1 y2 ∩ Γ.neighborSet L).ncard ≤ 1 :=
      ncard_spanSet_inter_neighborSet_le_one hP hT h4 L
    have hsub : ({y, y1} : Set V) ⊆ spanSet Γ y1 y2 ∩ Γ.neighborSet L := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨hy4, hyL⟩
      · exact ⟨left_mem_spanSet h4, hy1L⟩
    have hpair : ({y, y1} : Set V).ncard ≤ 1 :=
      le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) hle
    have : y = y1 := by
      by_contra hne
      rw [Set.ncard_pair hne] at hpair
      omega
    exact hyne1 this
  have hnotAdj : ¬ Γ.Adj y2 L := by
    intro h
    have h1 : Γ.dist L y2 = 1 := by
      rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr h
    have h2 : Γ.dist y2 M = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hy2M.symm
    have htri := hP.connected.dist_triangle (u := L) (v := y2) (w := M)
    omega
  have hy2L3 : Γ.dist y2 L = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hnotAdj
      (by rw [hy2_0, hL]; decide)
  let z : V := proj hP hy2L3
  have hzL : Γ.Adj L z := proj_adj hP hy2L3
  have hzy2 : Γ.dist z y2 = 2 := by
    rw [SimpleGraph.dist_comm]
    exact proj_dist hP hy2L3
  have hz0 : c z = 0 := color_eq_zero_of_adj_of_color_eq_one hL hzL
  have hz_ne_y1 : z ≠ y1 := by
    intro h
    rw [h] at hzy2
    omega
  have hzy1 : Γ.dist z y1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hzL.symm hy1L hz_ne_y1
  have hztrace : z ∈ traceSet Γ y1 y2 :=
    ⟨by rwa [SimpleGraph.dist_comm], by rwa [SimpleGraph.dist_comm]⟩
  have hzy : Γ.dist y z = 2 :=
    dist_eq_two_of_mem_span_of_mem_trace hP hT h4 hy4 hztrace
  have hxeq : x = z :=
    eq_of_dist_two_of_mem_neighborSet hP c hL hxL (by rwa [SimpleGraph.dist_comm]) hzL hzy hyNotL
  subst x
  let W : V := commonNeighbor hP hzy2
  have hzW : Γ.Adj z W := commonNeighbor_adj_left hP hzy2
  have hy2W : Γ.Adj y2 W := commonNeighbor_adj_right hP hzy2
  have hW1 : c W = 1 := color_eq_one_of_adj_of_color_eq_zero hz0 hzW
  have hLW : L ≠ W := by
    intro hEq
    exact hnotAdj (hEq ▸ hy2W)
  obtain ⟨z1, hz1W, hz1ne⟩ := exists_adj_ne_of_isThick hT hzW.symm
  obtain ⟨z2, hz2L, hz2ne⟩ := exists_adj_ne_of_isThick hT hzL
  have hz10 : c z1 = 0 := color_eq_zero_of_adj_of_color_eq_one hW1 hz1W
  have hz20 : c z2 = 0 := color_eq_zero_of_adj_of_color_eq_one hL hz2L
  have hz1z2 : Γ.dist z1 z2 = 4 :=
    dist_eq_four_of_mem_two_lines hP c hLW hL hW1 hzL hzW.symm hz1W hz1ne hz2L hz2ne
  have hzz1 : Γ.dist z z1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hzW hz1W (Ne.symm hz1ne)
  have hzz2 : Γ.dist z z2 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hzL.symm hz2L (Ne.symm hz2ne)
  have hy1block : y1 ∈ spanBlock Γ z z1 z2 := by
    rw [spanBlock, mem_blockThrough]
    exact ⟨L, hzL.symm, ⟨z2, right_mem_spanSet hz1z2, hz2L⟩, hy1L⟩
  have hy2block : y2 ∈ spanBlock Γ z z1 z2 := by
    rw [spanBlock, mem_blockThrough]
    exact ⟨W, hzW, ⟨z1, left_mem_spanSet hz1z2, hz1W⟩, hy2W.symm⟩
  have hspanBlock : spanSet Γ y1 y2 ⊆ spanBlock Γ z z1 z2 :=
    spanSet_subset_spanBlock hP hT c (hH z hz0) hp hz0 hz10 hz20 hzz1 hzz2 hz1z2
      hy1block hy2block h4
  have hyblock : y ∈ spanBlock Γ z z1 z2 := hspanBlock hy4
  have hgoal : Γ.neighborSet (commonNeighbor hP hxy) ⊆ spanBlock Γ z z1 z2 := by
    rw [spanBlock, mem_blockThrough] at hyblock
    obtain ⟨T, hzT, hTspan, hTy⟩ := hyblock
    have hTeq : T = commonNeighbor hP hxy := eq_commonNeighbor hP hxy hzT hTy.symm
    intro u hu
    refine ⟨commonNeighbor hP hxy, commonNeighbor_adj_left hP hxy, ?_, hu⟩
    rw [← hTeq]
    exact hTspan
  have hblock : spanBlock Γ z z1 z2 ⊆ spanUnion hP L M := by
    have h := spanBlock_subset_spanUnion hP hT c hH hp hM hL (by rwa [SimpleGraph.dist_comm])
      hy2M hy2W hzW.symm hzL
      hz1W hz1ne hz2L hz2ne hz1z2
    rw [spanUnion_comm hP L M]
    exact h
  exact subset_trans hgoal hblock


theorem neighborSet_commonNeighbor_subset_spanUnion_of_mem_left
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    (hH : ∀ u : V, c u = 0 → HasPropertyH Γ u) {s t p : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hp : ∀ x y : V, c x = 0 → Γ.dist x y = 4 → (spanSet Γ x y).ncard = p + 1)
    {L M x y : V} (hL : c L = 1) (hM : c M = 1) (hLM : Γ.dist L M = 4)
    (hxL : Γ.Adj L x) (hy : y ∈ spanUnion hP L M) (hxy : Γ.dist x y = 2) :
    Γ.neighborSet (commonNeighbor hP hxy) ⊆ spanUnion hP L M := by
  classical
  obtain ⟨y1, y2, hy1L, hy2M, hyS⟩ := hy
  have hLMne : L ≠ M := by
    intro hEq
    rw [hEq, SimpleGraph.dist_self] at hLM
    omega
  by_cases h4 : Γ.dist y1 y2 = 4
  · rw [spanOrLine_of_dist_eq_four hP h4] at hyS
    by_cases hy1 : y = y1
    · rw [show commonNeighbor hP hxy = L from
        (eq_commonNeighbor hP hxy hxL.symm (hy1 ▸ hy1L).symm).symm]
      exact neighborSet_subset_spanUnion_left hP hT c hL hM hLM
    · by_cases hy2 : y = y2
      · rw [← spanOrLine_of_dist_eq_two hP hxy]
        exact spanOrLine_subset_spanUnion hP hxL (hy2 ▸ hy2M)
      · exact neighborSet_commonNeighbor_subset_spanUnion_of_span hP hT c hH hdeg hp
          hL hM hLM hxL hy1L hy2M h4 hyS hy1 hy2 hxy
  · by_cases h2 : Γ.dist y1 y2 = 2
    · rw [spanOrLine_of_dist_eq_two hP h2] at hyS
      let V : V := commonNeighbor hP h2
      have hy1V : Γ.Adj y1 V := commonNeighbor_adj_left hP h2
      have hy2V : Γ.Adj y2 V := commonNeighbor_adj_right hP h2
      by_cases hx1 : x = y1
      · subst x
        have hVeq : commonNeighbor hP hxy = V :=
          (eq_commonNeighbor hP hxy hy1V (by simpa [V] using hyS.symm)).symm
        rw [show commonNeighbor hP hxy = commonNeighbor hP h2 from hVeq]
        rw [← spanOrLine_of_dist_eq_two hP h2]
        exact spanOrLine_subset_spanUnion hP hy1L hy2M
      · by_cases hy1 : y = y1
        · rw [show commonNeighbor hP hxy = L from
            (eq_commonNeighbor hP hxy hxL.symm (hy1 ▸ hy1L).symm).symm]
          exact neighborSet_subset_spanUnion_left hP hT c hL hM hLM
        · by_cases hy2 : y = y2
          · rw [← spanOrLine_of_dist_eq_two hP hxy]
            exact spanOrLine_subset_spanUnion hP hxL (hy2 ▸ hy2M)
          · exfalso
            have hyNotL : ¬ Γ.Adj L y := by
              intro hyL
              have hVL : V = L :=
                eq_of_two_common_points hP (fun h => hy1 h.symm)
                  (commonNeighbor_adj_left hP h2).symm (by simpa [V] using hyS) hy1L hyL
              have hLy2 : Γ.Adj L y2 := (hVL ▸ hy2V).symm
              have h2dist : Γ.dist L M = 2 :=
                dist_eq_two_of_adj_of_adj_of_ne hP hLy2 hy2M.symm hLMne
              omega
            have hxy1 : Γ.dist x y1 = 2 :=
              dist_eq_two_of_adj_of_adj_of_ne hP hxL.symm hy1L hx1
            have hyV' : Γ.Adj y V := (by simpa [V] using hyS : Γ.Adj V y).symm
            have hyy1 : Γ.dist y y1 = 2 :=
              dist_eq_two_of_adj_of_adj_of_ne hP hyV'
                (commonNeighbor_adj_left hP h2).symm hy1
            obtain ⟨W, hW, -⟩ :=
              existsUnique_commonNeighbor_of_pairwise_dist_two hP hxy hxy1 hyy1
            have hWL : W = L :=
              (existsUnique_commonNeighbor hP hxy1).unique
                ⟨hW.1, hW.2.2⟩ ⟨hxL.symm, hy1L.symm⟩
            exact hyNotL (hWL ▸ hW.2.1).symm
    · have hnil : spanOrLine hP y1 y2 = ∅ := by
        rw [spanOrLine, if_neg h4, dif_neg h2]
      rw [hnil] at hyS
      exact hyS.elim

end CFSG.Geometry.GeneralizedQuadrangles
