module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourRep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.Alt7KleinHyp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7FourNorm

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv Perm CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

namespace Alt7K

@[expose] def a0 : Perm (Fin 7) := swap 0 1 * swap 2 3

@[expose] def evenP : Finset (Perm (Fin 7)) := Finset.univ.filter (fun g => sign g = 1)

@[expose] def C0 : Finset (Perm (Fin 7)) :=
  evenP.filter (fun b => b * a0 = a0 * b ∧ b * b = 1 ∧ b ≠ 1 ∧ b ≠ a0)

@[expose] def Rset (b : Perm (Fin 7)) : Finset (Perm (Fin 7)) := {1, a0, b, a0 * b}

@[expose] def CA : Finset (Perm (Fin 7)) := evenP.filter (fun g => g * a0 = a0 * g)

@[expose] def cnt (b : Perm (Fin 7)) : ℕ :=
  (CA.filter (fun g => ∀ x ∈ Rset b, g * x * g⁻¹ ∈ Rset b)).card

@[expose] def g1 : Perm (Fin 7) := swap 0 2 * swap 1 3

@[expose] def g2 : Perm (Fin 7) := swap 0 3 * swap 1 2

private def CALw : List (List (Fin 7 × Fin 7)) :=
  [[], [(5, 6)], [(4, 5)], [(4, 5), (5, 6)],
    [(4, 6), (5, 6)], [(4, 6)], [(2, 3)], [(2, 3), (5, 6)],
    [(2, 3), (4, 5)], [(2, 3), (4, 5), (5, 6)], [(2, 3), (4, 6), (5, 6)], [(2, 3), (4, 6)],
    [(0, 1)], [(0, 1), (5, 6)], [(0, 1), (4, 5)], [(0, 1), (4, 5), (5, 6)],
    [(0, 1), (4, 6), (5, 6)], [(0, 1), (4, 6)], [(0, 1), (2, 3)], [(0, 1), (2, 3), (5, 6)],
    [(0, 1), (2, 3), (4, 5)], [(0, 1), (2, 3), (4, 5), (5, 6)], [(0, 1), (2, 3), (4, 6), (5, 6)], [(0, 1), (2, 3), (4, 6)],
    [(0, 2), (1, 3)], [(0, 2), (1, 3), (5, 6)], [(0, 2), (1, 3), (4, 5)], [(0, 2), (1, 3), (4, 5), (5, 6)],
    [(0, 2), (1, 3), (4, 6), (5, 6)], [(0, 2), (1, 3), (4, 6)], [(0, 2), (1, 3), (2, 3)], [(0, 2), (1, 3), (2, 3), (5, 6)],
    [(0, 2), (1, 3), (2, 3), (4, 5)], [(0, 2), (1, 3), (2, 3), (4, 5), (5, 6)], [(0, 2), (1, 3), (2, 3), (4, 6), (5, 6)], [(0, 2), (1, 3), (2, 3), (4, 6)],
    [(0, 3), (1, 2), (2, 3)], [(0, 3), (1, 2), (2, 3), (5, 6)], [(0, 3), (1, 2), (2, 3), (4, 5)], [(0, 3), (1, 2), (2, 3), (4, 5), (5, 6)],
    [(0, 3), (1, 2), (2, 3), (4, 6), (5, 6)], [(0, 3), (1, 2), (2, 3), (4, 6)], [(0, 3), (1, 2)], [(0, 3), (1, 2), (5, 6)],
    [(0, 3), (1, 2), (4, 5)], [(0, 3), (1, 2), (4, 5), (5, 6)], [(0, 3), (1, 2), (4, 6), (5, 6)], [(0, 3), (1, 2), (4, 6)]]

private def CAL : List (Perm (Fin 7)) :=
  CALw.map fun w => (w.map fun p : Fin 7 × Fin 7 => swap p.1 p.2).prod

private def permEqB (σ τ : Perm (Fin 7)) : Bool := (List.finRange 7).all fun i => decide (σ i = τ i)

private lemma permEqB_iff {σ τ : Perm (Fin 7)} : permEqB σ τ = true ↔ σ = τ := by
  simp only [permEqB, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  exact ⟨fun h => Equiv.ext h, fun h i => h ▸ rfl⟩

private lemma permNeB_iff {σ τ : Perm (Fin 7)} : (!permEqB σ τ) = true ↔ σ ≠ τ := by
  rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, permEqB_iff]

set_option maxRecDepth 100000 in
private lemma CAL_commB : CAL.all (fun c => permEqB (c * a0) (a0 * c)) = true := by
  decide +kernel

private lemma CAL_comm : ∀ c ∈ CAL, c * a0 = a0 * c := fun c hc =>
  permEqB_iff.1 (List.all_eq_true.1 CAL_commB c hc)

private def TupleP (p q r s t : Fin 7) : Prop :=
  a0 r = r → a0 s = s → a0 t = t → [p, a0 p, q, a0 q, r, s, t].Nodup →
    ∃ c ∈ CAL, c 0 = p ∧ c 2 = q ∧ c 4 = r ∧ c 5 = s ∧ c 6 = t

private instance (p q r s t : Fin 7) : Decidable (TupleP p q r s t) := by
  unfold TupleP
  infer_instance

set_option maxRecDepth 100000 in
private lemma tuple_cover : ∀ p q r s t : Fin 7, TupleP p q r s t := by
  decide +kernel

private lemma comm_apply {g : Perm (Fin 7)} (h : g * a0 = a0 * g) (i : Fin 7) :
    g (a0 i) = a0 (g i) := by
  have := congrArg (fun p : Perm (Fin 7) => p i) h
  simpa only [Perm.mul_apply] using this

private lemma mem_CAL_of_comm {g : Perm (Fin 7)} (h : g * a0 = a0 * g) : g ∈ CAL := by
  have e0 : a0 0 = 1 := by decide
  have e2 : a0 2 = 3 := by decide
  have e4 : a0 4 = 4 := by decide
  have e5 : a0 5 = 5 := by decide
  have e6 : a0 6 = 6 := by decide
  have g1' : g 1 = a0 (g 0) := by rw [← comm_apply h, e0]
  have g3' : g 3 = a0 (g 2) := by rw [← comm_apply h, e2]
  have f4 : a0 (g 4) = g 4 := by rw [← comm_apply h, e4]
  have f5 : a0 (g 5) = g 5 := by rw [← comm_apply h, e5]
  have f6 : a0 (g 6) = g 6 := by rw [← comm_apply h, e6]
  have hnd : [g 0, a0 (g 0), g 2, a0 (g 2), g 4, g 5, g 6].Nodup := by
    rw [← g1', ← g3']
    have hl : [g 0, g 1, g 2, g 3, g 4, g 5, g 6] =
        ([0, 1, 2, 3, 4, 5, 6] : List (Fin 7)).map g := rfl
    rw [hl]
    exact (List.nodup_map_iff g.injective).2 (by decide)
  obtain ⟨c, hc, h0, h2, h4, h5, h6⟩ := tuple_cover _ _ _ _ _ f4 f5 f6 hnd
  have hcc := CAL_comm c hc
  have c1 : c 1 = a0 (c 0) := by rw [← comm_apply hcc, e0]
  have c3 : c 3 = a0 (c 2) := by rw [← comm_apply hcc, e2]
  have hgc : g = c := by
    ext i
    have key : ∀ j : Fin 7, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by decide
    rcases key i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0]
    · rw [g1', c1, h0]
    · rw [h2]
    · rw [g3', c3, h2]
    · rw [h4]
    · rw [h5]
    · rw [h6]
  exact hgc ▸ hc

private def CAe : List (Perm (Fin 7)) := CAL.filter fun g => decide (sign g = 1)

private def C0e : List (Perm (Fin 7)) :=
  CAe.filter fun b => permEqB (b * b) 1 && (!permEqB b 1 && !permEqB b a0)

private lemma CA_eq : CA = CAe.toFinset := by
  ext g
  simp only [CA, CAe, evenP, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hc⟩
    exact ⟨mem_CAL_of_comm hc, hs⟩
  · rintro ⟨hm, hs⟩
    exact ⟨hs, CAL_comm g hm⟩

private lemma C0_eq : C0 = C0e.toFinset := by
  ext b
  simp only [C0, C0e, CAe, evenP, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Bool.and_eq_true, permEqB_iff,
    permNeB_iff]
  constructor
  · rintro ⟨hs, hc, h2, h3, h4⟩
    exact ⟨⟨mem_CAL_of_comm hc, hs⟩, h2, h3, h4⟩
  · rintro ⟨⟨hm, hs⟩, h2, h3, h4⟩
    exact ⟨hs, CAL_comm b hm, h2, h3, h4⟩

private def RL (b : Perm (Fin 7)) : List (Perm (Fin 7)) := [1, a0, b, a0 * b]

private def normB (b g : Perm (Fin 7)) : Bool :=
  (RL b).all fun x => (RL b).any fun y => permEqB (g * x * g⁻¹) y

private lemma mem_Rset_iff (b x : Perm (Fin 7)) : x ∈ Rset b ↔ x ∈ RL b := by
  simp only [Rset, RL, Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.mem_nil_iff,
    or_false]

private lemma normB_iff (b g : Perm (Fin 7)) :
    normB b g = true ↔ ∀ x ∈ Rset b, g * x * g⁻¹ ∈ Rset b := by
  simp only [normB, List.all_eq_true, List.any_eq_true, permEqB_iff, mem_Rset_iff]
  exact ⟨fun h x hx => by obtain ⟨y, hy, e⟩ := h x hx; exact e ▸ hy,
    fun h x hx => ⟨_, h x hx, rfl⟩⟩

set_option maxRecDepth 100000 in
private lemma bad_count_B : C0e.all (fun b => permEqB b g1 || permEqB b g2 ||
    decide ((CAe.filter (normB b)).length ≤ 23)) = true := by
  decide +kernel

theorem bad_count : ∀ b ∈ C0, b ≠ g1 → b ≠ g2 → cnt b ≤ 23 := by
  rw [C0_eq]
  intro b hb h1 h2
  have hB := List.all_eq_true.1 bad_count_B b (List.mem_toFinset.1 hb)
  simp only [Bool.or_eq_true, permEqB_iff, h1, h2, false_or, decide_eq_true_eq] at hB
  unfold cnt
  rw [CA_eq]
  have hsub : CAe.toFinset.filter (fun g => ∀ x ∈ Rset b, g * x * g⁻¹ ∈ Rset b) ⊆
      (CAe.filter (normB b)).toFinset := by
    intro g hg
    simp only [Finset.mem_filter, List.mem_toFinset] at hg
    simp only [List.mem_toFinset, List.mem_filter]
    exact ⟨hg.1, (normB_iff b g).2 hg.2⟩
  exact ((Finset.card_le_card hsub).trans (List.toFinset_card_le _)).trans hB

theorem Rset_g : Rset g1 = Rset g2 := by decide +kernel

theorem a0_mem : a0 ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem a0_sq : a0 * a0 = 1 := by decide +kernel

theorem a0_ne_one : a0 ≠ 1 := by decide +kernel

@[expose] def a0' : alternatingGroup (Fin 7) := ⟨a0, a0_mem⟩

theorem a0'_sq : a0' ^ 2 = 1 := Subtype.ext (by simpa [a0', pow_two] using a0_sq)

theorem a0'_ne_one : a0' ≠ 1 := fun h => a0_ne_one (congrArg Subtype.val h)

variable {R : Subgroup (alternatingGroup (Fin 7))}

theorem comm_of_sq (hR2 : ∀ a ∈ R, a ^ 2 = 1) {a b : alternatingGroup (Fin 7)} (ha : a ∈ R)
    (hb : b ∈ R) : a * b = b * a := by
  have h1 := hR2 _ (R.mul_mem ha hb)
  have h2 := hR2 a ha
  have h3 := hR2 b hb
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h2)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h3)
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h1)).symm
  rw [this, mul_inv_rev, ha', hb']

theorem mem_iff_of_klein (h4 : Nat.card R = 4) (hR2 : ∀ a ∈ R, a ^ 2 = 1)
    (hN : 72 ≤ Nat.card (Subgroup.normalizer (R : Set (alternatingGroup (Fin 7)))))
    (ha0 : a0' ∈ R) : ∀ y : alternatingGroup (Fin 7), y ∈ R ↔ (y : Perm (Fin 7)) ∈ Rset g1 := by
  classical
  obtain ⟨b₁, hb₁R, hb₁1, hb₁a⟩ : ∃ b₁ ∈ R, b₁ ≠ 1 ∧ b₁ ≠ a0' := by
    by_contra hno
    push Not at hno
    have hsub : (R : Set (alternatingGroup (Fin 7))) ⊆ {1, a0'} := by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      · simp [hno x hx h1]
    have hle : Nat.card R ≤ 2 := by
      have e : Nat.card R = (R : Set (alternatingGroup (Fin 7))).ncard :=
        Nat.card_coe_set_eq (R : Set (alternatingGroup (Fin 7)))
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({1, a0'} : Set (alternatingGroup (Fin 7))).ncard ≤ 2 := (Set.ncard_insert_le 1 {a0'}).trans (by simp)
      omega
    omega
  have hcomm := fun {a b} (ha : a ∈ R) (hb : b ∈ R) => comm_of_sq hR2 ha hb
  have ha0inv : a0'⁻¹ = a0' := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact a0'_sq)
  have hb2 := hR2 b₁ hb₁R
  have hbinv : b₁⁻¹ = b₁ := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
  have n1 : a0' * b₁ ≠ 1 := fun h => hb₁a (by
    have := eq_inv_of_mul_eq_one_right h
    rw [this, ha0inv])
  have n2 : a0' * b₁ ≠ a0' := fun h => hb₁1 (by simpa using h)
  have n3 : a0' * b₁ ≠ b₁ := fun h => a0'_ne_one (by simpa using h)
  have hSR : ({1, a0', b₁, a0' * b₁} : Set (alternatingGroup (Fin 7))) ⊆ R := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact R.one_mem
    · exact ha0
    · exact hb₁R
    · exact R.mul_mem ha0 hb₁R
  have hS4 : ({1, a0', b₁, a0' * b₁} : Set (alternatingGroup (Fin 7))).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_singleton]
    · simp only [Set.mem_singleton_iff]; exact fun h => n3 h.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hb₁a h.symm, fun h => n2 h.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => a0'_ne_one h.symm, fun h => hb₁1 h.symm, fun h => n1 h.symm⟩
  have hSeq : ({1, a0', b₁, a0' * b₁} : Set (alternatingGroup (Fin 7))) = (R : Set _) := by
    refine Set.eq_of_subset_of_ncard_le hSR ?_ (Set.toFinite _)
    have e : Nat.card R = (R : Set (alternatingGroup (Fin 7))).ncard :=
      Nat.card_coe_set_eq (R : Set (alternatingGroup (Fin 7)))
    omega
  have hmemS : ∀ y : alternatingGroup (Fin 7), y ∈ R ↔ y = 1 ∨ y = a0' ∨ y = b₁ ∨ y = a0' * b₁ := by
    intro y
    have := Set.ext_iff.1 hSeq y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe] at this
    exact this.symm
  set b : Perm (Fin 7) := (b₁ : Perm (Fin 7)) with hb
  have hbC : b ∈ C0 := by
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact Perm.mem_alternatingGroup.mp b₁.2
    · have := congrArg Subtype.val (hcomm hb₁R ha0)
      exact this
    · have := congrArg Subtype.val hb2
      simpa [pow_two] using this
    · exact fun h => hb₁1 (Subtype.ext h)
    · exact fun h => hb₁a (Subtype.ext h)
  have hiff : ∀ y : alternatingGroup (Fin 7), y ∈ R ↔ (y : Perm (Fin 7)) ∈ Rset b := by
    intro y
    rw [hmemS]
    simp only [Rset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (h | h | h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  have hbg : Rset b = Rset g1 := by
    by_cases hb1 : b = g1
    · rw [hb1]
    by_cases hb2 : b = g2
    · rw [hb2, Rset_g]
    exfalso
    have hcnt := bad_count b hbC hb1 hb2
    set N := Subgroup.normalizer (R : Set (alternatingGroup (Fin 7))) with hNdef
    have hmul := card_eq_orbit_mul N a0'
    have horb : Set.ncard {x : alternatingGroup (Fin 7) | ∃ k ∈ N, x = k * a0' * k⁻¹} ≤ 3 := by
      have hsub : {x : alternatingGroup (Fin 7) | ∃ k ∈ N, x = k * a0' * k⁻¹} ⊆
          (R : Set (alternatingGroup (Fin 7))) \ {1} := by
        rintro _ ⟨k, hk, rfl⟩
        refine ⟨(Subgroup.mem_normalizer_iff.1 hk a0').1 ha0, fun h => a0'_ne_one ?_⟩
        have : k * a0' * k⁻¹ = 1 := h
        simpa using this
      have h3 : ((R : Set (alternatingGroup (Fin 7))) \ {1}).ncard = 3 := by
        have e : (R : Set (alternatingGroup (Fin 7))).ncard = 4 := by
          rw [← Nat.card_coe_set_eq]; exact h4
        rw [Set.ncard_sdiff_singleton_of_mem R.one_mem, e]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h3.le
    have hst : Nat.card ↥(N ⊓ Subgroup.centralizer {a0'}) ≤ cnt b := by
      set F := CA.filter (fun g => ∀ x ∈ Rset b, g * x * g⁻¹ ∈ Rset b) with hF
      have key : ∀ g ∈ N ⊓ Subgroup.centralizer ({a0'} : Set (alternatingGroup (Fin 7))),
          (g : Perm (Fin 7)) ∈ F := by
        intro g hg
        obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.1 hg
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_filter.2
          ⟨Finset.mem_univ _, Perm.mem_alternatingGroup.mp g.2⟩, ?_⟩, ?_⟩
        · have := Subgroup.mem_centralizer_iff.1 hgC a0' (Set.mem_singleton _)
          have := congrArg Subtype.val this
          exact this.symm
        · have hc : ∀ y ∈ R, (g : Perm (Fin 7)) * (y : Perm (Fin 7)) * (g : Perm (Fin 7))⁻¹ ∈ Rset b :=
            fun y hy => (hiff _).1 ((Subgroup.mem_normalizer_iff.1 hgN y).1 hy)
          intro x hx
          simp only [Rset, Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · simpa using hc 1 R.one_mem
          · exact hc a0' ha0
          · exact hc b₁ hb₁R
          · have := hc (a0' * b₁) (R.mul_mem ha0 hb₁R)
            simpa [a0'] using this
      calc Nat.card ↥(N ⊓ Subgroup.centralizer {a0'})
          ≤ Nat.card (↥(F : Set (Perm (Fin 7)))) :=
            Nat.card_le_card_of_injective
              (fun g => ⟨(g.1 : Perm (Fin 7)), key g.1 g.2⟩)
              (fun g g' h => by
                have h' : ((g.1 : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
                    ((g'.1 : alternatingGroup (Fin 7)) : Perm (Fin 7)) :=
                  congrArg (fun z : ↥(F : Set (Perm (Fin 7))) => (z : Perm (Fin 7))) h
                exact Subtype.ext (Subtype.ext h'))
        _ = F.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    rw [hmul] at hN
    have h69 := Nat.mul_le_mul horb (hst.trans hcnt)
    have := hN.trans h69
    norm_num at this
  intro y
  rw [hiff, hbg]

theorem card_le_eight {D : Subgroup (alternatingGroup (Fin 7))} (hD : IsPGroup 2 D) :
    Nat.card D ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  have hdvd : Nat.card D ∣ 2520 := card_alt7 ▸ Subgroup.card_subgroup_dvd_card D
  rw [hn] at hdvd ⊢
  by_contra hlt
  have hn4 : 4 ≤ n := by
    by_contra h
    have : n ≤ 3 := by omega
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 hn4
  have := h16.trans hdvd
  norm_num at this

end Alt7K

open Alt7K in
theorem klein_unique_alt7 {D R R' : Subgroup (alternatingGroup (Fin 7))} (hD : IsPGroup 2 D)
    (hRD : R ≤ D) (hR'D : R' ≤ D) (h4 : Nat.card R = 4) (h4' : Nat.card R' = 4)
    (h2 : ∀ a ∈ R, a ^ 2 = 1) (h2' : ∀ a ∈ R', a ^ 2 = 1)
    (hN : 72 ≤ Nat.card (Subgroup.normalizer (R : Set (alternatingGroup (Fin 7)))))
    (hN' : 72 ≤ Nat.card (Subgroup.normalizer (R' : Set (alternatingGroup (Fin 7))))) :
    R = R' := by
  classical
  have hD8 := card_le_eight hD
  obtain ⟨a, haR, haR', ha1⟩ : ∃ a, a ∈ R ∧ a ∈ R' ∧ a ≠ 1 := by
    by_contra hno
    push Not at hno
    have hinj : Function.Injective (fun p : R × R' =>
        (⟨(p.1 : alternatingGroup (Fin 7)) * p.2, D.mul_mem (hRD p.1.2) (hR'D p.2.2)⟩ : D)) := by
      intro p q h
      have h1 : (p.1 : alternatingGroup (Fin 7)) * p.2 = q.1 * q.2 := congrArg Subtype.val h
      have h3 : (q.1 : alternatingGroup (Fin 7))⁻¹ * p.1 = q.2 * (p.2 : alternatingGroup (Fin 7))⁻¹ := by
        have : (q.1 : alternatingGroup (Fin 7))⁻¹ * (p.1 * p.2) = q.2 := by
          rw [h1]; group
        calc (q.1 : alternatingGroup (Fin 7))⁻¹ * p.1
            = (q.1 : alternatingGroup (Fin 7))⁻¹ * (p.1 * p.2) * (p.2 : alternatingGroup (Fin 7))⁻¹ := by
              group
          _ = q.2 * (p.2 : alternatingGroup (Fin 7))⁻¹ := by rw [this]
      have hx : (q.1 : alternatingGroup (Fin 7))⁻¹ * p.1 = 1 :=
        hno _ (R.mul_mem (R.inv_mem q.1.2) p.1.2) (h3 ▸ R'.mul_mem q.2.2 (R'.inv_mem p.2.2))
      have hq : (p.1 : alternatingGroup (Fin 7)) = q.1 := by
        have := congrArg (fun z => (q.1 : alternatingGroup (Fin 7)) * z) hx
        simpa using this
      have hp : (p.2 : alternatingGroup (Fin 7)) = q.2 := by
        rw [hq] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext hq) (Subtype.ext hp)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, h4, h4'] at this
    omega
  obtain ⟨c, hc⟩ := isConj_iff.1 (alt7_involutions_conj ha1 (h2 a haR) a0'_ne_one a0'_sq)
  let e : alternatingGroup (Fin 7) ≃* alternatingGroup (Fin 7) := MulAut.conj c
  have hmap : ∀ (S : Subgroup (alternatingGroup (Fin 7))), Nat.card S = 4 → (∀ a ∈ S, a ^ 2 = 1) →
      72 ≤ Nat.card (Subgroup.normalizer (S : Set (alternatingGroup (Fin 7)))) → a ∈ S →
      ∀ y : alternatingGroup (Fin 7), y ∈ S.map e.toMonoidHom ↔ (y : Perm (Fin 7)) ∈ Rset g1 := by
    intro S hS4 hS2 hSN haS
    refine mem_iff_of_klein (R := S.map e.toMonoidHom) ?_ ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective e.injective, hS4]
    · rintro _ ⟨y, hy, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, hS2 y hy, map_one]
    · exact hSN.trans (card_normalizer_map_ge e S)
    · exact ⟨a, haS, by simpa [e, MulAut.conj_apply] using hc⟩
  have h1 := hmap R h4 h2 hN haR
  have h1' := hmap R' h4' h2' hN' haR'
  have heq : R.map e.toMonoidHom = R'.map e.toMonoidHom := by
    ext y
    rw [h1, h1']
  exact Subgroup.map_injective e.injective heq

theorem alt7Hyp : Alt7Hyp (alternatingGroup (Fin 7)) where
  card_le R _ h2 := alt7_elemAbelian_card_le h2
  conj a b ha1 ha2 hb1 hb2 := alt7_involutions_conj ha1 ha2 hb1 hb2
  order5 := alt7_exists_order_five_product
  card_inv := alt7_card_involutions
  card_G := card_alt7
  klein R hR _ hs h72 := alt7_klein_normalizer hR hs h72
  klein_unique hD hRD hR'D h4 h4' h2 h2' hN hN' :=
    klein_unique_alt7 hD hRD hR'D h4 h4' h2 h2' hN hN'

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
