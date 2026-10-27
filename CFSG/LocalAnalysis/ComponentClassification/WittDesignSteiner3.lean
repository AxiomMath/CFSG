module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneAxioms

public section

namespace CFSG.ComponentClassification.WittDesign

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def IsSteinerTriple (𝓑 : Finset (Finset Ω)) : Prop :=
  Fintype.card Ω = 22 ∧ (∀ B ∈ 𝓑, B.card = 6) ∧
    ∀ T : Finset Ω, T.card = 3 → ∃! B, B ∈ 𝓑 ∧ T ⊆ B

variable {𝓑 : Finset (Finset Ω)}

omit [DecidableEq Ω] in
theorem IsSteinerTriple.card_points (h : IsSteinerTriple 𝓑) : Fintype.card Ω = 22 := h.1

omit [DecidableEq Ω] in
theorem IsSteinerTriple.card_block (h : IsSteinerTriple 𝓑) {B : Finset Ω} (hB : B ∈ 𝓑) :
    B.card = 6 :=
  h.2.1 B hB

@[expose] def derivedLines (𝓑 : Finset (Finset Ω)) (a : Ω) : Finset (Finset {x // x ≠ a}) :=
  (𝓑.filter (a ∈ ·)).image fun B => B.subtype (· ≠ a)

omit [Fintype Ω] in
theorem mem_subtype_ne {B : Finset Ω} {a : Ω} {x : {x // x ≠ a}} :
    x ∈ B.subtype (· ≠ a) ↔ (x : Ω) ∈ B :=
  Finset.mem_subtype

omit [Fintype Ω] in
theorem card_subtype_ne {B : Finset Ω} {a : Ω} (ha : a ∈ B) :
    (B.subtype (· ≠ a)).card = B.card - 1 := by
  rw [Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem ha]

omit [Fintype Ω] in
theorem subtype_ne_injOn (a : Ω) :
    Set.InjOn (fun B : Finset Ω => B.subtype (· ≠ a)) {B | a ∈ B} := by
  intro B hB B' hB' e
  ext x
  by_cases hx : x = a
  · subst hx
    exact ⟨fun _ => hB', fun _ => hB⟩
  · have := congrArg (fun L : Finset {x // x ≠ a} => (⟨x, hx⟩ : {x // x ≠ a}) ∈ L) e
    simpa only [mem_subtype_ne, eq_iff_iff] using this

theorem card_ne_eq (h : Fintype.card Ω = 22) (a : Ω) : Fintype.card {x // x ≠ a} = 21 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, h]

theorem IsSteinerTriple.derived (h : IsSteinerTriple 𝓑) (a : Ω) :
    IsSteinerPlane (derivedLines 𝓑 a) := by
  refine ⟨card_ne_eq h.1 a, ?_, ?_⟩
  · intro L hL
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hL
    rw [Finset.mem_filter] at hB
    rw [card_subtype_ne hB.2, h.card_block hB.1]
  · intro T hT
    set T' : Finset Ω := insert a (T.map (Function.Embedding.subtype _))
    have haT : a ∉ T.map (Function.Embedding.subtype _) := by
      intro ha
      obtain ⟨x, -, hx⟩ := Finset.mem_map.1 ha
      exact x.2 hx
    have hT' : T'.card = 3 := by
      rw [Finset.card_insert_of_notMem haT, Finset.card_map, hT]
    have hsub : ∀ {C : Finset Ω}, T' ⊆ C ↔ a ∈ C ∧ T ⊆ C.subtype (· ≠ a) := by
      intro C
      constructor
      · intro hC
        refine ⟨hC (Finset.mem_insert_self _ _), fun x hx => mem_subtype_ne.2 (hC ?_)⟩
        exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hx)
      · rintro ⟨haC, hTC⟩ y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact haC
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
          exact mem_subtype_ne.1 (hTC hx)
    obtain ⟨B, ⟨hB, hTB⟩, hu⟩ := h.2.2 T' hT'
    obtain ⟨haB, hTB'⟩ := hsub.1 hTB
    refine ⟨B.subtype (· ≠ a), ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hB, haB⟩),
      hTB'⟩, ?_⟩
    rintro L ⟨hL, hTL⟩
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hL
    rw [Finset.mem_filter] at hC
    rw [hu C ⟨hC.1, hsub.2 ⟨hC.2, hTL⟩⟩]

theorem IsSteinerTriple.card_inter_le (h : IsSteinerTriple 𝓑) {B B' : Finset Ω} (hB : B ∈ 𝓑)
    (hB' : B' ∈ 𝓑) (hne : B ≠ B') : (B ∩ B').card ≤ 2 := by
  by_contra hc
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (show 3 ≤ (B ∩ B').card by omega)
  obtain ⟨C, -, hu⟩ := h.2.2 T hcard
  exact hne ((hu B ⟨hB, hT.trans Finset.inter_subset_left⟩).trans
    (hu B' ⟨hB', hT.trans Finset.inter_subset_right⟩).symm)

theorem IsSteinerTriple.card_inter_ne_one (h : IsSteinerTriple 𝓑) {B B' : Finset Ω}
    (hB : B ∈ 𝓑) (hB' : B' ∈ 𝓑) : (B ∩ B').card ≠ 1 := by
  intro h1
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
  have hxB : x ∈ B ∩ B' := hx ▸ Finset.mem_singleton_self x
  rw [Finset.mem_inter] at hxB
  have hL : B.subtype (· ≠ x) ∈ derivedLines 𝓑 x :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hB, hxB.1⟩)
  have hL' : B'.subtype (· ≠ x) ∈ derivedLines 𝓑 x :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hB', hxB.2⟩)
  obtain ⟨y, hy, hy'⟩ := (h.derived x).exists_mem_inter hL hL'
  have hyB : (y : Ω) ∈ B ∩ B' := Finset.mem_inter.2 ⟨mem_subtype_ne.1 hy, mem_subtype_ne.1 hy'⟩
  rw [hx, Finset.mem_singleton] at hyB
  exact y.2 hyB

theorem IsSteinerTriple.card_inter (h : IsSteinerTriple 𝓑) {B B' : Finset Ω} (hB : B ∈ 𝓑)
    (hB' : B' ∈ 𝓑) (hne : B ≠ B') : (B ∩ B').card = 0 ∨ (B ∩ B').card = 2 := by
  have h1 := h.card_inter_le hB hB' hne
  have h2 := h.card_inter_ne_one hB hB'
  omega

theorem IsSteinerTriple.card_blocks_mem (h : IsSteinerTriple 𝓑) (a : Ω) :
    (𝓑.filter (a ∈ ·)).card = 21 := by
  rw [← (h.derived a).card_lines, derivedLines, Finset.card_image_of_injOn]
  intro B hB B' hB' e
  exact subtype_ne_injOn a (Finset.mem_filter.1 hB).2 (Finset.mem_filter.1 hB').2 e

theorem IsSteinerTriple.card_blocks (h : IsSteinerTriple 𝓑) : 𝓑.card = 77 := by
  have hcount : ∑ B ∈ 𝓑, B.card = ∑ a : Ω, (𝓑.filter (a ∈ ·)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_congr rfl fun B hB => h.card_block hB,
    Finset.sum_congr rfl fun a _ => h.card_blocks_mem a, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, h.card_points, smul_eq_mul, smul_eq_mul] at hcount
  omega

theorem IsSteinerTriple.card_blocks_not_mem (h : IsSteinerTriple 𝓑) (a : Ω) :
    (𝓑.filter (a ∉ ·)).card = 56 := by
  have := Finset.card_filter_add_card_filter_not (s := 𝓑) (p := (a ∈ ·))
  rw [h.card_blocks_mem a, h.card_blocks] at this
  omega

end CFSG.ComponentClassification.WittDesign
