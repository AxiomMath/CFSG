module

public import CFSG.GF2Type.Smith1979W3.Cert690.Tab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

@[expose] noncomputable def spanOfList (S : List ℕ) : Submodule (ZMod 2) V₀ :=
  Submodule.span (ZMod 2) (Code.vec '' {x : ℕ | x ∈ S})

theorem spanOfList_nil : spanOfList [] = ⊥ := by
  simp [spanOfList]

theorem spanOfList_cons (x : ℕ) (S : List ℕ) :
    spanOfList (x :: S) = Submodule.span (ZMod 2) {Code.vec x} ⊔ spanOfList S := by
  unfold spanOfList
  rw [show Code.vec '' {y : ℕ | y ∈ x :: S} =
      insert (Code.vec x) (Code.vec '' {y : ℕ | y ∈ S}) by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff]
    constructor
    · rintro ⟨y, rfl | hy, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hy, rfl⟩
    · rintro (rfl | ⟨y, hy, rfl⟩)
      · exact ⟨x, Or.inl rfl, rfl⟩
      · exact ⟨y, Or.inr hy, rfl⟩]
  rw [Submodule.span_insert]

@[expose] def spanStep (B : Array ℕ) (x : ℕ) : Array ℕ :=
  if B.contains x then B else B ++ B.map (fun y => y ^^^ x)

theorem spanArr_eq_foldl (S : List ℕ) : spanArr S = S.foldl spanStep #[0] := by
  unfold spanArr spanStep
  simp only [Array.contains_eq_mem]

theorem spanStep_represents {B : Array ℕ} {W : Submodule (ZMod 2) V₀}
    (h1 : ∀ b ∈ B.toList, Code.vec b ∈ W)
    (h2 : ∀ w ∈ W, ∃ b ∈ B.toList, Code.vec b = w) (x : ℕ) :
    (∀ b ∈ (spanStep B x).toList, Code.vec b ∈ W ⊔ Submodule.span (ZMod 2) {Code.vec x}) ∧
    (∀ w ∈ W ⊔ Submodule.span (ZMod 2) {Code.vec x},
      ∃ b ∈ (spanStep B x).toList, Code.vec b = w) := by
  by_cases hx : B.contains x
  · have hxmem : x ∈ B.toList := Array.mem_toList_iff.mpr (Array.contains_iff_mem.mp hx)
    have hxW : Code.vec x ∈ W := h1 x hxmem
    have hsup : W ⊔ Submodule.span (ZMod 2) {Code.vec x} = W :=
      sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using hxW))
    rw [spanStep, if_pos hx, hsup]
    exact ⟨h1, h2⟩
  · rw [spanStep, if_neg hx]
    constructor
    · intro b hb
      rw [Array.toList_append, Array.toList_map] at hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Submodule.mem_sup_left (h1 b hb)
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        rw [vec_xor]
        exact Submodule.add_mem_sup (h1 y hy) (Submodule.subset_span (by simp))
    · intro w hw
      rw [Submodule.mem_sup] at hw
      obtain ⟨a, ha, c, hc, rfl⟩ := hw
      rw [Submodule.mem_span_singleton] at hc
      obtain ⟨k, hk⟩ := hc
      rcases zmod2_eq_zero_or_eq_one k with rfl | rfl
      · rw [zero_smul] at hk
        subst hk
        simp only [add_zero]
        obtain ⟨b, hb, rfl⟩ := h2 a ha
        exact ⟨b, by rw [Array.toList_append]; exact List.mem_append_left _ hb, rfl⟩
      · rw [one_smul] at hk
        subst hk
        obtain ⟨b, hb, rfl⟩ := h2 a ha
        refine ⟨b ^^^ x, ?_, ?_⟩
        · rw [Array.toList_append, Array.toList_map]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
        · rw [vec_xor]

theorem foldl_spanStep_represents (S : List ℕ) :
    ∀ (B : Array ℕ) (W : Submodule (ZMod 2) V₀),
      (∀ b ∈ B.toList, Code.vec b ∈ W) →
      (∀ w ∈ W, ∃ b ∈ B.toList, Code.vec b = w) →
      (∀ b ∈ (S.foldl spanStep B).toList, Code.vec b ∈ W ⊔ spanOfList S) ∧
      (∀ w ∈ W ⊔ spanOfList S,
        ∃ b ∈ (S.foldl spanStep B).toList, Code.vec b = w) := by
  induction S with
  | nil =>
    intro B W h1 h2
    simp only [List.foldl, spanOfList_nil, sup_bot_eq]
    exact ⟨h1, h2⟩
  | cons x S ih =>
    intro B W h1 h2
    have hx := spanStep_represents h1 h2 x
    have hIH := ih (spanStep B x) (W ⊔ Submodule.span (ZMod 2) {Code.vec x}) hx.1 hx.2
    rw [List.foldl_cons, spanOfList_cons, ← sup_assoc]
    exact hIH

theorem spanArr_represents (S : List ℕ) :
    (∀ b ∈ (spanArr S).toList, Code.vec b ∈ spanOfList S) ∧
    (∀ v ∈ spanOfList S, ∃ b ∈ (spanArr S).toList, Code.vec b = v) := by
  have h := foldl_spanStep_represents S #[0] ⊥
    (by
      intro b hb
      have hb0 : b = 0 := by simpa using hb
      subst hb0
      rw [vec_zero]
      exact Submodule.zero_mem _)
    (by intro w hw; rw [Submodule.mem_bot] at hw; subst hw; exact ⟨0, by simp, vec_zero⟩)
  rw [spanArr_eq_foldl]
  simpa using h

theorem spanOfList_spanArr (S : List ℕ) : spanOfList (spanArr S).toList = spanOfList S := by
  refine le_antisymm ?_ ?_
  · rw [spanOfList, Submodule.span_le]
    rintro v ⟨b, hb, rfl⟩
    exact (spanArr_represents S).1 b hb
  · rw [spanOfList, Submodule.span_le]
    rintro v ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hvc⟩ := (spanArr_represents S).2 (Code.vec b)
      (Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← hvc]
    exact Submodule.subset_span ⟨c, hc, rfl⟩

theorem spanOfList_eq_of_mem_iff {S T : List ℕ}
    (h : ∀ x, x ∈ S ↔ x ∈ T) : spanOfList S = spanOfList T := by
  unfold spanOfList
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (h x).mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (h x).mpr hx, rfl⟩

theorem spanArr_vPlus : spanArr [2, 4, 32] = vPlusVecs.toArray := by decide +kernel

theorem spanArr_vStar : spanArr [1, 8, 16] = vStarVecs.toArray := by decide +kernel

theorem spanOfList_vPlus_eq : spanOfList vPlusVecs = spanOfList [2, 4, 32] := by
  rw [show spanOfList vPlusVecs = spanOfList (spanArr [2, 4, 32]).toList by
    simp [spanArr_vPlus]]
  rw [spanOfList_spanArr]

theorem spanOfList_vPlus : spanOfList vPlusVecs = VPlus := by
  rw [spanOfList_vPlus_eq]
  have hset : Code.vec '' {x : ℕ | x ∈ [2, 4, 32]} =
      ({Code.vec 2, Code.vec 4, Code.vec 32} : Set V₀) := by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl, rfl⟩ <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨2, Or.inl rfl, rfl⟩
      · exact ⟨4, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨32, Or.inr (Or.inr rfl), rfl⟩
  unfold spanOfList VPlus
  rw [hset]

theorem spanOfList_vStar_eq : spanOfList vStarVecs = spanOfList [1, 8, 16] := by
  rw [show spanOfList vStarVecs = spanOfList (spanArr [1, 8, 16]).toList by
    simp [spanArr_vStar]]
  rw [spanOfList_spanArr]

theorem spanOfList_vStar : spanOfList vStarVecs = VStar := by
  rw [spanOfList_vStar_eq]
  have hset : Code.vec '' {x : ℕ | x ∈ [1, 8, 16]} =
      ({Code.vec 1, Code.vec 8, Code.vec 16} : Set V₀) := by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl | rfl, rfl⟩ <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, Or.inl rfl, rfl⟩
      · exact ⟨8, Or.inr (Or.inl rfl), rfl⟩
      · exact ⟨16, Or.inr (Or.inr rfl), rfl⟩
  unfold spanOfList VStar
  rw [hset]

theorem mem_VPlus_iff {v : V₀} : v ∈ VPlus ↔ ∃ n ∈ vPlusVecs, Code.vec n = v := by
  rw [← spanOfList_vPlus, spanOfList_vPlus_eq]
  constructor
  · intro hv
    obtain ⟨n, hn, hnv⟩ := (spanArr_represents [2, 4, 32]).2 v hv
    rw [spanArr_vPlus] at hn
    exact ⟨n, by simpa using hn, hnv⟩
  · rintro ⟨n, hn, rfl⟩
    exact (spanArr_represents [2, 4, 32]).1 n (by simpa [spanArr_vPlus] using hn)

theorem mem_VStar_iff {v : V₀} : v ∈ VStar ↔ ∃ n ∈ vStarVecs, Code.vec n = v := by
  rw [← spanOfList_vStar, spanOfList_vStar_eq]
  constructor
  · intro hv
    obtain ⟨n, hn, hnv⟩ := (spanArr_represents [1, 8, 16]).2 v hv
    rw [spanArr_vStar] at hn
    exact ⟨n, by simpa using hn, hnv⟩
  · rintro ⟨n, hn, rfl⟩
    exact (spanArr_represents [1, 8, 16]).1 n (by simpa [spanArr_vStar] using hn)

end CFSG.GF2Type.Smith1979W3.Cert690
