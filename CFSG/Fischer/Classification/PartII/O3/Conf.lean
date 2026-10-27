module

public import CFSG.Fischer.Classification.PartII.O3.PlaneType
public import CFSG.Fischer.Classification.PartII.O3.PlaneCoord
public import CFSG.Fischer.Classification.PartII.O3Endgame

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

section Bridge

variable (hP : Pair X E) {d e z : X} (hd : d ∈ E) (he : e ∈ E) (hz : z ∈ E)
  (hde : d * e ≠ e * d) (hdz : d * z ≠ z * d) (hez : e * z ≠ z * e)
  (hzl : z * (d * e * d) ≠ d * e * d * z)
include hP hd he hz hde hdz hez hzl

theorem isPlane_planePt : IsPlane E (planePt d e z) := by
  have hr := range_planePt hP hd he hz hde hdz hez hzl
  have hmem : ∀ p, planePt d e z p ∈ E ∩ (Subgroup.closure ({d, e, z} : Set X) : Set X) :=
    fun p => hr ▸ Set.mem_range_self p
  have hinj := planePt_injective hP hd he hz hde hdz hez hzl
  refine ⟨fun p => (hmem p).1, hinj, fun p q hpq => ?_, planePt_tau hP hd he hz hde hdz hez hzl,
    fun t => ?_⟩
  · exact Pair.not_commute_of_mem_inter_closure_affine hP hd he hz hde hdz hez hzl (hmem p)
      (hmem q) fun h => hpq (hinj h)
  · refine ⟨(d * e) ^ t.1.val * (d * z) ^ t.2.val, ?_,
      fun p => conj_planePt_trans hP hd he hz hde hdz hez hzl t p⟩
    have hd' : d ∈ Subgroup.closure (Set.range (planePt d e z)) :=
      Subgroup.subset_closure ⟨0, planePt_zero⟩
    have he' : e ∈ Subgroup.closure (Set.range (planePt d e z)) :=
      Subgroup.subset_closure ⟨(1, 0), planePt_one_zero hP hd he hde⟩
    have hz' : z ∈ Subgroup.closure (Set.range (planePt d e z)) :=
      Subgroup.subset_closure ⟨(0, 1), planePt_zero_one hP hd hz hdz⟩
    exact mul_mem (pow_mem (mul_mem hd' he') _) (pow_mem (mul_mem hd' hz') _)

end Bridge

theorem mem_line_symm_pt : ∀ r s : Pt, s ≠ 0 → (s = 0 ∨ s = r ∨ s = r + r) →
    (r = 0 ∨ r = s ∨ r = s + s) := by
  decide

theorem line_inter_pt : ∀ r s x : Pt, (x = 0 ∨ x = r ∨ x = r + r) →
    (x = 0 ∨ x = s ∨ x = s + s) → x ≠ 0 → (s = 0 ∨ s = r ∨ s = r + r) := by
  decide +kernel

theorem sub_ne_zero_pt : ∀ p q : Pt, p ≠ q → q - p ≠ 0 := by decide

theorem line_eq_pt : ∀ r r' x : Pt, r ≠ 0 → (r = 0 ∨ r = r' ∨ r = r' + r') →
    ((x = 0 ∨ x = r' ∨ x = r' + r') ↔ (x = 0 ∨ x = r ∨ x = r + r)) := by
  decide +kernel

theorem exists_not_mem_line_pt : ∀ r : Pt, ∃ x : Pt, ¬ (x = 0 ∨ x = r ∨ x = r + r) := by
  decide

structure ConfAt (E : Set X) (φ : Pt → X) (w₁ w₂ : X) (r₁ r₂ : Pt) : Prop where
  plane : IsPlane E φ
  cent₁ : Cent E φ w₁
  cent₂ : Cent E φ w₂
  ne₁ : r₁ ≠ 0
  ne₂ : r₂ ≠ 0
  typ₁ : typ E φ w₁ = lineSet r₁
  typ₂ : typ E φ w₂ = lineSet r₂
  dist : r₂ ∉ lineSet r₁

@[expose] def part (E : Set X) (φ : Pt → X) (r : Pt) : Set X :=
  {e | Cent E φ e ∧ typ E φ e = lineSet r}

@[expose] def top (E : Set X) (φ : Pt → X) : Set X := {e | Cent E φ e ∧ typ E φ e = Set.univ}

theorem disjoint_part_top (E : Set X) (φ : Pt → X) (r : Pt) :
    Disjoint (part E φ r) (top E φ) := by
  rw [Set.disjoint_left]
  rintro e ⟨-, h1⟩ ⟨-, h2⟩
  obtain ⟨x, hx⟩ := exists_not_mem_line_pt r
  have : x ∈ lineSet r := h1 ▸ h2 ▸ Set.mem_univ x
  exact hx this

namespace ConfAt

variable {φ : Pt → X} {w₁ w₂ : X} {r₁ r₂ : Pt} (hc : ConfAt E φ w₁ w₂ r₁ r₂) (hP : Pair X E)
include hc hP

theorem cent_of_isWit {p q : Pt} (hpq : p ≠ q) {e : X} (he : IsWit E e (φ p) (φ q)) :
    Cent E φ e := by
  have hr0 : q - p ≠ 0 := sub_ne_zero_pt p q hpq
  by_cases h1 : q - p ∈ lineSet r₁
  · have h2 : q - p ∉ lineSet r₂ := fun h2 => hc.dist (line_inter_pt r₁ r₂ (q - p) h1 h2 hr0)
    refine hc.plane.cent_of_isWit hP hc.cent₂ hpq (s := r₂) ?_ ?_ ?_ he
    · rw [hc.typ₂]
      exact Or.inr (Or.inl rfl)
    · exact fun hs => h2 (mem_line_symm_pt (q - p) r₂ hc.ne₂ hs)
    · intro hw
      have h := (hc.plane.isWit_iff hP hc.cent₂).1 hw
      rw [hc.typ₂] at h
      exact h2 h
  · refine hc.plane.cent_of_isWit hP hc.cent₁ hpq (s := r₁) ?_ ?_ ?_ he
    · rw [hc.typ₁]
      exact Or.inr (Or.inl rfl)
    · exact fun hs => h1 (mem_line_symm_pt (q - p) r₁ hc.ne₁ hs)
    · intro hw
      have h := (hc.plane.isWit_iff hP hc.cent₁).1 hw
      rw [hc.typ₁] at h
      exact h1 h

theorem isWit_iff {p q : Pt} (hpq : p ≠ q) {e : X} :
    IsWit E e (φ p) (φ q) ↔ Cent E φ e ∧ q - p ∈ typ E φ e :=
  ⟨fun he => ⟨hc.cent_of_isWit hP hpq he,
      (hc.plane.isWit_iff hP (hc.cent_of_isWit hP hpq he)).1 he⟩,
    fun h => (hc.plane.isWit_iff hP h.1).2 h.2⟩

theorem wit_eq {r : Pt} (hr : r ≠ 0) :
    {e | IsWit E e (φ 0) (φ r)} = part E φ r ∪ top E φ := by
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_union, part, top]
  rw [hc.isWit_iff hP (Ne.symm hr), sub_zero_pt]
  constructor
  · rintro ⟨hce, hre⟩
    rcases hc.plane.typ_cases hP hce with h | h | ⟨r', hr', h⟩
    · rw [h] at hre
      exact absurd hre hr
    · exact Or.inr ⟨hce, h⟩
    · rw [h] at hre
      refine Or.inl ⟨hce, ?_⟩
      rw [h]
      ext x
      exact line_eq_pt r r' x hr hre
  · rintro (⟨hce, h⟩ | ⟨hce, h⟩)
    · exact ⟨hce, h ▸ Or.inr (Or.inl rfl)⟩
    · exact ⟨hce, h ▸ Set.mem_univ r⟩

theorem ncard_wit_eq_add {r : Pt} (hr : r ≠ 0) :
    {e | IsWit E e (φ 0) (φ r)}.ncard = (part E φ r).ncard + (top E φ).ncard := by
  have := Pair.finite hP
  rw [hc.wit_eq hP hr, Set.ncard_union_eq (disjoint_part_top E φ r)]

end ConfAt

theorem ConfAt.part_nonempty {φ : Pt → X} {w₁ w₂ : X} {r₁ r₂ : Pt}
    (hc : ConfAt E φ w₁ w₂ r₁ r₂) (hS : Setting X E) {r : Pt} (hr : r ≠ 0) :
    (part E φ r).Nonempty := by
  have hP := hS.pair
  have := Pair.finite hP
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have h1 := hc.ncard_wit_eq_add hP hr
  have h2 := hc.ncard_wit_eq_add hP hc.ne₁
  have hpne : ∀ {s : Pt}, s ≠ 0 → φ 0 * φ s ≠ φ s * φ 0 := fun hs =>
    hc.plane.ncomm 0 _ (Ne.symm hs)
  have h3 := hS.ncard_wit_eq (hc.plane.mem 0) (hc.plane.mem r) (hpne hr) (hc.plane.mem 0)
    (hc.plane.mem r₁) (hpne hc.ne₁)
  have hw : w₁ ∈ part E φ r₁ := ⟨hc.cent₁, hc.typ₁⟩
  have h4 : 0 < (part E φ r₁).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨w₁, hw⟩
  rw [h, Set.ncard_empty] at h1
  omega

end O3

end CFSG.Fischer.Classification
