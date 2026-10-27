module

public import CFSG.Fischer.Classification.PartII.O3.Dual

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

@[expose] def Others (r s₁ s₂ s₃ : Pt) : Prop :=
  s₁ ≠ 0 ∧ s₂ ≠ 0 ∧ s₃ ≠ 0 ∧ ¬ (s₁ = 0 ∨ s₁ = r ∨ s₁ = r + r) ∧
    ¬ (s₂ = 0 ∨ s₂ = r ∨ s₂ = r + r) ∧ ¬ (s₃ = 0 ∨ s₃ = r ∨ s₃ = r + r) ∧
    ¬ (s₂ = 0 ∨ s₂ = s₁ ∨ s₂ = s₁ + s₁) ∧ ¬ (s₃ = 0 ∨ s₃ = s₁ ∨ s₃ = s₁ + s₁) ∧
    ¬ (s₃ = 0 ∨ s₃ = s₂ ∨ s₃ = s₂ + s₂)

theorem exists_three_other_dirs (r : Pt) (hr : r ≠ 0) : ∃ s₁ s₂ s₃ : Pt, Others r s₁ s₂ s₃ := by
  obtain ⟨a, b⟩ := r
  fin_cases a <;> fin_cases b
  · exact absurd rfl hr
  · exact ⟨(1, 0), (1, 1), (1, 2), by unfold Others; decide⟩
  · exact ⟨(1, 0), (1, 1), (1, 2), by unfold Others; decide⟩
  · exact ⟨(0, 1), (1, 1), (1, 2), by unfold Others; decide⟩
  · exact ⟨(1, 0), (0, 1), (1, 2), by unfold Others; decide⟩
  · exact ⟨(1, 0), (0, 1), (1, 1), by unfold Others; decide⟩
  · exact ⟨(0, 1), (1, 1), (1, 2), by unfold Others; decide⟩
  · exact ⟨(1, 0), (0, 1), (1, 1), by unfold Others; decide⟩
  · exact ⟨(1, 0), (0, 1), (1, 2), by unfold Others; decide⟩

theorem disjoint_part_part (E : Set X) (φ : Pt → X) {s s' : Pt} (h : s' ∉ lineSet s) :
    Disjoint (part E φ s) (part E φ s') := by
  rw [Set.disjoint_left]
  intro e he he'
  exact ConfAt.typ_ne_of_not_mem he he' h rfl

theorem line_pt : ∀ p q x : Pt, (x - p = 0 ∨ x - p = q - p ∨ x - p = q - p + (q - p)) →
    x = p ∨ x = q ∨ x = -p - q := by
  decide +kernel

theorem not_line_pt : ∀ p q x : Pt, ¬ (x - p = 0 ∨ x - p = q - p ∨ x - p = q - p + (q - p)) →
    x ≠ p ∧ x ≠ q ∧ x ≠ -p - q := by
  decide +kernel

namespace ConfAt

variable {φ : Pt → X} {w₁ w₂ : X} {r₁ r₂ : Pt} (hc : ConfAt E φ w₁ w₂ r₁ r₂) (hS : Setting X E)
include hc hS

theorem ncard_part_eq {r s : Pt} (hr : r ≠ 0) (hs : s ≠ 0) :
    (part E φ s).ncard = (part E φ r).ncard := by
  have h1 := hc.ncard_wit_eq_add hS.pair hr
  have h2 := hc.ncard_wit_eq_add hS.pair hs
  have h3 := hS.ncard_wit_eq (hc.plane.mem 0) (hc.plane.mem r) (hc.plane.ncomm 0 r (Ne.symm hr))
    (hc.plane.mem 0) (hc.plane.mem s) (hc.plane.ncomm 0 s (Ne.symm hs))
  omega

theorem false_of_commute_line {e₀ : X} (he₀ : e₀ ∈ E) (he₀π : ∀ q, e₀ ≠ φ q) {p r : Pt}
    (hr : r ≠ 0) (hline : ∀ q, e₀ * φ q = φ q * e₀ ↔ q - p ∈ lineSet r) : False := by
  have hP := hS.pair
  have := Pair.finite hP
  obtain ⟨s₁, s₂, s₃, h1, h2, h3, h1r, h2r, h3r, h21, h31, h32⟩ := exists_three_other_dirs r hr
  obtain ⟨e, he⟩ := hc.part_nonempty hS hr
  obtain ⟨ψ, u, hu, hψ, hψp⟩ := hc.exists_dual hS (p₀ := p) hr h1 h1r he
  have hpq : p ≠ p + r := fun h => hr (eq_zero_of_add_eq_pt p r h.symm)
  have hcp : e₀ * φ p = φ p * e₀ := (hline p).2 (by rw [sub_self]; exact Or.inl rfl)
  have hcr : e₀ * φ (p + r) = φ (p + r) * e₀ :=
    (hline _).2 (by rw [add_sub_cancel_left_pt]; exact Or.inr (Or.inl rfl))
  have hmu : e₀ ∈ muSet E (φ p) (φ (p + r)) :=
    ⟨⟨he₀, he₀π p, hcp⟩, ⟨he₀, he₀π _, hcr⟩⟩
  have hnc : ∀ s, s ∉ lineSet r → e₀ * φ (p + s) ≠ φ (p + s) * e₀ := fun s hs h =>
    hs (by rw [← add_sub_cancel_left_pt p s]; exact (hline _).1 h)
  have hnw : ¬ IsWit E e₀ (φ p) (φ (p + r)) := fun h =>
    hnc s₁ h1r ((hc.cent_of_isWit hP hpq h).2 (p + s₁)).2.2.symm
  have hcψ : Cent E ψ e₀ := hψ.plane.cent_of_commute he₀ fun q => by
    have hw : IsWit E (ψ q) (φ p) (φ (p + r)) := (hc.isWit_iff hP hpq).2
      ⟨(hψp q).1, by rw [add_sub_cancel_left_pt, (hψp q).2]; exact Or.inr (Or.inl rfl)⟩
    exact (Pair.commute_of_isWit hP hw hmu hnw).symm
  have hoth : ∀ f, (∃ s, s ≠ 0 ∧ s ∉ lineSet r ∧ f ∈ part E φ s) ∨ f ∈ top E φ →
      Cent E ψ f ∧ f * e₀ ≠ e₀ * f := by
    rintro f hf
    obtain ⟨s, hsr, hfs, hst⟩ : ∃ s, s ∉ lineSet r ∧ (f ∈ part E φ s ∪ top E φ) ∧
        s ∈ typ E φ f := by
      rcases hf with ⟨s, -, hsr, hfs⟩ | hft
      · exact ⟨s, hsr, Or.inl hfs, by rw [hfs.2]; exact Or.inr (Or.inl rfl)⟩
      · exact ⟨s₁, h1r, Or.inr hft, by rw [hft.2]; exact Set.mem_univ _⟩
    have hcf : Cent E φ f := by
      rcases hfs with h | h
      exacts [h.1, h.1]
    refine ⟨⟨hcf.1, fun q => mem_localClass_symm (hψp q).1.1
      (hc.mem_localClass_of_part hS hsr (hψp q) hfs)⟩, fun h => ?_⟩
    have hef : e₀ ≠ f := fun hef => hnc s₁ h1r (by rw [hef]; exact (hcf.2 _).2.2.symm)
    have hcs := hc.plane.commute_add hP hcf ⟨he₀, hef, h.symm⟩ he₀π (q := p + s) hcp
      (by rw [add_sub_cancel_left_pt]; exact hst)
    exact hnc s hsr hcs
  have hu' : (∃ s, s ≠ 0 ∧ s ∉ lineSet r ∧ u ∈ part E φ s) ∨ u ∈ top E φ := by
    rcases hu with hu | hu
    · exact Or.inl ⟨s₁, h1, h1r, hu⟩
    · exact Or.inr hu
  have he₀t : typ E ψ e₀ = lineSet (0, 1) := by
    obtain ⟨hcu, hne⟩ := hoth u hu'
    rw [← hψ.plane.typ_eq_of_not_commute hP hcu hcψ hne, hψ.typ₂]
  have hall : ∀ f, (∃ s, s ≠ 0 ∧ s ∉ lineSet r ∧ f ∈ part E φ s) ∨ f ∈ top E φ →
      f ∈ part E ψ (0, 1) := fun f hf =>
    ⟨(hoth f hf).1, (hψ.plane.typ_eq_of_not_commute hP (hoth f hf).1 hcψ (hoth f hf).2).trans
      he₀t⟩
  set T := part E φ s₁ ∪ (part E φ s₂ ∪ (part E φ s₃ ∪ top E φ))
  have hsub : insert e₀ T ⊆ part E ψ (0, 1) := by
    rintro f (rfl | hf | hf | hf | hf)
    · exact ⟨hcψ, he₀t⟩
    · exact hall f (Or.inl ⟨s₁, h1, h1r, hf⟩)
    · exact hall f (Or.inl ⟨s₂, h2, h2r, hf⟩)
    · exact hall f (Or.inl ⟨s₃, h3, h3r, hf⟩)
    · exact hall f (Or.inr hf)
  have he₀T : e₀ ∉ T := by
    have hne : ¬ Cent E φ e₀ := fun h => hnc s₁ h1r (h.2 _).2.2.symm
    rintro (hf | hf | hf | hf)
    exacts [hne hf.1, hne hf.1, hne hf.1, hne hf.1]
  have hT : T.ncard = (part E φ s₁).ncard + ((part E φ s₂).ncard + ((part E φ s₃).ncard +
      (top E φ).ncard)) := by
    rw [Set.ncard_union_eq (Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h21,
        Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h31, disjoint_part_top E φ s₁⟩⟩),
      Set.ncard_union_eq (Set.disjoint_union_right.2 ⟨disjoint_part_part E φ h32,
        disjoint_part_top E φ s₂⟩),
      Set.ncard_union_eq (disjoint_part_top E φ s₃)]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem he₀T, hT, hc.ncard_part_eq hS hr h1, hc.ncard_part_eq hS hr h2,
    hc.ncard_part_eq hS hr h3] at hle
  have hw1 := hψ.ncard_wit_eq_add hP (r := (0, 1)) (by decide)
  have hw2 := hc.ncard_wit_eq_add hP hr
  have hw3 := hS.ncard_wit_eq (hc.plane.mem 0) (hc.plane.mem r) (hc.plane.ncomm 0 r (Ne.symm hr))
    (hψ.plane.mem 0) (hψ.plane.mem (0, 1)) (hψ.plane.ncomm 0 (0, 1) (by decide))
  omega

theorem cent_of_mem_muSet {p q : Pt} (hpq : p ≠ q) {e : X} (he : e ∈ muSet E (φ p) (φ q)) :
    Cent E φ e := by
  have heπ : ∀ x, e ≠ φ x := by
    intro x hx
    have h1 := he.1
    rw [hx] at h1
    exact hc.plane.ncomm x p (fun h => h1.2.1 (by rw [h])) h1.2.2
  have hT : IsTauClosed {x | e * φ x = φ x * e} := hc.plane.isTauClosed_commute
  have hp : e * φ p = φ p * e := he.1.2.2
  have hq : e * φ q = φ q * e := he.2.2.2
  by_contra hne
  refine hc.false_of_commute_line hS he.1.1 heπ (p := p) (r := q - p) (sub_ne_zero_pt p q hpq)
    fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · by_contra hxl
    obtain ⟨h1, h2, h3⟩ := not_line_pt p q x hxl
    have huniv := hT.eq_univ_of_not_collinear hp hq hx (Ne.symm hpq) h1 h2 h3
    exact hne (hc.plane.cent_of_commute he.1.1 fun y =>
      (huniv ▸ Set.mem_univ y : y ∈ {x | e * φ x = φ x * e}))
  · rcases line_pt p q x hx with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hT p hp q hq

end ConfAt

end O3

end CFSG.Fischer.Classification
