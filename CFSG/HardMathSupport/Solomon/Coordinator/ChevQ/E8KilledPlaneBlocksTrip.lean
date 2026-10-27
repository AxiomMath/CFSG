module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksPred
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneWords

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg


set_option linter.unusedSectionVars false

theorem permOf8_orbit {P : Array ℕ} {v : WeylGroup Tag.E8} (hP : PermOf8 P v) {a : ℕ}
    (ha : a < 240) :
    P.getD a 0 < 240 ∧ P.getD (P.getD a 0) 0 < 240 ∧
      e8Certificate.root (P.getD a 0) = v • e8Certificate.root a ∧
      e8Certificate.root (P.getD (P.getD a 0) 0) = v ^ 2 • e8Certificate.root a := by
  obtain ⟨h1, h2⟩ := hP a ha
  obtain ⟨h3, h4⟩ := hP _ h1
  refine ⟨h1, h3, h2, ?_⟩
  rw [h4, h2, pow_two, mul_smul]

theorem root_mem_orbit_of_mem {P : Array ℕ} {v : WeylGroup Tag.E8} (hP : PermOf8 P v) {a y : ℕ}
    (ha : a < 240) (hy : y ∈ [a, P.getD a 0, P.getD (P.getD a 0) 0]) :
    e8Certificate.root y ∈ ({e8Certificate.root a, v • e8Certificate.root a,
      v ^ 2 • e8Certificate.root a} : Set (Fin Tag.E8.rank → ℤ)) := by
  obtain ⟨-, -, h2, h4⟩ := permOf8_orbit hP ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hy with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h4)

theorem mem_e8PlaneTrip {P : Array ℕ} {G : Array ℤ} {S : List ℕ} {d : ℕ} :
    d ∈ e8PlaneTrip P G S ↔ d ∈ S ∧
      (G.getD (240 * d + P.getD d 0) 0 == 0 && G.getD (240 * d + P.getD (P.getD d 0) 0) 0 == 0 &&
        G.getD (240 * P.getD d 0 + P.getD (P.getD d 0) 0) 0 == 0) = true := by
  unfold e8PlaneTrip
  rw [List.mem_filter]

theorem mem_e8PlaneTrip_iff {P : Array ℕ} {G : Array ℤ} {σ : ℕ} {v : WeylGroup Tag.E8}
    (hP : PermOf8 P v) (hG : GramOf8 G) {d : ℕ} (hd : d ∈ e8PlaneSig σ) :
    d ∈ e8PlaneTrip P G (e8PlaneSig σ) ↔ IsOrthTriple v (e8Certificate.root d) := by
  have hd240 := (mem_e8PlaneSig.1 hd).1
  obtain ⟨h1, h3, h2, h4⟩ := permOf8_orbit hP hd240
  rw [mem_e8PlaneTrip, and_iff_right hd, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq,
    beq_iff_eq, beq_iff_eq, hG _ _ hd240 h1, hG _ _ hd240 h3, hG _ _ h1 h3, h4, h2]
  exact and_assoc

theorem e8PlaneTR_spec {rt P : Array ℕ}
    (hrt : ∀ b x, b < 240 → x < 240 → rt.getD (240 * b + x) 0 < 240 ∧
      e8Certificate.root (rt.getD (240 * b + x) 0) =
        rootReflection (e8Certificate.root b) • e8Certificate.root x)
    {v : WeylGroup Tag.E8} (hP : PermOf8 P v) {δ x : ℕ} (hδ : δ < 240) (hx : x < 240) :
    e8PlaneTR rt P δ x < 240 ∧
      e8Certificate.root (e8PlaneTR rt P δ x) =
        tripleRefl v (e8Certificate.root δ) • e8Certificate.root x := by
  obtain ⟨h1, h3, h2, h4⟩ := permOf8_orbit hP hδ
  have hw : ∀ b ∈ [δ, P.getD δ 0, P.getD (P.getD δ 0) 0], b < 240 := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hδ
    · exact h1
    · exact h3
  obtain ⟨hlt, heq⟩ := e8PlanePermOf_spec hrt hw hx
  refine ⟨hlt, ?_⟩
  unfold e8PlaneTR
  rw [heq]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h2, h4]
  unfold tripleRefl
  simp only [mul_assoc]

theorem e8PlaneD3T_sound {rt P : Array ℕ} {G : Array ℤ} {σ : ℕ} {v : WeylGroup Tag.E8}
    (hrt : ∀ b x, b < 240 → x < 240 → rt.getD (240 * b + x) 0 < 240 ∧
      e8Certificate.root (rt.getD (240 * b + x) 0) =
        rootReflection (e8Certificate.root b) • e8Certificate.root x)
    (hP : PermOf8 P v) (hG : GramOf8 G) (h : e8PlaneD3T rt P G σ = true) :
    ∀ d ∈ sigSet σ, IsOrthTriple v d → ∀ β ∈ sigSet σ, IsOrthTriple v β →
      ∃ l : List (Fin Tag.E8.rank → ℤ), l.length ≤ 2 ∧
        (∀ δ ∈ l, δ ∈ sigSet σ ∧ IsOrthTriple v δ) ∧
        (l.map (tripleRefl v)).prod • β ∈
          ({d, v • d, v ^ 2 • d} : Set (Fin Tag.E8.rank → ℤ)) := by
  unfold e8PlaneD3T at h
  dsimp only at h
  rintro d ⟨a, ha, rfl⟩ hdo β ⟨b, hb, rfl⟩ hbo
  have haT : a ∈ e8PlaneTrip P G (e8PlaneSig σ) := (mem_e8PlaneTrip_iff hP hG ha).2 hdo
  have hbT : b ∈ e8PlaneTrip P G (e8PlaneSig σ) := (mem_e8PlaneTrip_iff hP hG hb).2 hbo
  have ha240 := (mem_e8PlaneSig.1 ha).1
  have hb240 := (mem_e8PlaneSig.1 hb).1
  have h1 := List.all_eq_true.1 h a haT
  have h2 := List.all_eq_true.1 h1 b hbT
  rw [Bool.or_eq_true, Bool.or_eq_true] at h2
  rcases h2 with (h3 | h3) | h3
  · refine ⟨[], by simp, by simp, ?_⟩
    rw [List.map_nil, List.prod_nil, one_smul]
    exact root_mem_orbit_of_mem hP ha240 (List.contains_iff_mem.1 h3)
  · obtain ⟨δ, hδT, hδ⟩ := List.any_eq_true.1 h3
    have hδS : δ ∈ e8PlaneSig σ := (List.mem_filter.1 hδT).1
    have hδ240 := (mem_e8PlaneSig.1 hδS).1
    obtain ⟨-, heq⟩ := e8PlaneTR_spec hrt hP hδ240 hb240
    refine ⟨[e8Certificate.root δ], by simp, ?_, ?_⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨⟨δ, hδS, rfl⟩, (mem_e8PlaneTrip_iff hP hG hδS).1 hδT⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← heq]
      exact root_mem_orbit_of_mem hP ha240 (List.contains_iff_mem.1 hδ)
  · obtain ⟨δ₁, hδ₁T, h4⟩ := List.any_eq_true.1 h3
    obtain ⟨δ₂, hδ₂T, hδ⟩ := List.any_eq_true.1 h4
    have hδ₁S : δ₁ ∈ e8PlaneSig σ := (List.mem_filter.1 hδ₁T).1
    have hδ₂S : δ₂ ∈ e8PlaneSig σ := (List.mem_filter.1 hδ₂T).1
    have hδ₁240 := (mem_e8PlaneSig.1 hδ₁S).1
    have hδ₂240 := (mem_e8PlaneSig.1 hδ₂S).1
    obtain ⟨hlt₂, heq₂⟩ := e8PlaneTR_spec hrt hP hδ₂240 hb240
    obtain ⟨-, heq₁⟩ := e8PlaneTR_spec hrt hP hδ₁240 hlt₂
    refine ⟨[e8Certificate.root δ₁, e8Certificate.root δ₂], by simp, ?_, ?_⟩
    · intro x hx
      rw [List.mem_cons, List.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ⟨⟨δ₁, hδ₁S, rfl⟩, (mem_e8PlaneTrip_iff hP hG hδ₁S).1 hδ₁T⟩
      · exact ⟨⟨δ₂, hδ₂S, rfl⟩, (mem_e8PlaneTrip_iff hP hG hδ₂S).1 hδ₂T⟩
    · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [mul_smul, ← heq₂, ← heq₁]
      exact root_mem_orbit_of_mem hP ha240 (List.contains_iff_mem.1 hδ)

theorem e8PlaneD3_full_sound {rt P : Array ℕ} {G : Array ℤ} {σ : ℕ} {v : WeylGroup Tag.E8}
    (hrt : ∀ b x, b < 240 → x < 240 → rt.getD (240 * b + x) 0 < 240 ∧
      e8Certificate.root (rt.getD (240 * b + x) 0) =
        rootReflection (e8Certificate.root b) • e8Certificate.root x)
    (hP : PermOf8 P v) (hG : GramOf8 G) (h : (e8PlaneD3 P G σ && e8PlaneD3T rt P G σ) = true) :
    (sigSet σ).ncard = 24 ∧ (∀ γ ∈ sigSet σ, v • γ = γ ∨ iform γ (v • γ) = 0) ∧
      (∀ d ∈ sigSet σ, IsOrthTriple v d → ∀ β ∈ sigSet σ, IsOrthTriple v β →
        ∃ l : List (Fin Tag.E8.rank → ℤ), l.length ≤ 2 ∧
          (∀ δ ∈ l, δ ∈ sigSet σ ∧ IsOrthTriple v δ) ∧
          (l.map (tripleRefl v)).prod • β ∈
            ({d, v • d, v ^ 2 • d} : Set (Fin Tag.E8.rank → ℤ))) ∧
      ∃ d ∈ sigSet σ, iform d (v • d) = 0 ∧ iform d (v ^ 2 • d) = 0 ∧
        iform (v • d) (v ^ 2 • d) = 0 := by
  rw [Bool.and_eq_true] at h
  obtain ⟨h24, hfix, horb⟩ := e8PlaneD3_sound hP hG h.1
  exact ⟨h24, hfix, e8PlaneD3T_sound hrt hP hG h.2, horb⟩

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane
