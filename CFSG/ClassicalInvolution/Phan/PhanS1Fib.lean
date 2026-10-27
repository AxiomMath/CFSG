module

public import CFSG.ClassicalInvolution.Phan.PhanB8Tits

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] {S : PhanFamilyB3 C G}

section Points

theorem mem_residue_mk_iff (J : Set (Fin 3)) (a b : G) :
    (b : G ⧸ torusSub S) ∈ (phanSystem S).residue J (a : G ⧸ torusSub S) ↔
      a⁻¹ * b ∈ parab S J := by
  rw [mem_parab_iff]
  constructor
  · intro h
    have h' := (phanSystem_isMorphism_smul (S := S) a⁻¹).mapsTo_residue J
      (a : G ⧸ torusSub S) h
    simp only [smul_mk, inv_mul_cancel] at h'
    exact h'
  · intro h
    have h' := (phanSystem_isMorphism_smul (S := S) a).mapsTo_residue J
      ((1 : G) : G ⧸ torusSub S) h
    simp only [smul_mk, mul_one, mul_inv_cancel_left] at h'
    exact h'

variable (S) in
@[expose] noncomputable def ptMap : G ⧸ torusSub S → G ⧸ parab S {1, 2} :=
  Subgroup.quotientMapOfLE (torusSub_le_parab (S := S) {1, 2})

theorem ptMap_mk (a : G) :
    ptMap S (a : G ⧸ torusSub S) = (a : G ⧸ parab S {1, 2}) := rfl

theorem ptMap_eq_iff (c d : G ⧸ torusSub S) :
    ptMap S c = ptMap S d ↔ d ∈ (phanSystem S).residue {1, 2} c := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective d
  rw [ptMap_mk, ptMap_mk, QuotientGroup.eq, mem_residue_mk_iff]

variable (S) in
@[expose] def ptGraph : SimpleGraph (G ⧸ parab S {1, 2}) where
  Adj x y := x ≠ y ∧ ∃ c d : G ⧸ torusSub S, ptMap S c = x ∧ ptMap S d = y ∧
    (phanSystem S).adj 0 c d
  symm := ⟨fun _ _ ⟨hne, c, d, hc, hd, h⟩ => ⟨hne.symm, d, c, hd, hc, adj_symm h⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem ptGraph_adj_of_adj {c d : G ⧸ torusSub S} (h : (phanSystem S).adj 0 c d)
    (hne : ptMap S c ≠ ptMap S d) : (ptGraph S).Adj (ptMap S c) (ptMap S d) :=
  ⟨hne, c, d, rfl, rfl, h⟩

variable (S) in
@[expose] def PtStep0 : Prop :=
  ∀ {e g : G ⧸ torusSub S}, (phanSystem S).adj 0 e g → ptMap S e = ptMap S g → e = g

variable (S) in
@[expose] def PtEdge : Prop :=
  ∀ {a b c d : G ⧸ torusSub S}, (phanSystem S).adj 0 a c → (phanSystem S).adj 0 b d →
    ptMap S a = ptMap S b → ptMap S c = ptMap S d → ptMap S a ≠ ptMap S c →
      d ∈ (phanSystem S).residue {2} c ∧ b ∈ (phanSystem S).residue {2} a

variable (S) in
@[expose] noncomputable def phanFib (h0 : PtStep0 S) : Fib (phanSystem S) (ptGraph S) where
  P := ptMap S
  a := 0
  J' := {1, 2}
  Q := fun _ => True
  step_Q := fun _ _ _ => trivial
  step_P := fun {i e g} hi hadj _ =>
    (ptMap_eq_iff e g).2 (residue_mono (Set.singleton_subset_iff.2 hi) e
      (mem_residue_singleton.2 hadj))
  step_a := fun {e g} hadj _ => by
    by_cases h : ptMap S e = ptMap S g
    · exact Or.inl (h0 hadj h)
    · exact Or.inr (ptGraph_adj_of_adj hadj h)

end Points

section Rigid

theorem twoHomotopic_of_types {I C' : Type*} {X : ChamberSystem I C'} {J : Set I}
    (hJ : J.encard ≤ 2) {x : C'} {γ₁ γ₂ : List (I × C')} (h₁ : X.IsGallery x γ₁)
    (h₂ : X.IsGallery x γ₂) (hJ₁ : ∀ i ∈ galleryType γ₁, i ∈ J)
    (hJ₂ : ∀ i ∈ galleryType γ₂, i ∈ J) (hend : galleryEnd x γ₁ = galleryEnd x γ₂) :
    X.TwoHomotopic x γ₁ γ₂ := by
  have := twoHomotopic_replace (X := X) (x := x) [] γ₁ γ₂ [] hJ (by simpa using h₁)
    (by simpa using h₂) hJ₁ hJ₂ (by simpa using hend)
  simpa using this

theorem pair_encard_le_two (i j : Fin 3) : ({i, j} : Set (Fin 3)).encard ≤ 2 :=
  (Set.encard_insert_le _ _).trans (by rw [Set.encard_singleton]; norm_num)

theorem single_subset_pair : ({2} : Set (Fin 3)) ⊆ {1, 2} := by
  intro i hi
  simp only [Set.mem_singleton_iff] at hi
  simp [hi]

theorem single_subset_pair' : ({2} : Set (Fin 3)) ⊆ {0, 2} := by
  intro i hi
  simp only [Set.mem_singleton_iff] at hi
  simp [hi]

theorem phanFib_rigid (h0 : PtStep0 S) (he : PtEdge S) : (phanFib S h0).Rigid where
  null := fun {e γ} _ hγ hend => by
    have h := twoHomotopic_of_types (X := phanSystem S) (J := {1, 2}) (pair_encard_le_two 1 2)
      hγ.1 (isGallery_nil e) hγ.2 (by simp) (by simpa using hend)
    exact h
  edge := by
    intro e e' f g ρ ρ' x' _ _ hPe hΓ hρ hf hPf hρ' hf' hPf'
    have hP1 : ptMap S (galleryEnd e ρ) = ptMap S e :=
      (phanFib S h0).P_galleryEnd trivial hρ
    have hP1' : ptMap S (galleryEnd e' ρ') = ptMap S e' :=
      (phanFib S h0).P_galleryEnd trivial hρ'
    have hPe' : ptMap S e = ptMap S e' := hPe
    have hPf₁ : ptMap S f = x' := hPf
    have hPf₂ : ptMap S g = x' := hPf'
    have hne : ptMap S (galleryEnd e ρ) ≠ ptMap S f := by
      rw [hP1, hPf₁]
      exact hΓ.1
    obtain ⟨hgres, hE'res⟩ := he hf hf' (hP1.trans (hPe'.trans hP1'.symm))
      (hPf₁.trans hPf₂.symm) hne
    obtain ⟨τ₂, hτ₂, hτ₂e⟩ := mem_residue_iff_exists_isJGallery.1 hE'res
    obtain ⟨τ', hτ', hτ'e⟩ := mem_residue_iff_exists_isJGallery.1 hgres
    have hτ₂J : IsJGallery (phanSystem S) {1, 2} (galleryEnd e ρ) τ₂ :=
      hτ₂.mono single_subset_pair
    have hcat₁ : IsJGallery (phanSystem S) {1, 2} e (ρ ++ τ₂) := hρ.append hτ₂J
    have hend₁ : galleryEnd e (ρ ++ τ₂) = galleryEnd e' ρ' := by
      rw [galleryEnd_append, hτ₂e]
    have hrevJ : IsJGallery (phanSystem S) {1, 2} (galleryEnd e (ρ ++ τ₂))
        (galleryReverse e' ρ') := by
      rw [hend₁]
      exact hρ'.reverse
    refine ⟨ρ ++ τ₂ ++ galleryReverse e' ρ', τ', hcat₁.append hrevJ, ?_,
      hτ'.mono single_subset_pair, hτ'e, ?_⟩
    · rw [galleryEnd_append, hend₁, galleryEnd_galleryReverse]
    ·
      have hrev : (phanSystem S).TwoHomotopic (galleryEnd e' ρ')
          (galleryReverse e' ρ' ++ ρ') [] := twoHomotopic_reverse_append hρ'.1
      have hA : (phanSystem S).TwoHomotopic e
          (ρ ++ τ₂ ++ galleryReverse e' ρ' ++ ρ' ++ [(0, g)])
          (ρ ++ τ₂ ++ [(0, g)]) := by
        have e1 : ρ ++ τ₂ ++ galleryReverse e' ρ' ++ ρ' ++ [(0, g)] =
            (ρ ++ τ₂) ++ ((galleryReverse e' ρ' ++ ρ') ++ [(0, g)]) := by simp
        have e2 : ρ ++ τ₂ ++ [(0, g)] = (ρ ++ τ₂) ++ ([] ++ [(0, g)]) := by simp
        rw [e1, e2]
        refine TwoHomotopic.append_left (X := phanSystem S) (x := e) (ρ ++ τ₂) ?_
        rw [hend₁]
        exact hrev.append_right [(0, g)]
      have hB : (phanSystem S).TwoHomotopic (galleryEnd e ρ) (τ₂ ++ [(0, g)])
          ((0, f) :: τ') := by
        refine twoHomotopic_of_types (J := {0, 2}) (pair_encard_le_two 0 2) ?_ ?_ ?_ ?_ ?_
        · refine hτ₂.1.append ?_
          rw [hτ₂e]
          exact ⟨hf', trivial⟩
        · exact ⟨hf, hτ'.1⟩
        · intro i hi
          rw [galleryType_append, List.mem_append] at hi
          rcases hi with hi | hi
          · exact single_subset_pair' (hτ₂.2 i hi)
          · simp [galleryType] at hi
            subst hi
            simp
        · intro i hi
          simp only [galleryType, List.map_cons, List.mem_cons] at hi
          rcases hi with rfl | hi
          · simp
          · exact single_subset_pair' (hτ'.2 i (by simpa [galleryType] using hi))
        · rw [galleryEnd_append, hτ₂e]
          simp only [galleryEnd_cons]
          rw [hτ'e]
          simp
      have hB' := TwoHomotopic.append_left (X := phanSystem S) (x := e) ρ hB
      have e3 : ρ ++ τ₂ ++ [(0, g)] = ρ ++ (τ₂ ++ [(0, g)]) := by simp
      show (phanSystem S).TwoHomotopic e
        (ρ ++ τ₂ ++ galleryReverse e' ρ' ++ ρ' ++ [(0, g)]) (ρ ++ (0, f) :: τ')
      rw [e3] at hA
      exact hA.trans hB'

end Rigid

end CFSG.ClassicalInvolution.PhanB3.S
