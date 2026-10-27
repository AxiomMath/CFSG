module

public import CFSG.ClassicalInvolution.Phan.PhanQ38SolidNull

public section

namespace CFSG.ClassicalInvolution.PhanQ

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG

section Smul

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G}

theorem ptMap_smul (g : G) (c : G ⧸ torusSub S) : ptMap S (g • c) = g • ptMap S c := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  rw [smul_mk, ptMap_mk, ptMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul]

theorem ptGraph_adj_smul_of_adj (g : G) {x y : G ⧸ parab S {1, 2, 3}} (h : (ptGraph S).Adj x y) :
    (ptGraph S).Adj (g • x) (g • y) := by
  obtain ⟨hne, c, d, hc, hd, hadj⟩ := h
  refine ⟨fun h' => hne (smul_left_cancel g h'), g • c, g • d, ?_, ?_,
    (phanSystem_isMorphism_smul (S := S) g) 0 _ _ hadj⟩
  · rw [ptMap_smul, hc]
  · rw [ptMap_smul, hd]

theorem ptGraph_adj_smul (g : G) {x y : G ⧸ parab S {1, 2, 3}} :
    (ptGraph S).Adj (g • x) (g • y) ↔ (ptGraph S).Adj x y := by
  refine ⟨fun h => ?_, ptGraph_adj_smul_of_adj g⟩
  have := ptGraph_adj_smul_of_adj g⁻¹ h
  simpa using this

theorem IsJGallery.smul {J : Set (Fin 4)} (g : G) {c : G ⧸ torusSub S}
    {γ : List (Fin 4 × G ⧸ torusSub S)} (h : IsJGallery (phanSystem S) J c γ) :
    IsJGallery (phanSystem S) J (g • c) (galleryMap (g • ·) γ) :=
  ⟨(phanSystem_isMorphism_smul (S := S) g).isGallery h.1, by simpa using h.2⟩

theorem solidNull_of_points_smul (h0 : PtStep0 S) {J₀ : Set (Fin 4)}
    (hJ₀ : J₀ = {0, 1, 2} ∨ J₀ = {0, 1, 3}) (R : Set (G ⧸ torusSub S))
    (hR : ∀ {i : Fin 4} {e g : G ⧸ torusSub S}, i ∈ J₀ → (phanSystem S).adj i e g → e ∈ R →
      g ∈ R)
    (hip : ∀ c ∈ R, ∀ c' ∈ R, ptMap S c = ptMap S c' →
      ∃ τ, IsJGallery (phanSystem S) {i | i ∈ J₀ ∧ i ≠ 0} c τ ∧ galleryEnd c τ = c')
    (hedge : ∀ c ∈ R, ∀ y ∈ ptMap S '' R, (ptGraph S).Adj (ptMap S c) y →
      ∃ c₁ ∈ R, ∃ g ∈ R, ptMap S c₁ = ptMap S c ∧ ptMap S g = y ∧ (phanSystem S).adj 0 c₁ g)
    (g : G) {x : G ⧸ parab S {1, 2, 3}} (w : (ptGraph S).Walk x x)
    (hw : ∀ v ∈ w.support, g⁻¹ • v ∈ ptMap S '' R) : SolidNull S h0 w := by
  refine solidNull_of_points h0 hJ₀ ((g • ·) '' R) ?_ ?_ ?_ w ?_
  · rintro i e g' hi hadj ⟨c, hc, rfl⟩
    have h1 := (phanSystem_isMorphism_smul (S := S) g⁻¹) i _ _ hadj
    dsimp only at h1
    rw [inv_smul_smul] at h1
    refine ⟨g⁻¹ • g', hR hi h1 hc, ?_⟩
    simp
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hp
    rw [ptMap_smul, ptMap_smul] at hp
    obtain ⟨τ, hτ, hτe⟩ := hip c hc c' hc' (smul_left_cancel g hp)
    refine ⟨galleryMap (g • ·) τ, IsJGallery.smul g hτ, ?_⟩
    rw [galleryEnd_galleryMap' (g • ·) rfl, hτe]
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩ hadj
    dsimp only at hadj ⊢
    rw [ptMap_smul, ptMap_smul, ptGraph_adj_smul] at hadj
    obtain ⟨c₁, hc₁, g₂, hg₂, h1, h2, h3⟩ := hedge c hc (ptMap S d) ⟨d, hd, rfl⟩ hadj
    refine ⟨g • c₁, ⟨c₁, hc₁, rfl⟩, g • g₂, ⟨g₂, hg₂, rfl⟩, ?_, ?_,
      (phanSystem_isMorphism_smul (S := S) g) 0 _ _ h3⟩
    · rw [ptMap_smul, ptMap_smul, h1]
    · rw [ptMap_smul, ptMap_smul, h2]
  · intro v hv
    obtain ⟨c, hc, hcv⟩ := hw v hv
    refine ⟨g • c, ⟨c, hc, rfl⟩, ?_⟩
    rw [ptMap_smul, hcv, smul_inv_smul]

end Smul

end CFSG.ClassicalInvolution.PhanQ
