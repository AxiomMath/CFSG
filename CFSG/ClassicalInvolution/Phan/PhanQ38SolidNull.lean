module

public import CFSG.ClassicalInvolution.Phan.PhanG9Fib

public section

namespace CFSG.ClassicalInvolution.PhanQ


open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G}

@[expose] noncomputable def solidFib (h0 : PtStep0 S) (J₀ : Set (Fin 4)) (hJ₀ : (0 : Fin 4) ∈ J₀)
    (R : Set (G ⧸ torusSub S))
    (hR : ∀ {i : Fin 4} {e g : G ⧸ torusSub S}, i ∈ J₀ → (phanSystem S).adj i e g → e ∈ R →
      g ∈ R) :
    Fib (phanSystem S) (ptGraph S) where
  P := ptMap S
  a := 0
  J' := {i | i ∈ J₀ ∧ i ≠ 0}
  Q := fun e => e ∈ R
  step_Q := fun {i e g} hi hadj he => by
    rcases hi with rfl | hi
    · exact hR hJ₀ hadj he
    · exact hR hi.1 hadj he
  step_P := fun {i e g} hi hadj _ => by
    have hi' : i ∈ ({1, 2, 3} : Set (Fin 4)) := by
      obtain ⟨-, hne⟩ := hi
      fin_cases i <;> simp_all
    exact (ptMap_eq_iff e g).2 (residue_mono (Set.singleton_subset_iff.2 hi') e
      (mem_residue_singleton.2 hadj))
  step_a := fun {e g} hadj _ => by
    by_cases h : ptMap S e = ptMap S g
    · exact Or.inl (h0 hadj h)
    · exact Or.inr (ptGraph_adj_of_adj hadj h)

theorem solidNull_of_points (h0 : PtStep0 S) {J₀ : Set (Fin 4)}
    (hJ₀ : J₀ = {0, 1, 2} ∨ J₀ = {0, 1, 3}) (R : Set (G ⧸ torusSub S))
    (hR : ∀ {i : Fin 4} {e g : G ⧸ torusSub S}, i ∈ J₀ → (phanSystem S).adj i e g → e ∈ R →
      g ∈ R)
    (hip : ∀ c ∈ R, ∀ c' ∈ R, ptMap S c = ptMap S c' →
      ∃ τ, IsJGallery (phanSystem S) {i | i ∈ J₀ ∧ i ≠ 0} c τ ∧ galleryEnd c τ = c')
    (hedge : ∀ c ∈ R, ∀ y ∈ ptMap S '' R, (ptGraph S).Adj (ptMap S c) y →
      ∃ c₁ ∈ R, ∃ g ∈ R, ptMap S c₁ = ptMap S c ∧ ptMap S g = y ∧ (phanSystem S).adj 0 c₁ g)
    {x : G ⧸ parab S {1, 2, 3}} (w : (ptGraph S).Walk x x)
    (hw : ∀ v ∈ w.support, v ∈ ptMap S '' R) : SolidNull S h0 w := by
  have hJ0 : (0 : Fin 4) ∈ J₀ := by rcases hJ₀ with rfl | rfl <;> simp
  let F := solidFib h0 J₀ hJ0 R hR
  obtain ⟨c₁, hc₁, hc₁x⟩ := hw x (by simp)
  have hlift : ∀ {e : G ⧸ torusSub S} {x' : G ⧸ parab S {1, 2, 3}}, F.Q e →
      (fun v => v ∈ ptMap S '' R) (F.P e) → (fun v => v ∈ ptMap S '' R) x' →
      (ptGraph S).Adj (F.P e) x' →
      ∃ (ρ : List (Fin 4 × G ⧸ torusSub S)) (g : G ⧸ torusSub S),
        IsJGallery (phanSystem S) F.J' e ρ ∧ (phanSystem S).adj F.a (galleryEnd e ρ) g ∧
          F.P g = x' ∧ F.Q g := by
    intro e x' he _ hx' hadj
    obtain ⟨c₂, hc₂, g, hg, hP₂, hPg, hadj0⟩ := hedge e he x' hx' hadj
    obtain ⟨τ, hτ, hτe⟩ := hip e he c₂ hc₂ hP₂.symm
    exact ⟨τ, g, hτ, by rw [hτe]; exact hadj0, hPg, hg⟩
  obtain ⟨γ, hγ⟩ := F.exists_lift (D := fun v => v ∈ ptMap S '' R) hlift w hw c₁ hc₁ hc₁x
  have hsub : F.J' ⊆ (phanFib S h0).J' := fun i hi => by
    obtain ⟨-, hne⟩ := hi
    fin_cases i <;> simp_all [phanFib]
  have hγ' : (phanFib S h0).Lift w c₁ γ :=
    Fib.Lift.mono (F := F) (F' := phanFib S h0) rfl rfl hsub hγ
  have hQe : F.Q (galleryEnd c₁ γ) := hγ.Q_galleryEnd hc₁
  have hPe : F.P (galleryEnd c₁ γ) = x := hγ.end_eq hc₁
  obtain ⟨τ₁, hτ₁, hτ₁e⟩ := hip _ hQe c₁ hc₁
    (by rw [show ptMap S (galleryEnd c₁ γ) = x from hPe, hc₁x])
  refine ⟨J₀, hJ₀, c₁, γ, τ₁, hγ', ?_, ?_, ?_, hτ₁e⟩
  · intro i hi
    have := (hγ.isJGallery).2 i hi
    rcases this with rfl | hi'
    · exact hJ0
    · exact hi'.1
  · exact IsJGallery.mono hsub hτ₁
  · intro i hi
    exact (hτ₁.2 i hi).1

end CFSG.ClassicalInvolution.PhanQ
