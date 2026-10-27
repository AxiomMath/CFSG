module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Rank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Comb

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def GoodU (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) : Prop :=
  x ≠ 0 ∧ finrank K (fixOf ρ {x}) + 8 ≤ finrank K V

theorem cover_eight [CharP K 2] [FiniteDimensional K V] (ρ : Multiplicative Z3 →* Module.End K V)
    (hfaith : ∀ x, act ρ x = 1 → x = 0)
    (hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})))
    (hp0 : Even (finrank K (fixOf ρ Set.univ))) (h8 : 8 ≤ finrank K V) :
    (⊤ : Submodule K V) ≤ (⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x}) ⊔
      ⨆ x ∈ {x | GoodU ρ x}, LinearMap.ker (eCyc ρ x) := by
  classical
  set r₀ := finrank K (LinearMap.range (e0 ρ)) with hr₀def
  set r : Z3 → ℕ := fun φ => finrank K (LinearMap.range (isoP ρ φ)) with hrdef
  have hr₀ : Even r₀ := by rw [hr₀def, range_e0]; exact hp0
  have hr : ∀ φ ∈ Rset, Even (r φ) := by
    intro φ hφ
    have h1 := hpN φ hφ
    rw [finrank_fixOf_N_eq ρ hφ] at h1
    exact (Nat.even_add.1 h1).1 hr₀
  have hN : finrank K V = r₀ + ∑ φ ∈ Rset, r φ := finrank_eq_sum_isoP ρ
  have hF : ∀ x, finrank K (fixOf ρ {x}) = lineSum r₀ r x := fun x =>
    finrank_fixOf_single_eq ρ x
  have hsub_fix : ∀ φ ∈ Rset, ∀ x, dot φ x = 0 → LinearMap.range (isoP ρ φ) ≤ fixOf ρ {x} := by
    rintro φ - x hx _ ⟨w, rfl⟩
    have h1 := eCyc_isoP ρ φ x w
    simp only [hx, ↓reduceIte] at h1
    rw [← h1]
    exact eCyc_mem_fixOf ρ x _
  have hsub_ker : ∀ φ ∈ Rset, ∀ x, dot φ x ≠ 0 →
      LinearMap.range (isoP ρ φ) ≤ LinearMap.ker (eCyc ρ x) := by
    rintro φ - x hx _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, eCyc_isoP]
    simp only [hx, ↓reduceIte]
  have hmoved : ∀ φ ∈ Rset, r φ ≠ 0 →
      ∃ y : Z3, ∃ u ∈ LinearMap.range (isoP ρ φ), act ρ y u ≠ u := by
    intro φ hφ hr0
    have hne : LinearMap.range (isoP ρ φ) ≠ ⊥ := fun h => hr0 (by
      show finrank K (LinearMap.range (isoP ρ φ)) = 0
      rw [h, finrank_bot])
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    by_contra hall
    push Not at hall
    obtain ⟨w, rfl⟩ := hu
    apply hu0
    have h1 : e0 ρ (isoP ρ φ w) = isoP ρ φ w :=
      e0_of_mem ρ fun y _ => hall y _ ⟨w, rfl⟩
    rw [← h1, e0_isoP ρ hφ]
  have hgood_of : ∀ φ ∈ Rset, r φ ≠ 0 → ∀ x ∈ Rset, dot φ x = 0 →
      6 ≤ finrank K (fixOf ρ {x}) → GoodSix ρ x := by
    intro φ hφ hr0 x hxR hx h6
    obtain ⟨y, u, hu, hyu⟩ := hmoved φ hφ hr0
    exact ⟨ne_zero_of_mem_Rset x hxR, h6, y, u, hsub_fix φ hφ x hx hu, hyu⟩
  have hex : ∃ ψ ∈ Rset, r ψ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : finrank K V = r₀ := by
      rw [hN, Finset.sum_eq_zero hall, add_zero]
    have h2 : fixOf ρ Set.univ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← range_e0, ← hr₀def, h1]
    have h3 : act ρ ![1, 0, 0] = 1 := LinearMap.ext fun v => by
      have : v ∈ fixOf ρ Set.univ := h2 ▸ Submodule.mem_top
      exact this _ (Set.mem_univ _)
    have h4 := congrFun (hfaith _ h3) 0
    simp at h4
  intro v _
  rw [← e0_add_sum_isoP ρ v]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun φ hφ => ?_)
  ·
    by_cases h0 : r₀ = 0
    · have : LinearMap.range (e0 ρ) = ⊥ := Submodule.finrank_eq_zero.1 h0
      have hv : e0 ρ v = 0 := by
        have h1 : e0 ρ v ∈ LinearMap.range (e0 ρ) := ⟨v, rfl⟩
        rw [this, Submodule.mem_bot] at h1
        exact h1
      rw [hv]
      exact Submodule.zero_mem _
    obtain ⟨ψ, hψ, hrψ⟩ := hex
    rcases exists_line_of_ne_zero hr₀ hr (by rw [← hN]; exact h8) hψ hrψ with
      ⟨x, hxR, hxψ, h6⟩ | ⟨h0', -⟩
    · rw [← hF x] at h6
      have hgood := hgood_of ψ hψ hrψ x hxR hxψ h6
      refine (le_sup_left : (⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x}) ≤ _) ?_
      have hle : fixOf ρ {x} ≤ ⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x} :=
        le_iSup₂_of_le x hgood le_rfl
      exact hle (fixOf_univ_le ρ {x} (e0_mem_fixOf ρ _ v))
    · exact absurd h0' h0
  ·
    by_cases h0 : r φ = 0
    · have : LinearMap.range (isoP ρ φ) = ⊥ := Submodule.finrank_eq_zero.1 h0
      have hv : isoP ρ φ v = 0 := by
        have h1 : isoP ρ φ v ∈ LinearMap.range (isoP ρ φ) := ⟨v, rfl⟩
        rw [this, Submodule.mem_bot] at h1
        exact h1
      rw [hv]
      exact Submodule.zero_mem _
    rcases exists_line_of_ne_zero hr₀ hr (by rw [← hN]; exact h8) hφ h0 with
      ⟨x, hxR, hxφ, h6⟩ | ⟨-, x, hxR, hxφ, h8x⟩
    · rw [← hF x] at h6
      have hgood := hgood_of φ hφ h0 x hxR hxφ h6
      refine (le_sup_left : (⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x}) ≤ _) ?_
      have hle : fixOf ρ {x} ≤ ⨆ x ∈ {x | GoodSix ρ x}, fixOf ρ {x} :=
        le_iSup₂_of_le x hgood le_rfl
      exact hle (hsub_fix φ hφ x hxφ ⟨v, rfl⟩)
    · rw [← hF x, ← hN] at h8x
      have hgood : GoodU ρ x := ⟨ne_zero_of_mem_Rset x hxR, h8x⟩
      refine (le_sup_right : (⨆ x ∈ {x | GoodU ρ x}, LinearMap.ker (eCyc ρ x)) ≤ _) ?_
      have hle : LinearMap.ker (eCyc ρ x) ≤ ⨆ x ∈ {x | GoodU ρ x}, LinearMap.ker (eCyc ρ x) :=
        le_iSup₂_of_le x hgood le_rfl
      exact hle (hsub_ker φ hφ x hxφ ⟨v, rfl⟩)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
