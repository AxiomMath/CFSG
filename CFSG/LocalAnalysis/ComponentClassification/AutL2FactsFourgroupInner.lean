module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupA7
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup Equiv

variable {F : Type} [Field F] [Finite F]

theorem sqLeft_of_involution (hodd : IsOddPrimePower (Nat.card F)) {x : PGammaL2 F}
    (hx : orderOf x = 2) (hr : x.right ≠ 1) : SqLeft x := by
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hodd x hx hr
  have hx' : x = SemidirectProduct.inl C * SemidirectProduct.inr x.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]
    group
  have hσ : SqLeft (SemidirectProduct.inr x.right : PGammaL2 F) := ⟨1, by simp⟩
  rw [hx', sqLeft_mul, sqLeft_mul, sqLeft_inv]
  tauto

theorem exists_two_ne_of_card_four {G : Type*} [Group G] (W : Subgroup G) (hW4 : Nat.card W = 4) :
    ∃ x ∈ W, ∃ y ∈ W, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  classical
  have : Finite W := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype W := Fintype.ofFinite W
  have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : W)
  obtain ⟨y, hy1, hyx⟩ : ∃ y : W, y ≠ 1 ∧ y ≠ x := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset W) ⊆ {1, x} := by
      intro w _
      by_cases hw : w = 1
      · simp [hw]
      · simp [h w hw]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hW4] at this
    have h2 : ({1, x} : Finset W).card ≤ 2 := Finset.card_le_two
    omega
  exact ⟨x, x.2, y, y.2, fun h => hx1 (Subtype.ext h), fun h => hy1 (Subtype.ext h),
    fun h => hyx (Subtype.ext h).symm⟩

theorem fourgroup_meets_psl (hodd : IsOddPrimePower (Nat.card F)) (W : Subgroup (PGammaL2 F))
    (hW2 : ∀ w ∈ W, w * w = 1) (hW4 : Nat.card W = 4) :
    ∃ w ∈ W, w ≠ 1 ∧ w ∈ pGammaL2PSLRange F := by
  obtain ⟨x, hxW, y, hyW, hx1, hy1, hxy⟩ := exists_two_ne_of_card_four W hW4
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxy
    have := hW2 x hxW
    calc x = x * (x * y) := by rw [h, mul_one]
      _ = y := by rw [← mul_assoc, this, one_mul]
  by_contra hcon
  push Not at hcon
  have htype : ∀ w ∈ W, w ≠ 1 →
      (w.right = 1 ∧ ¬ SqLeft w) ∨ (w.right ≠ 1 ∧ SqLeft w) := by
    intro w hw hw1
    have hnot := hcon w hw hw1
    rw [mem_pslRange_iff] at hnot
    by_cases hr : w.right = 1
    · exact Or.inl ⟨hr, fun h => hnot ⟨hr, h⟩⟩
    · exact Or.inr ⟨hr, sqLeft_of_involution hodd
        (orderOf_eq_prime (by rw [pow_two]; exact hW2 w hw) hw1) hr⟩
  have hsq : ∀ w ∈ W, w.right ^ 2 = 1 := fun w hw => by
    rw [pow_two]
    have := congrArg SemidirectProduct.right (hW2 w hw)
    simpa using this
  have hxyW := mul_mem hxW hyW
  have hr3 : (x * y).right = x.right * y.right := rfl
  have hs3 := sqLeft_mul x y
  rcases htype x hxW hx1 with ⟨hxr, hxs⟩ | ⟨hxr, hxs⟩ <;>
    rcases htype y hyW hy1 with ⟨hyr, hys⟩ | ⟨hyr, hys⟩ <;>
    rcases htype (x * y) hxyW hxy1 with ⟨hzr, hzs⟩ | ⟨hzr, hzs⟩
  all_goals try (rw [hr3] at hzr)
  all_goals try (simp only [hxr, hyr, one_mul, mul_one, ne_eq, not_true_eq_false] at hzr)
  all_goals try tauto
  · have : IsCyclic (F ≃+* F) := isCyclic_ringAut F
    rcases eq_one_or_eq_of_sq_eq_one_cyclic (hsq x hxW) hxr (hsq y hyW) with h | h
    · exact hyr h
    · rw [h] at hzr
      apply hzr
      have := hsq x hxW
      rwa [pow_two] at this

theorem footeFourgroupInner :
    ∀ (S : Type) [Group S] [Finite S],
      (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
      ∀ W : Subgroup (MulAut S), (∀ w ∈ W, w * w = 1) → Nat.card W = 4 →
        ∃ w ∈ W, w ≠ 1 ∧ w ∈ (MulAut.conj : S →* MulAut S).range := by
  intro S _ _ hS W hW2 hW4
  rcases hS with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  ·
    obtain ⟨x, hxW, y, hyW, hx1, hy1, hxy⟩ := exists_two_ne_of_card_four W hW4
    have hinner : ∀ w : MulAut S, ∀ π : Perm (Fin 7), a7Conj π = MulAut.congr e w →
        π ∈ alternatingGroup (Fin 7) → w ∈ (MulAut.conj : S →* MulAut S).range := by
      intro w π hπ hπA
      refine ⟨e.symm ⟨π, hπA⟩, (MulAut.congr e).injective ?_⟩
      rw [congr_conj_eq, MulEquiv.apply_symm_apply, ← hπ, a7Conj_of_mem hπA]
    obtain ⟨π₁, hπ₁⟩ := exists_a7Conj_eq (MulAut.congr e x)
    obtain ⟨π₂, hπ₂⟩ := exists_a7Conj_eq (MulAut.congr e y)
    by_cases h₁ : π₁ ∈ alternatingGroup (Fin 7)
    · exact ⟨x, hxW, hx1, hinner x π₁ hπ₁ h₁⟩
    by_cases h₂ : π₂ ∈ alternatingGroup (Fin 7)
    · exact ⟨y, hyW, hy1, hinner y π₂ hπ₂ h₂⟩
    refine ⟨x * y, mul_mem hxW hyW, fun h => hxy ?_, hinner _ (π₁ * π₂) ?_ ?_⟩
    · have := hW2 x hxW
      calc x = x * (x * y) := by rw [h, mul_one]
        _ = y := by rw [← mul_assoc, this, one_mul]
    · rw [map_mul, map_mul, hπ₁, hπ₂]
    · rw [Perm.mem_alternatingGroup] at h₁ h₂ ⊢
      rw [Perm.sign_mul]
      rcases Int.units_eq_one_or (Perm.sign π₁) with h | h
      · exact absurd h h₁
      rcases Int.units_eq_one_or (Perm.sign π₂) with h' | h'
      · exact absurd h' h₂
      rw [h, h']
      decide
  ·
    obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
    have hodd := isOddPrimePower_of hp hp2 hf hF
    set Φ := autEquiv e
    obtain ⟨_, ⟨w, hwW, rfl⟩, hw1, hwL⟩ := fourgroup_meets_psl hodd (W.map Φ.toMonoidHom)
      (by
        rintro _ ⟨w, hw, rfl⟩
        change Φ w * Φ w = 1
        rw [← map_mul, hW2 w hw, map_one])
      (by rw [Subgroup.card_map_of_injective Φ.injective, hW4])
    refine ⟨w, hwW, fun h => hw1 (by rw [h]; exact map_one _), ?_⟩
    rw [← map_autEquiv_innAut e] at hwL
    obtain ⟨β, hβ, hβw⟩ := hwL
    rwa [← Φ.injective hβw]

end CFSG.ComponentClassification.AutL2Facts
