module

public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.PositiveRootCollection

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

variable {τ : Tag}

theorem two_le_rank (τ : Tag) : 2 ≤ τ.rank := by
  cases τ <;> decide

variable (τ) in
theorem exists_isRoot_forall_height_le :
    ∃ θ, IsRoot τ θ ∧ ∀ γ, IsRoot τ γ → height γ ≤ height θ := by
  obtain ⟨θ, hθ, hmax⟩ := (rootFinset τ).exists_max_image height
    ⟨Pi.single ⟨0, τ.rank_pos⟩ 1, mem_rootFinset.2 (isRoot_single τ _)⟩
  exact ⟨θ, mem_rootFinset.1 hθ, fun γ hγ => hmax γ (mem_rootFinset.2 hγ)⟩

theorem height_pos_of_forall_height_le
    {θ : Fin τ.rank → ℤ}
    (hmax : ∀ γ, IsRoot τ γ → height γ ≤ height θ) : 0 < height θ := by
  have h := hmax _ (isRoot_single τ ⟨0, τ.rank_pos⟩)
  rw [height_single] at h
  omega

theorem not_isRoot_nsmul_add_nsmul_of_forall_height_le
    {θ β : Fin τ.rank → ℤ}
    (hmax : ∀ γ, IsRoot τ γ → height γ ≤ height θ) (hβp : 0 < height β) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ¬IsRoot τ (a • θ + b • β) := by
  intro h
  have h1 := hmax _ h
  have hθp := height_pos_of_forall_height_le hmax
  rw [height_nsmul_add_nsmul] at h1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem commute_pinnedX_of_forall_height_le
    (R : Type) [CommRing R] {θ β : Fin τ.rank → ℤ}
    (hθ : IsRoot τ θ) (hmax : ∀ γ, IsRoot τ γ → height γ ≤ height θ) (hβ : IsRoot τ β)
    (hβp : 0 < height β) (c d : R) :
    Commute (pinnedX τ R θ c) (pinnedX τ R β d) := by
  by_cases hθβ : θ = β
  · subst hθβ
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · have hc := commutator_rootSubgroup_le R hθ hβ (height_pos_of_forall_height_le hmax) hβp hθβ
    have hbot : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
        ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • θ + b • β), rootSubgroup τ R γ) = ⊥ := by
      refine iSup₂_eq_bot.2 ?_
      rintro γ ⟨hγ, a, b, ha, hb, rfl⟩
      exact absurd hγ (not_isRoot_nsmul_add_nsmul_of_forall_height_le hmax hβp ha hb)
    rw [hbot] at hc
    have hmem := hc (Subgroup.commutator_mem_commutator (mem_rootSubgroup.2 ⟨c, rfl⟩)
      (mem_rootSubgroup.2 ⟨d, rfl⟩))
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

section CharTwo

variable {K : Type} [Field K]

theorem pinnedX_one_mul_self
    (h2 : (2 : K) = 0) (α : Fin τ.rank → ℤ) :
    pinnedX τ K α 1 * pinnedX τ K α 1 = 1 := by
  rw [← pinnedX_add, one_add_one_eq_two, h2, pinnedX_zero]

theorem pinnedX_one_ne_one
    (α : Fin τ.rank → ℤ) : pinnedX τ K α 1 ≠ 1 := fun h =>
  one_ne_zero (pinnedX_injective τ K α (h.trans (pinnedX_zero τ K α).symm))

theorem pinnedX_one_ne_pinnedX_one
    {θ β : Fin τ.rank → ℤ} (hθ : IsRoot τ θ ∧ 0 < height θ)
    (hβ : IsRoot τ β ∧ 0 < height β) (hne : θ ≠ β) :
    pinnedX τ K θ 1 ≠ pinnedX τ K β 1 := fun h => by
  have hinj : Function.Injective ![θ, β] := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  have hpos : ∀ i, IsRoot τ (![θ, β] i) ∧ 0 < height (![θ, β] i) := by
    intro i
    fin_cases i
    · exact hθ
    · exact hβ
  have key := (positive_root_product_injectivity τ K ![θ, β] hinj hpos).2
    (a₁ := ![1, 0]) (a₂ := ![0, 1]) (by
      simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
        Matrix.cons_val_zero, Matrix.cons_val_succ, pinnedX_zero, one_mul]
      exact h)
  have := congrFun key 0
  simp at this

theorem entrywise_pinnedX_one
    (δ : K →+* K) (α : Fin τ.rank → ℤ) :
    entrywise δ (pinnedX τ K α 1 : Module.End K (RootModule τ K)) = pinnedX τ K α 1 := by
  rw [entrywise_pinnedX, map_one]

theorem entrywise_eq_of_mem_kleinFourOf {x y : ModGL τ K} {hx : x * x = 1} {hy : y * y = 1}
    {hxy : x * y = y * x} (δ : K →+* K)
    (hδx : entrywise δ (x : Module.End K (RootModule τ K)) = x)
    (hδy : entrywise δ (y : Module.End K (RootModule τ K)) = y) {g : ModGL τ K}
    (hg : g ∈ FourGroup.kleinFourOf x y hx hy hxy) :
    entrywise δ (g : Module.End K (RootModule τ K)) = g := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact entrywise_one δ
  · exact hδx
  · exact hδy
  · rw [Units.val_mul, entrywise_mul, hδx, hδy]

end CharTwo

theorem even_Chevalley_coordinate_fields_fixed_four_group
    (τ : Tag) (K : Type) [Field K]
    (hK : ringChar K = 2) :
    ∃ A : Subgroup (ModGL τ K), A ≤ adjointGroup τ K ∧ CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 4 ∧
      ∀ δ : K →+* K, ∀ g ∈ A, entrywise δ (g : Module.End K (RootModule τ K)) = g := by
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := ringChar.of_eq hK
    exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨θ, hθ, hmax⟩ := exists_isRoot_forall_height_le τ
  obtain ⟨j, hj⟩ : ∃ j : Fin τ.rank, (Pi.single j 1 : Fin τ.rank → ℤ) ≠ θ := by
    by_contra! h
    have h01 := (h ⟨0, τ.rank_pos⟩).trans (h ⟨1, two_le_rank τ⟩).symm
    have := congrFun h01 ⟨0, τ.rank_pos⟩
    simp at this
  have hβ : IsRoot τ (Pi.single j 1) ∧ 0 < height (Pi.single j 1 : Fin τ.rank → ℤ) :=
    ⟨isRoot_single τ j, by rw [height_single]; omega⟩
  have hxy : pinnedX τ K θ 1 * pinnedX τ K (Pi.single j 1) 1 =
      pinnedX τ K (Pi.single j 1) 1 * pinnedX τ K θ 1 :=
    commute_pinnedX_of_forall_height_le K hθ hmax hβ.1 hβ.2 1 1
  obtain ⟨A, hAmem, hAle, hA, hAcard⟩ := FourGroup.exists_kleinFour (pinnedX_one_mul_self h2 θ)
    (pinnedX_one_mul_self h2 _) hxy (pinnedX_one_ne_one θ) (pinnedX_one_ne_one _)
    (pinnedX_one_ne_pinnedX_one ⟨hθ, height_pos_of_forall_height_le hmax⟩ hβ (Ne.symm hj))
  refine ⟨A, hAle _ (pinnedX_mem_adjointGroup θ 1) (pinnedX_mem_adjointGroup _ 1), hA, hAcard,
    fun δ g hg => ?_⟩
  rcases hAmem g hg with rfl | rfl | rfl | rfl
  · exact entrywise_one δ
  · exact entrywise_pinnedX_one δ θ
  · exact entrywise_pinnedX_one δ _
  · rw [Units.val_mul, entrywise_mul, entrywise_pinnedX_one, entrywise_pinnedX_one]

end CFSG.LieType.Chevalley
