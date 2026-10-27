module

public import CFSG.LieType.Chevalley.ExceptionalFieldFourCoverLifts
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverSeries
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverCommuting

public noncomputable section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem form_eq_zero_of_rootPairs
    (h h' : ℤ) (b : ModGL τ K → ModGL τ K → ZMod 2)
    (hb₁ : ∀ x ∈ heightSeries τ K h, ∀ x' ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h',
      b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h', ∀ y' ∈ heightSeries τ K h',
      b x (y * y') = b x y + b x y')
    (hroot : ∀ α ∈ heightSet τ h, ∀ β ∈ heightSet τ h', ∀ c d : K,
      b (pinnedX τ K α c) (pinnedX τ K β d) = 0) :
    ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h', b x y = 0 := by
  have hleft : ∀ α ∈ heightSet τ h, ∀ c : K, ∀ y ∈ heightSeries τ K h',
      b (pinnedX τ K α c) y = 0 := by
    intro α hα c y hy
    rw [heightSeries_eq_closure] at hy
    refine eq_zero_of_closure (b (pinnedX τ K α c)) (fun y hy y' hy' => ?_) ?_ y hy
    · rw [← heightSeries_eq_closure] at hy hy'
      exact hb₂ _ (pinnedX_mem_heightSeries hα _) _ hy _ hy'
    · rintro _ ⟨β, hβ, d, rfl⟩
      exact hroot α hα β hβ c d
  intro x hx y hy
  rw [heightSeries_eq_closure] at hx
  refine eq_zero_of_closure (fun x => b x y) (fun x hx x' hx' => ?_) ?_ x hx
  · rw [← heightSeries_eq_closure] at hx hx'
    exact hb₁ _ hx _ hx' _ hy
  · rintro _ ⟨α, hα, c, rfl⟩
    exact hleft α hα c y hy

theorem form_pinnedX_eq_zero
    [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (h h' : ℤ) (b : ModGL τ K → ModGL τ K → ZMod 2)
    (hb₁ : ∀ x ∈ heightSeries τ K h, ∀ x' ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h',
      b (x * x') y = b x y + b x' y)
    (hb₂ : ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h', ∀ y' ∈ heightSeries τ K h',
      b x (y * y') = b x y + b x y')
    (hb₅ : ∀ (t : Fin τ.rank → Kˣ), ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h',
      b (torusVec τ K t * x * (torusVec τ K t)⁻¹) (torusVec τ K t * y * (torusVec τ K t)⁻¹) =
        b x y)
    {α β : Fin τ.rank → ℤ} (hα : α ∈ heightSet τ h) (hβ : β ∈ heightSet τ h')
    (harith : ∀ i j : ℕ, i < f → j < f →
      ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k) (c d : K) :
    b (pinnedX τ K α c) (pinnedX τ K β d) = 0 := by
  refine rootChar_form_eq_zero hf hK harith
    (fun c d => b (pinnedX τ K α c) (pinnedX τ K β d)) (fun c₁ c₂ d => ?_)
    (fun c d₁ d₂ => ?_) (fun t c d => ?_) c d
  · rw [pinnedX_add]
    exact hb₁ _ (pinnedX_mem_heightSeries hα _) _ (pinnedX_mem_heightSeries hα _) _
      (pinnedX_mem_heightSeries hβ _)
  · rw [pinnedX_add]
    exact hb₂ _ (pinnedX_mem_heightSeries hα _) _ (pinnedX_mem_heightSeries hβ _) _
      (pinnedX_mem_heightSeries hβ _)
  · rw [← torusVec_conj_pinnedX hα.1, ← torusVec_conj_pinnedX hβ.1]
    exact hb₅ t _ (pinnedX_mem_heightSeries hα _) _ (pinnedX_mem_heightSeries hβ _)

variable (τ K) in
@[expose] def posRootGroup
    (δ : Fin τ.rank → ℤ) : Set (ModGL τ K) :=
  {g | IsRoot τ δ ∧ 0 < height δ ∧ ∃ c : K, g = pinnedX τ K δ c}

theorem posRootGroup_subset
    (δ : Fin τ.rank → ℤ) : posRootGroup τ K δ ⊆ posUnipotent τ K := by
  rintro _ ⟨hδ, hδp, c, rfl⟩
  exact (le_iSup₂_of_le δ ⟨hδ, hδp⟩ le_rfl : rootSubgroup τ K δ ≤ posUnipotent τ K)
    (Subgroup.subset_closure ⟨c, rfl⟩)

variable [Finite K] [CharP K 2]

theorem ker_eq_bot_of_adjointGroup_four
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hK : Nat.card K = 2 ^ 2) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* adjointGroup τ K) (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have := finite_modGL (τ := τ) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
    (card_posUnipotent (τ := τ) (K := K))
  have hχ : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → 0 < height β → rootChar K β ≠ 1 :=
    fun β hβ hβp => rootChar_ne_one hK (exists_not_dvd_cartanCoord hτ' le_rfl hβ hβp)
  have hT := odd_card_torus (τ := τ) hK (by norm_num)
  refine ker_eq_bot_of_coprime_central_series_of_commute η hη hC h2 (U := posUnipotent τ K)
    posUnipotent_le_adjointGroup hUp hUi hT (torusVec τ K) torusVec_mem_adjointGroup
    (fun t x hx => torusVec_conj_mem_rootSpan t (fun _ hα => hα.1) hx)
    (maxHeight τ).toNat (series τ K) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (posRootGroup τ K) (posRootGroup τ K)
    posRootGroup_subset posRootGroup_subset ?_ ?_
  ·
    rw [series, Nat.cast_zero, sub_zero, heightSeries_maxHeight_add_one]
  ·
    rw [series, toNat_maxHeight, add_sub_cancel_left, heightSeries_one]
  ·
    intro i _
    rw [series_succ, series_eq]
    exact heightSeries_antitone (by omega)
  ·
    intro i _ t x hx
    exact torusVec_conj_mem_heightSeries t hx
  ·
    intro i _ x hx g hg
    rw [series_succ] at hx
    rw [series_eq]
    rw [← heightSeries_one] at hg
    have hc := commutator_heightSeries_le K (maxHeight τ - i) 1
      (Subgroup.commutator_mem_commutator (inv_mem hx) (inv_mem hg))
    rwa [commutatorElement_def, inv_inv, inv_inv] at hc
  ·
    intro i _ x hx
    rw [series_succ] at hx
    rw [series_eq]
    exact sq_mem_heightSeries_succ hx
  ·
    intro i _ x hx hfix
    rw [series_succ] at hx
    rw [series_eq] at hfix ⊢
    exact mem_heightSeries_succ_of_forall hT hχ hx hfix
  ·
    intro i _ j _ b
    rw [series_succ, series_succ]
    intro h₁ h₂ _ _ h₅ h₆
    refine form_eq_zero_of_rootPairs _ _ b h₁ h₂ fun α hα β hβ c d => ?_
    by_cases hab : α = β
    · subst hab
      exact h₆ α _ ⟨hα.1, hα.2.1, c, rfl⟩ _ ⟨hα.1, hα.2.1, d, rfl⟩
    · exact form_pinnedX_eq_zero (by norm_num) hK _ _ b h₁ h₂ h₅ hα hβ
        (fun i' j' hi' hj' => cross_not_dvd hτ hα.1 hα.2.1 hβ.1 hβ.2.1 hab i' j' hi' hj') c d
  ·
    rintro δ a y ⟨-, -, c, hc⟩ ⟨-, -, d, hd⟩
    exact lift_commute_root hη hC hτ hK δ a y ⟨c, hc⟩ ⟨d, hd⟩

end CFSG.LieType.Chevalley.ExceptionalCover

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley ExceptionalCover
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem untwisted_field_four_central_two_cover_trivial
    {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {E : Type*} {J : Type} [Group E] [Group J]
    [Finite E] [Group.IsPerfect E] (η : E →* J) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    (hJ : UntwistedChevalleyModel J τ (2 ^ 2)) : η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hJ
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  set η' : E →* adjointGroup τ K := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_adjointGroup_four hτ hK η' (e.surjective.comp hη) (hker' ▸ hC)
    (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

theorem ordinary_exceptional_field_four_central_two_cover_trivial
    {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hJ : LieModel J t 0 2 2) : η.ker = ⊥ ∧ Function.Bijective η := by
  rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · rcases ht with rfl | rfl | rfl | rfl <;> exact absurd hc (by decide)
  · rcases ht with rfl | rfl | rfl | rfl
    · exact untwisted_field_four_central_two_cover_trivial (Or.inl rfl) η hη hC h2 hX.2
    · exact untwisted_field_four_central_two_cover_trivial (Or.inr (Or.inl rfl)) η hη hC h2 hX.2
    · exact untwisted_field_four_central_two_cover_trivial (Or.inr (Or.inr (Or.inl rfl))) η hη
        hC h2 hX.2
    · exact untwisted_field_four_central_two_cover_trivial (Or.inr (Or.inr (Or.inr rfl))) η hη
        hC h2 hX.2
  · rcases ht with rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  · rcases ht with rfl | rfl | rfl | rfl <;> exact absurd hs (by decide)

end CFSG.LieType.Chevalley
