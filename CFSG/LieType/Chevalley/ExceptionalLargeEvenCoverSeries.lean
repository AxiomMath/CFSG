module

public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverHeight
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverArith
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivial

public noncomputable section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def series
    (i : ℕ) : Subgroup (ModGL τ K) :=
  heightSeries τ K (maxHeight τ + 1 - i)

theorem series_succ
    (i : ℕ) : series τ K (i + 1) = heightSeries τ K (maxHeight τ - i) := by
  rw [series]
  congr 1
  push_cast
  ring

theorem series_eq
    (i : ℕ) : series τ K i = heightSeries τ K ((maxHeight τ - i) + 1) := by
  rw [series]
  congr 1
  ring

theorem toNat_maxHeight
    : ((maxHeight τ).toNat : ℤ) = maxHeight τ :=
  Int.toNat_of_nonneg (by linarith [one_le_maxHeight τ])

variable [Finite K] [CharP K 2]

theorem ker_eq_bot_of_adjointGroup
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* adjointGroup τ K) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have := finite_modGL (τ := τ) (K := K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
    (card_posUnipotent (τ := τ) (K := K))
  have hχ : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → 0 < height β → rootChar K β ≠ 1 :=
    fun β hβ hβp => rootChar_ne_one hK (exists_not_dvd_cartanCoord hτ (by omega) hβ hβp)
  have hT := odd_card_torus (τ := τ) hK (by omega)
  refine ker_eq_bot_of_coprime_central_series η hη hC h2 (U := posUnipotent τ K)
    posUnipotent_le_adjointGroup hUp hUi hT (torusVec τ K) torusVec_mem_adjointGroup
    (fun t x hx => torusVec_conj_mem_rootSpan t (fun _ hα => hα.1) hx)
    (maxHeight τ).toNat (series τ K) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    intro h₁ h₂ _ _ h₅
    exact form_eq_zero_of_heightSeries (by omega) hK
      (fun α β hα hαp hβ hβp i' j' hi' hj' => pair_not_dvd hτ hf hα hαp hβ hβp i' j' hi' hj')
      _ _ b h₁ h₂ h₅

end CFSG.LieType.Chevalley.ExceptionalCover

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley ExceptionalCover

theorem untwisted_large_even_central_two_cover_trivial
    {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {E : Type*} {J : Type} [Group E]
    [Group J] [Finite E] [Group.IsPerfect E] (η : E →* J) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) {f : ℕ} (hf : 3 ≤ f)
    (hJ : UntwistedChevalleyModel J τ (2 ^ f)) : η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hJ
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  set η' : E →* adjointGroup τ K := e.toMonoidHom.comp η with hη'
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_adjointGroup hτ hf hK η' (e.surjective.comp hη) (hker' ▸ hC)
    (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end CFSG.LieType.Chevalley
