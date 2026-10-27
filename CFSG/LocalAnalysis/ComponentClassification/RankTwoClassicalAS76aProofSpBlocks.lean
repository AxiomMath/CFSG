module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviProj
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped MatrixGroups

section Blocks

variable {K : Type} [Field K] {m : ℕ}

variable (K m) in
@[expose] noncomputable def spW : SL(2, K) →* StatedSp (m + 1) K :=
  longBlock K (m + 1) (Fin.last m)

variable (K m) in
@[expose] noncomputable def spL : StatedSp m K →* StatedSp (m + 1) K :=
  spEmbed Fin.castSucc (Fin.castSucc_injective m)

theorem range_spW : (spW K m).range = suppGroup (coords (Fin.last m)) := range_longBlock _

theorem range_spL : (spL K m).range = suppGroup (coords (Fin.last m))ᶜ := by
  rw [spL, range_spEmbed, ← range_succAbove (Fin.last m), Fin.succAbove_last]

theorem spW_commute_spL (X : SL(2, K)) (S : StatedSp m K) :
    spW K m X * spL K m S = spL K m S * spW K m X := by
  have h1 : spW K m X ∈ suppGroup (coords (Fin.last m)) := by
    rw [← range_spW]
    exact ⟨X, rfl⟩
  have h2 : spL K m S ∈ suppGroup (coords (Fin.last m))ᶜ := by
    rw [← range_spL]
    exact ⟨S, rfl⟩
  exact commute_suppGroup_compl h1 h2

variable (K m) in
@[expose] noncomputable def spBarW : Subgroup (StatedProj (StatedSp (m + 1) K)) :=
  ((proj (m + 1) K).comp (spW K m)).range

variable (K m) in
@[expose] noncomputable def spBarL : Subgroup (StatedProj (StatedSp (m + 1) K)) :=
  ((proj (m + 1) K).comp (spL K m)).range

theorem spBarW_commute_spBarL {x y : StatedProj (StatedSp (m + 1) K)} (hx : x ∈ spBarW K m)
    (hy : y ∈ spBarL K m) : x * y = y * x := by
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := hy
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, spW_commute_spL]

theorem commutator_spBarW (h4 : ∃ s : Finset K, s.card = 4) :
    ⁅spBarW K m, spBarW K m⁆ = spBarW K m :=
  commutator_range_of_perfect _
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl
      (Or.inr h4)).commutator_eq_top

theorem commutator_spBarL (h4 : ∃ s : Finset K, s.card = 4) :
    ⁅spBarL K m, spBarL K m⁆ = spBarL K m :=
  commutator_range_of_perfect _
    (CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp m K (Or.inl h4)).commutator_eq_top

end Blocks

section CharTwo

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}

theorem proj_sp_injective : Function.Injective (proj (m + 1) K) :=
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo.1

theorem eq_one_of_mul_self_eq_one {c : K} (h : c * c = 1) : c = 1 := by
  have h3 : (c - 1) ^ 2 = 0 := by
    rw [sub_sq, sq, h, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow,
      CharTwo.add_self_eq_zero]
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

theorem mem_range_spL_of_commute {g : StatedSp (m + 1) K}
    (h₁ : g * spW K m (sl2Upper 1) = spW K m (sl2Upper 1) * g)
    (h₂ : g * spW K m (sl2Lower 1) = spW K m (sl2Lower 1) * g) : g ∈ (spL K m).range := by
  rw [range_spL, mem_suppGroup_iff (parClosed_coords _).compl]
  set e : Fin (m + 1) ⊕ Fin (m + 1) := Sum.inl (Fin.last m) with he
  set f : Fin (m + 1) ⊕ Fin (m + 1) := Sum.inr (Fin.last m) with hf
  have hef : e ≠ f := Sum.inl_ne_inr
  set M := mat (m + 1) K g with hM
  have hU : M * single e f 1 = single e f 1 * M := by
    have h := congrArg (mat (m + 1) K) h₁
    rw [map_mul, map_mul, spW, longBlock_sl2Upper, mat_elt_positiveLong, transvection,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have hL : M * single f e 1 = single f e 1 * M := by
    have h := congrArg (mat (m + 1) K) h₂
    rw [map_mul, map_mul, spW, longBlock_sl2Lower, mat_elt_negativeLong, transvection,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
    exact add_left_cancel h
  have c1 : ∀ r, r ≠ e → M r e = 0 := fun r hr => by
    have h := congrFun (congrFun hU r) f
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hr] at h
    simpa using h
  have c2 : ∀ r, r ≠ f → M r f = 0 := fun r hr => by
    have h := congrFun (congrFun hL r) e
    rw [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hr] at h
    simpa using h
  have c3 : M e e = M f f := by
    have h := congrFun (congrFun hU e) f
    rw [mul_single_apply_same, single_mul_apply_same] at h
    simpa using h
  have hform : M e e * M f f = 1 := by
    have key := congrFun (congrFun (mat_transpose_mul_gram_mul g) e) f
    rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply,
      Finset.sum_eq_single e] at key
    · simpa [he, hf, par, sgn] using key
    · intro c _ hc
      rw [show (mat (m + 1) K) g c e = 0 from c1 c hc, zero_mul]
    · simp
  have hc : M e e = 1 := eq_one_of_mul_self_eq_one (by rw [← hform, ← c3])
  intro t ht r
  have ht' : t ∈ coords (Fin.last m) := not_not.mp ht
  rcases mem_coords.1 ht' with rfl | rfl
  · by_cases hr : r = e
    · rw [hr, hc, Matrix.one_apply_eq]
    · rw [c1 r hr, Matrix.one_apply_ne hr]
  · by_cases hr : r = f
    · rw [hr, ← c3, hc, Matrix.one_apply_eq]
    · rw [c2 r hr, Matrix.one_apply_ne hr]

theorem mem_spBarL_of_commute {x : StatedProj (StatedSp (m + 1) K)}
    (hx : ∀ w ∈ spBarW K m, x * w = w * x) : x ∈ spBarL K m := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have h1 := hx _ ⟨sl2Upper 1, rfl⟩
  have h2 := hx _ ⟨sl2Lower 1, rfl⟩
  simp only [MonoidHom.comp_apply] at h1 h2
  change proj (m + 1) K g * _ = _ * proj (m + 1) K g at h1 h2
  rw [← map_mul, ← map_mul] at h1 h2
  obtain ⟨S, hS⟩ := mem_range_spL_of_commute (proj_sp_injective h1) (proj_sp_injective h2)
  exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]; rfl⟩

theorem proj_spW_injective : Function.Injective ((proj (m + 1) K).comp (spW K m)) :=
  proj_sp_injective.comp (longBlock_injective _)

theorem proj_spL_injective : Function.Injective ((proj (m + 1) K).comp (spL K m)) :=
  proj_sp_injective.comp (spEmbed_injective _)

variable (K m) in
@[expose] noncomputable def spBarWEquiv : SL(2, K) ≃* spBarW K m :=
  MonoidHom.ofInjective proj_spW_injective

variable (K m) in
@[expose] noncomputable def spBarLEquiv : StatedSp m K ≃* spBarL K m :=
  MonoidHom.ofInjective proj_spL_injective

theorem isQuasisimple_spBarW (h4 : ∃ s : Finset K, s.card = 4) :
    CFSG.IsQuasisimple ↥(spBarW K m) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (spBarWEquiv K m) (isQuasisimple_SL le_rfl h4)

omit [Field K] [CharP K 2] in
theorem four_le_card_of_finset (h4 : ∃ s : Finset K, s.card = 4) : 4 ≤ Nat.card K ∨ Infinite K := by
  rcases finite_or_infinite K with hfin | hinf
  · left
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨s, hs⟩ := h4
    rw [Nat.card_eq_fintype_card, ← hs]
    exact Finset.card_le_univ s
  · exact Or.inr hinf

theorem isQuasisimple_spBarL (hm : 1 ≤ m) (h4 : ∃ s : Finset K, s.card = 4) :
    CFSG.IsQuasisimple ↥(spBarL K m) := by
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv (spBarLEquiv K m)
    (CFSG.LieType.Universal.Symplectic.isQuasisimple m K hm (Or.inl ?_))
  rcases four_le_card_of_finset h4 with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem center_statedSp_eq_bot (hm : 1 ≤ m) : center (StatedSp m K) = ⊥ := by
  have : NeZero m := ⟨by omega⟩
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    ← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.spScalars_eq_bot_of_charTwo (r := m)]

theorem card_center_spBarL (hm : 1 ≤ m) : Nat.card (center (spBarL K m)) = 1 := by
  rw [← card_center_congr (spBarLEquiv K m), center_statedSp_eq_bot hm, Subgroup.card_bot]

end CharTwo

end CFSG.ComponentClassification.RankTwoClassical
