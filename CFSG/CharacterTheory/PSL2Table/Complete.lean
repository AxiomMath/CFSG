module

public import CFSG.CharacterTheory.PSL2Table.TorusCharacters
public import CFSG.CharacterTheory.PSL2Table.Norms

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem mem_blocksIrr_of_norm_one {G : Type} [Group G] [Fintype G] {f : G → ℂ}
    (hf : f ∈ BlocksVChar G) (hn : BlocksInnerProduct f f = 1) (hpos : 0 < (f 1).re) :
    f ∈ BlocksIrr G := by
  obtain ⟨χ, hpos' | hneg⟩ := blocksVChar_norm_one_signed_irreducible hf hn
  · rw [hpos']
    exact χ.2
  · exfalso
    have h1 := blocksIrr_identity_re_pos χ
    rw [hneg, Pi.neg_apply, Complex.neg_re] at hpos
    linarith

theorem steinberg_mem_blocksIrr (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) : steinberg F ∈ BlocksIrr PSL(2, F) := by
  apply mem_blocksIrr_of_norm_one steinberg_mem_blocksVChar (steinberg_inner_self hF hq hν)
  rw [steinberg_one]
  simp only [Complex.natCast_re, Nat.cast_pos]
  exact Fintype.card_pos

theorem units_hom_inv_inv {K : Type} [Group K] (α : K →* ℂˣ) : α⁻¹⁻¹ = α := by
  ext k
  simp only [MonoidHom.inv_apply, inv_inv]

theorem units_hom_sq_eq_one_of_inv {K : Type} [Group K] {α : K →* ℂˣ} (h : α⁻¹ ^ 2 = 1) :
    α ^ 2 = 1 := by
  ext k
  have := congrArg (fun φ : K →* ℂˣ => φ k) h
  simp only [sq, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.one_apply] at this
  rw [← _root_.mul_inv_rev, inv_eq_one] at this
  rw [sq, MonoidHom.mul_apply, this, MonoidHom.one_apply]

theorem inv_ne_of_sq_ne_one {K : Type} [Group K] {α : K →* ℂˣ} (hα : α ^ 2 ≠ 1) : α ≠ α⁻¹ := by
  intro h
  apply hα
  rw [sq]
  nth_rewrite 2 [h]
  exact mul_inv_cancel α

theorem principal_mem_blocksIrr (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {α : splitTorus F →* ℂˣ} (hα : α ^ 2 ≠ 1) :
    principal α ∈ BlocksIrr PSL(2, F) := by
  apply mem_blocksIrr_of_norm_one (principal_mem_blocksVChar α)
  · rw [principal_inner hF hq hν, ite_eq_left rfl, ite_eq_right (inv_ne_of_sq_ne_one hα)]
    ring
  · rw [principal_one hF]
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity

theorem discrete_mem_blocksIrr (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {β : nonsplitTorus ν →* ℂˣ} (hβ : β ^ 2 ≠ 1) :
    discrete β ∈ BlocksIrr PSL(2, F) := by
  apply mem_blocksIrr_of_norm_one (discrete_mem_blocksVChar β)
  · rw [discrete_inner hF hq hν, ite_eq_left rfl, ite_eq_right (inv_ne_of_sq_ne_one hβ)]
    ring
  · rw [discrete_one hF hν]
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, sub_pos]
    exact_mod_cast (by omega : 1 < Fintype.card F)

theorem eq_of_values (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F} (hν : ¬ IsSquare ν)
    {f g : PSL(2, F) → ℂ} (hf : BlocksIsClassFunction f) (hg : BlocksIsClassFunction g)
    (h1 : f 1 = g 1) (hP : ∀ x ∈ unipotent F, x ≠ 1 → f x = g x)
    (hT : ∀ x ∈ splitTorus F, x ≠ 1 → f x = g x)
    (hS : ∀ x ∈ nonsplitTorus ν, x ≠ 1 → f x = g x) : f = g := by
  funext y
  have key : ∀ {H : Subgroup PSL(2, F)}, (∀ x ∈ H, x ≠ 1 → f x = g x) → y ∈ conjSet H →
      f y = g y := by
    intro H hH hy
    obtain ⟨hy1, k, hk⟩ := hy
    have hne : k * y * k⁻¹ ≠ 1 := by
      intro h
      apply hy1
      have := congrArg (fun z => k⁻¹ * z * k) h
      simpa [mul_assoc] using this
    rw [← hf y k, ← hg y k]
    exact hH _ hk hne
  rcases mem_conjSet_cases hF hq hν y with rfl | h | h | h
  · exact h1
  · exact key hP h
  · exact key hT h
  · exact key hS h

theorem principal_inv (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (α : splitTorus F →* ℂˣ) : principal α⁻¹ = principal α := by
  apply eq_of_values hF hq hν (blocksVChar_isClassFunction (principal_mem_blocksVChar _))
    (blocksVChar_isClassFunction (principal_mem_blocksVChar _))
  · rw [principal_one hF, principal_one hF]
  · intro x hx hx1
    rw [principal_of_mem_unipotent hF _ hx hx1, principal_of_mem_unipotent hF _ hx hx1]
  · intro x hx hx1
    rw [principal_of_mem_splitTorus _ hx hx1, principal_of_mem_splitTorus _ hx hx1,
      ← units_hom_apply_inv, ← units_hom_apply_inv, inv_inv]
    ring
  · intro x hx hx1
    rw [principal_of_mem_nonsplitTorus hF hν _ hx hx1,
      principal_of_mem_nonsplitTorus hF hν _ hx hx1]

theorem discrete_inv (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (β : nonsplitTorus ν →* ℂˣ) : discrete β⁻¹ = discrete β := by
  apply eq_of_values hF hq hν (blocksVChar_isClassFunction (discrete_mem_blocksVChar _))
    (blocksVChar_isClassFunction (discrete_mem_blocksVChar _))
  · rw [discrete_one hF hν, discrete_one hF hν]
  · intro x hx hx1
    rw [discrete_of_mem_unipotent hF hν _ hx hx1, discrete_of_mem_unipotent hF hν _ hx hx1]
  · intro x hx hx1
    rw [discrete_of_mem_splitTorus hF hν _ hx hx1, discrete_of_mem_splitTorus hF hν _ hx hx1]
  · intro x hx hx1
    rw [discrete_of_mem_nonsplitTorus hF hν _ hx hx1, discrete_of_mem_nonsplitTorus hF hν _ hx hx1,
      ← units_hom_apply_inv, ← units_hom_apply_inv, inv_inv]
    ring

theorem principal_eq_iff (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {α : splitTorus F →* ℂˣ} (hα : α ^ 2 ≠ 1) (α' : splitTorus F →* ℂˣ) :
    principal α' = principal α ↔ α' = α ∨ α' = α⁻¹ := by
  constructor
  · intro h
    have h1 := principal_inner hF hq hν α α'
    rw [h, principal_inner hF hq hν, ite_eq_left rfl, ite_eq_right (inv_ne_of_sq_ne_one hα)] at h1
    by_cases h2 : α = α'
    · exact Or.inl h2.symm
    · rw [ite_eq_right h2] at h1
      by_cases h3 : α = α'⁻¹
      · right
        rw [h3, units_hom_inv_inv]
      · rw [ite_eq_right h3] at h1
        norm_num at h1
  · rintro (rfl | rfl)
    · rfl
    · exact principal_inv hF hq hν α

theorem discrete_eq_iff (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {β : nonsplitTorus ν →* ℂˣ} (hβ : β ^ 2 ≠ 1) (β' : nonsplitTorus ν →* ℂˣ) :
    discrete β' = discrete β ↔ β' = β ∨ β' = β⁻¹ := by
  constructor
  · intro h
    have h1 := discrete_inner hF hq hν β β'
    rw [h, discrete_inner hF hq hν, ite_eq_left rfl, ite_eq_right (inv_ne_of_sq_ne_one hβ)] at h1
    by_cases h2 : β = β'
    · exact Or.inl h2.symm
    · rw [ite_eq_right h2] at h1
      by_cases h3 : β = β'⁻¹
      · right
        rw [h3, units_hom_inv_inv]
      · rw [ite_eq_right h3] at h1
        norm_num at h1
  · rintro (rfl | rfl)
    · rfl
    · exact discrete_inv hF hq hν β

noncomputable instance fintypeSplitChars : Fintype (splitTorus F →* ℂˣ) := Fintype.ofFinite _

noncomputable instance decEqSplitChars : DecidableEq (splitTorus F →* ℂˣ) := Classical.decEq _

noncomputable instance decEqNonsplitChars (ν : F) : DecidableEq (nonsplitTorus ν →* ℂˣ) :=
  Classical.decEq _

noncomputable instance fintypeNonsplitChars (ν : F) : Fintype (nonsplitTorus ν →* ℂˣ) :=
  Fintype.ofFinite _

@[expose] noncomputable def principalParams (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Finset (splitTorus F →* ℂˣ) :=
  Finset.univ.filter fun α => α ^ 2 ≠ 1

@[expose] noncomputable def discreteParams (ν : F) : Finset (nonsplitTorus ν →* ℂˣ) :=
  Finset.univ.filter fun β => β ^ 2 ≠ 1

@[expose] noncomputable def principalSet (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Finset (PSL(2, F) → ℂ) :=
  (principalParams F).image principal

@[expose] noncomputable def discreteSet (ν : F) : Finset (PSL(2, F) → ℂ) :=
  (discreteParams ν).image discrete

theorem card_filter_sq_ne_one {A : Type} [Group A] [Finite A] [Fintype (A →* ℂˣ)]
    [DecidableEq (A →* ℂˣ)] (hcomm : ∀ a b : A, a * b = b * a) :
    (Finset.univ.filter fun α : A →* ℂˣ => α ^ 2 ≠ 1).card =
      Nat.card A - Nat.card {a : A // a ^ 2 = 1} := by
  classical
  obtain ⟨h1, h2⟩ := card_units_hom_of_comm hcomm
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (A →* ℂˣ))) (fun α : A →* ℂˣ => α ^ 2 = 1)
  have hsq : (Finset.univ.filter fun α : A →* ℂˣ => α ^ 2 = 1).card =
      Nat.card {α : A →* ℂˣ // α ^ 2 = 1} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hsq, h2, Finset.card_univ, ← Nat.card_eq_fintype_card, h1] at h
  simp only [ne_eq]
  omega

theorem card_image_pairs {A : Type} [Group A] [Fintype (A →* ℂˣ)] [DecidableEq (A →* ℂˣ)]
    {Y : Type} [DecidableEq Y]
    (f : (A →* ℂˣ) → Y)
    (hf : ∀ α : A →* ℂˣ, α ^ 2 ≠ 1 → ∀ α', f α' = f α ↔ α' = α ∨ α' = α⁻¹) :
    ((Finset.univ.filter fun α : A →* ℂˣ => α ^ 2 ≠ 1).image f).card * 2 =
      (Finset.univ.filter fun α : A →* ℂˣ => α ^ 2 ≠ 1).card := by
  classical
  set s := Finset.univ.filter fun α : A →* ℂˣ => α ^ 2 ≠ 1 with hs
  have hfiber : ∀ y ∈ s.image f, (s.filter (fun α' => f α' = y)).card = 2 := by
    intro y hy
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hy
    have hα' : α ^ 2 ≠ 1 := (Finset.mem_filter.mp hα).2
    have hinv : α⁻¹ ^ 2 ≠ 1 := fun h => hα' (units_hom_sq_eq_one_of_inv h)
    have hfib : s.filter (fun α' => f α' = f α) = {α, α⁻¹} := by
      ext α'
      rw [Finset.mem_filter, hf α hα' α', Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro (rfl | rfl)
        · exact ⟨hα, Or.inl rfl⟩
        · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinv⟩, Or.inr rfl⟩
    rw [hfib, Finset.card_pair (inv_ne_of_sq_ne_one hα')]
  rw [Finset.card_eq_sum_card_image f s, Finset.sum_congr rfl hfiber, Finset.sum_const,
    smul_eq_mul]

theorem card_principalSet (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) :
    (principalSet F).card * 2 =
      Nat.card (splitTorus F) - (if IsSquare (-1 : F) then 2 else 1) := by
  rw [principalSet, principalParams,
    card_image_pairs principal (fun α hα α' => principal_eq_iff hF hq hν hα α'),
    card_filter_sq_ne_one splitTorus_comm, card_sq_eq_one_splitTorus hF]

theorem card_discreteSet (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) :
    (discreteSet ν).card * 2 =
      Nat.card (nonsplitTorus ν) - (if IsSquare (-1 : F) then 1 else 2) := by
  rw [discreteSet, discreteParams,
    card_image_pairs discrete (fun β hβ β' => discrete_eq_iff hF hq hν hβ β'),
    card_filter_sq_ne_one nonsplitTorus_comm, card_sq_eq_one_nonsplitTorus hF hν]

@[expose] noncomputable def knownSet (F : Type) [Field F] [Fintype F] [DecidableEq F] (ν : F) :
    Finset (PSL(2, F) → ℂ) :=
  insert 1 (insert (steinberg F) (principalSet F ∪ discreteSet ν))

theorem mem_principalSet_iff (χ : PSL(2, F) → ℂ) :
    χ ∈ principalSet F ↔ ∃ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 ∧ principal α = χ := by
  simp [principalSet, principalParams]

theorem mem_discreteSet_iff {ν : F} (χ : PSL(2, F) → ℂ) :
    χ ∈ discreteSet ν ↔ ∃ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 ∧ discrete β = χ := by
  simp [discreteSet, discreteParams]

theorem knownSet_subset (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) : ∀ χ ∈ knownSet F ν, χ ∈ BlocksIrr PSL(2, F) := by
  intro χ hχ
  simp only [knownSet, Finset.mem_insert, Finset.mem_union, mem_principalSet_iff,
    mem_discreteSet_iff] at hχ
  rcases hχ with rfl | rfl | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩
  · exact CFSG.DirectProduct.one_mem_blocksIrr _
  · exact steinberg_mem_blocksIrr hF hq hν
  · exact principal_mem_blocksIrr hF hq hν hα
  · exact discrete_mem_blocksIrr hF hq hν hβ

theorem sum_degree_sq_knownSet (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) :
    ∑ χ ∈ knownSet F ν, χ 1 ^ 2 = (Nat.card PSL(2, F) : ℂ) -
      (if IsSquare (-1 : F) then ((Fintype.card F : ℂ) + 1) ^ 2
        else ((Fintype.card F : ℂ) - 1) ^ 2) / 2 := by
  classical
  have hq' : (5 : ℝ) ≤ Fintype.card F := by exact_mod_cast hq
  have hpdeg : ∀ χ ∈ principalSet F, χ 1 = Fintype.card F + 1 := by
    intro χ hχ
    obtain ⟨α, -, rfl⟩ := (mem_principalSet_iff χ).mp hχ
    exact principal_one hF α
  have hddeg : ∀ χ ∈ discreteSet ν, χ 1 = Fintype.card F - 1 := by
    intro χ hχ
    obtain ⟨β, -, rfl⟩ := (mem_discreteSet_iff χ).mp hχ
    exact discrete_one hF hν β
  have hdisj : Disjoint (principalSet F) (discreteSet ν) := by
    rw [Finset.disjoint_left]
    intro χ h1 h2
    have := (hpdeg χ h1).symm.trans (hddeg χ h2)
    have := congrArg Complex.re this
    simp at this
    linarith
  have hSt : steinberg F ∉ principalSet F ∪ discreteSet ν := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · have h' := (steinberg_one (F := F)).symm.trans (hpdeg _ h)
      have h'' : (Fintype.card F : ℝ) = Fintype.card F + 1 := by
        simpa using congrArg Complex.re h'
      linarith
    · have h' := (steinberg_one (F := F)).symm.trans (hddeg _ h)
      have h'' : (Fintype.card F : ℝ) = Fintype.card F - 1 := by
        simpa using congrArg Complex.re h'
      linarith
  have hone : (1 : PSL(2, F) → ℂ) ∉ insert (steinberg F) (principalSet F ∪ discreteSet ν) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · have h' := congrFun h 1
      rw [steinberg_one, Pi.one_apply] at h'
      have h'' : (1 : ℝ) = Fintype.card F := by simpa using congrArg Complex.re h'
      linarith
    · rcases Finset.mem_union.mp h with h | h
      · have h' := hpdeg _ h
        rw [Pi.one_apply] at h'
        have h'' : (1 : ℝ) = Fintype.card F + 1 := by simpa using congrArg Complex.re h'
        linarith
      · have h' := hddeg _ h
        rw [Pi.one_apply] at h'
        have h'' : (1 : ℝ) = Fintype.card F - 1 := by simpa using congrArg Complex.re h'
        linarith
  have hsP : ∑ χ ∈ principalSet F, χ 1 ^ 2 =
      (principalSet F).card * ((Fintype.card F : ℂ) + 1) ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => ((Fintype.card F : ℂ) + 1) ^ 2)
      (fun χ hχ => by rw [hpdeg χ hχ]), Finset.sum_const, nsmul_eq_mul]
  have hsD : ∑ χ ∈ discreteSet ν, χ 1 ^ 2 =
      (discreteSet ν).card * ((Fintype.card F : ℂ) - 1) ^ 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => ((Fintype.card F : ℂ) - 1) ^ 2)
      (fun χ hχ => by rw [hddeg χ hχ]), Finset.sum_const, nsmul_eq_mul]
  rw [knownSet, Finset.sum_insert hone, Finset.sum_insert hSt, Finset.sum_union hdisj, hsP, hsD,
    Pi.one_apply, steinberg_one]
  have hP := card_principalSet hF hq hν
  have hD := card_discreteSet hF hq hν
  have hT := card_splitTorus_complex hF (F := F)
  have hS := card_nonsplitTorus_complex hF hν
  have hG := card_PSL_complex hF (F := F)
  have hT' := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  have hS' := card_nonsplitTorus hF hν
  split_ifs with hm
  · have hP' : ((principalSet F).card : ℂ) * 2 = (Nat.card (splitTorus F) : ℂ) - 2 := by
      have h2 : 2 ≤ Nat.card (splitTorus F) := by omega
      rw [ite_eq_left hm] at hP
      have := congrArg (Nat.cast (R := ℂ)) hP
      push_cast [Nat.cast_sub h2] at this
      exact this
    have hD' : ((discreteSet ν).card : ℂ) * 2 = (Nat.card (nonsplitTorus ν) : ℂ) - 1 := by
      have h1 : 1 ≤ Nat.card (nonsplitTorus ν) := by omega
      rw [ite_eq_left hm] at hD
      have := congrArg (Nat.cast (R := ℂ)) hD
      push_cast [Nat.cast_sub h1] at this
      exact this
    rw [hT] at hP'
    rw [hS] at hD'
    rw [hG]
    linear_combination ((Fintype.card F : ℂ) + 1) ^ 2 / 2 * hP' +
      ((Fintype.card F : ℂ) - 1) ^ 2 / 2 * hD'
  · have hP' : ((principalSet F).card : ℂ) * 2 = (Nat.card (splitTorus F) : ℂ) - 1 := by
      have h1 : 1 ≤ Nat.card (splitTorus F) := by omega
      rw [ite_eq_right hm] at hP
      have := congrArg (Nat.cast (R := ℂ)) hP
      push_cast [Nat.cast_sub h1] at this
      exact this
    have hD' : ((discreteSet ν).card : ℂ) * 2 = (Nat.card (nonsplitTorus ν) : ℂ) - 2 := by
      have h2 : 2 ≤ Nat.card (nonsplitTorus ν) := by omega
      rw [ite_eq_right hm] at hD
      have := congrArg (Nat.cast (R := ℂ)) hD
      push_cast [Nat.cast_sub h2] at this
      exact this
    rw [hT] at hP'
    rw [hS] at hD'
    rw [hG]
    linear_combination ((Fintype.card F : ℂ) + 1) ^ 2 / 2 * hP' +
      ((Fintype.card F : ℂ) - 1) ^ 2 / 2 * hD'

end CFSG.PSL2Table
