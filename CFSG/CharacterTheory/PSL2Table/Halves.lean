module

public import CFSG.CharacterTheory.PSL2Table.GelfandGraev
public import CFSG.CharacterTheory.PSL2Table.Complete
public import CFSG.CharacterTheory.PSL2Table.NormTwoSplit

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG.TwoRankLowerBound.Helpers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem exists_order_two_char {A : Type} [Group A] [Finite A] (hcomm : ∀ a b : A, a * b = b * a)
    (h : Nat.card {a : A // a ^ 2 = 1} = 2) : ∃ α : A →* ℂˣ, α ≠ 1 ∧ α ^ 2 = 1 := by
  rw [← (card_units_hom_of_comm hcomm).2, Nat.card_eq_two_iff] at h
  obtain ⟨x, y, hxy, -⟩ := h
  by_cases hx : (x : A →* ℂˣ) = 1
  · refine ⟨y, fun hy => hxy (Subtype.ext (hx.trans hy.symm)), y.2⟩
  · exact ⟨x, hx, x.2⟩

@[expose] noncomputable def splitQuadChar (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    splitTorus F →* ℂˣ :=
  if h : ∃ α : splitTorus F →* ℂˣ, α ≠ 1 ∧ α ^ 2 = 1 then h.choose else 1

@[expose] noncomputable def nonsplitQuadChar (ν : F) : nonsplitTorus ν →* ℂˣ :=
  if h : ∃ β : nonsplitTorus ν →* ℂˣ, β ≠ 1 ∧ β ^ 2 = 1 then h.choose else 1

theorem splitQuadChar_spec (hF : ringChar F ≠ 2) (hm : IsSquare (-1 : F)) :
    splitQuadChar F ≠ 1 ∧ splitQuadChar F ^ 2 = 1 := by
  have hex : ∃ α : splitTorus F →* ℂˣ, α ≠ 1 ∧ α ^ 2 = 1 := by
    apply exists_order_two_char splitTorus_comm
    rw [card_sq_eq_one_splitTorus hF, ite_eq_left hm]
  rw [splitQuadChar, dite_eq_left hex]
  exact hex.choose_spec

theorem nonsplitQuadChar_spec (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
    (hm : ¬ IsSquare (-1 : F)) : nonsplitQuadChar ν ≠ 1 ∧ nonsplitQuadChar ν ^ 2 = 1 := by
  have hex : ∃ β : nonsplitTorus ν →* ℂˣ, β ≠ 1 ∧ β ^ 2 = 1 := by
    apply exists_order_two_char nonsplitTorus_comm
    rw [card_sq_eq_one_nonsplitTorus hF hν, ite_eq_right hm]
  rw [nonsplitQuadChar, dite_eq_left hex]
  exact hex.choose_spec

theorem inv_eq_of_sq_eq_one {K : Type} [Group K] {α : K →* ℂˣ} (h : α ^ 2 = 1) : α⁻¹ = α := by
  ext k
  have := congrArg (fun φ : K →* ℂˣ => φ k) h
  simp only [sq, MonoidHom.mul_apply, MonoidHom.one_apply] at this
  rw [MonoidHom.inv_apply, inv_eq_of_mul_eq_one_right this]

@[expose] noncomputable def normTwoChar (F : Type) [Field F] [Fintype F] [DecidableEq F] (ν : F) :
    PSL(2, F) → ℂ :=
  if IsSquare (-1 : F) then principal (splitQuadChar F) else discrete (nonsplitQuadChar ν)

@[expose] def normTwoDegree (F : Type) [Field F] [Fintype F] [DecidableEq F] : ℕ :=
  if IsSquare (-1 : F) then Fintype.card F + 1 else Fintype.card F - 1

theorem normTwoChar_mem_blocksVChar {ν : F} : normTwoChar F ν ∈ BlocksVChar PSL(2, F) := by
  rw [normTwoChar]
  split_ifs
  · exact principal_mem_blocksVChar _
  · exact discrete_mem_blocksVChar _

theorem normTwoChar_one (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    normTwoChar F ν 1 = normTwoDegree F := by
  rw [normTwoChar, normTwoDegree]
  split_ifs
  · rw [principal_one hF]
    push_cast
    ring
  · rw [discrete_one hF hν, Nat.cast_sub (by have := Fintype.one_lt_card (α := F); omega)]
    push_cast
    ring

theorem normTwoChar_of_mem_unipotent (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
    {x : PSL(2, F)} (hx : x ∈ unipotent F) (hx1 : x ≠ 1) :
    normTwoChar F ν x = if IsSquare (-1 : F) then 1 else -1 := by
  rw [normTwoChar]
  split_ifs
  · exact principal_of_mem_unipotent hF _ hx hx1
  · exact discrete_of_mem_unipotent hF hν _ hx hx1

theorem normTwoChar_inner_self (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) : BlocksInnerProduct (normTwoChar F ν) (normTwoChar F ν) = 2 := by
  rw [normTwoChar]
  split_ifs with hm
  · obtain ⟨-, h2⟩ := splitQuadChar_spec hF hm
    rw [principal_inner hF hq hν, ite_eq_left rfl, ite_eq_left (inv_eq_of_sq_eq_one h2).symm]
    norm_num
  · obtain ⟨-, h2⟩ := nonsplitQuadChar_spec hF hν hm
    rw [discrete_inner hF hq hν, ite_eq_left rfl, ite_eq_left (inv_eq_of_sq_eq_one h2).symm]
    norm_num

theorem principal_inner_principal_quad (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {α₀ : splitTorus F →* ℂˣ} (h0 : α₀ ^ 2 = 1) {α : splitTorus F →* ℂˣ}
    (hα : α ^ 2 ≠ 1) : BlocksInnerProduct (principal α₀) (principal α) = 0 := by
  rw [principal_inner hF hq hν, ite_eq_right, ite_eq_right]
  · ring
  all_goals
    rintro rfl
    first
      | exact hα h0
      | exact hα (units_hom_sq_eq_one_of_inv h0)

theorem discrete_inner_discrete_quad (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {β₀ : nonsplitTorus ν →* ℂˣ} (h0 : β₀ ^ 2 = 1)
    {β : nonsplitTorus ν →* ℂˣ} (hβ : β ^ 2 ≠ 1) :
    BlocksInnerProduct (discrete β₀) (discrete β) = 0 := by
  rw [discrete_inner hF hq hν, ite_eq_right, ite_eq_right]
  · ring
  all_goals
    rintro rfl
    first
      | exact hβ h0
      | exact hβ (units_hom_sq_eq_one_of_inv h0)

theorem normTwoChar_inner_known (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) :
    ∀ χ ∈ knownSet F ν, BlocksInnerProduct (normTwoChar F ν) χ = 0 := by
  intro χ hχ
  simp only [knownSet, Finset.mem_insert, Finset.mem_union, mem_principalSet_iff,
    mem_discreteSet_iff] at hχ
  rw [normTwoChar]
  split_ifs with hm
  · obtain ⟨h1, h2⟩ := splitQuadChar_spec hF hm
    rcases hχ with rfl | rfl | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩
    · rw [principal_inner_one hF hq hν, ite_eq_right h1]
    · rw [principal_inner_steinberg hF hq hν, ite_eq_right h1]
    · exact principal_inner_principal_quad hF hq hν h2 hα
    · exact principal_inner_discrete hF hq hν _ _
  · obtain ⟨h1, h2⟩ := nonsplitQuadChar_spec hF hν hm
    rcases hχ with rfl | rfl | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩
    · rw [discrete_inner_one hF hq hν, ite_eq_right h1, neg_zero]
    · rw [discrete_inner_steinberg hF hq hν, ite_eq_right h1]
    · rw [bip_conj_symm, principal_inner_discrete hF hq hν, map_zero]
    · exact discrete_inner_discrete_quad hF hq hν h2 hβ

theorem known_const_unipotent (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    ∀ χ ∈ insert (normTwoChar F ν) (knownSet F ν), ∃ c : ℂ,
      ∀ x ∈ unipotent F, x ≠ 1 → χ x = c := by
  intro χ hχ
  simp only [knownSet, Finset.mem_insert, Finset.mem_union, mem_principalSet_iff,
    mem_discreteSet_iff] at hχ
  rcases hχ with rfl | rfl | rfl | ⟨α, -, rfl⟩ | ⟨β, -, rfl⟩
  · exact ⟨_, fun x hx hx1 => normTwoChar_of_mem_unipotent hF hν hx hx1⟩
  · exact ⟨1, fun _ _ _ => rfl⟩
  · exact ⟨0, fun x hx hx1 => steinberg_of_mem_unipotent hF hx hx1⟩
  · exact ⟨1, fun x hx hx1 => principal_of_mem_unipotent hF α hx hx1⟩
  · exact ⟨-1, fun x hx hx1 => discrete_of_mem_unipotent hF hν β hx hx1⟩

@[expose] noncomputable def halfPlus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F) :
    PSL(2, F) → ℂ :=
  (1 / 2 : ℂ) • (normTwoChar F ν + ggDiff hF ψ ν)

@[expose] noncomputable def halfMinus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F) :
    PSL(2, F) → ℂ :=
  (1 / 2 : ℂ) • (normTwoChar F ν - ggDiff hF ψ ν)

theorem blocksIrr_eq (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    BlocksIrr PSL(2, F) = (knownSet F ν : Set (PSL(2, F) → ℂ)) ∪
        {halfPlus hF ψ ν, halfMinus hF ψ ν} ∧
      halfPlus hF ψ ν ∈ BlocksIrr PSL(2, F) ∧ halfMinus hF ψ ν ∈ BlocksIrr PSL(2, F) ∧
      halfPlus hF ψ ν ≠ halfMinus hF ψ ν ∧ halfPlus hF ψ ν ∉ knownSet F ν ∧
      halfMinus hF ψ ν ∉ knownSet F ν ∧
      2 * halfPlus hF ψ ν 1 = normTwoDegree F ∧ 2 * halfMinus hF ψ ν 1 = normTwoDegree F := by
  classical
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hd : 0 < normTwoDegree F := by
    rw [normTwoDegree]
    split_ifs <;> omega
  have hXsum : ∑ χ ∈ knownSet F ν, χ 1 ^ 2 =
      (Nat.card PSL(2, F) : ℂ) - ((normTwoDegree F : ℕ) : ℂ) ^ 2 / 2 := by
    rw [sum_degree_sq_knownSet hF hq hν, normTwoDegree]
    split_ifs
    · push_cast
      ring
    · rw [Nat.cast_sub hq1]
      push_cast
      ring
  obtain ⟨ξ₁, ξ₂, hξ₁, hξ₂, hne, hξ₁X, hξ₂X, hΦ, hd₁, hd₂, hIrr⟩ :=
    norm_two_split (knownSet_subset hF hq hν) hd hXsum normTwoChar_mem_blocksVChar
      (normTwoChar_inner_self hF hq hν) (normTwoChar_one hF hν) (normTwoChar_inner_known hF hq hν)
  have hΔX : ∀ θ ∈ knownSet F ν, BlocksInnerProduct (ggDiff hF ψ ν) θ = 0 := by
    intro θ hθ
    obtain ⟨c, hc⟩ := known_const_unipotent hF hν θ (Finset.mem_insert_of_mem hθ)
    exact ggDiff_inner_of_const hF hq hψ hν
      (blocksVChar_isClassFunction (AddSubgroup.subset_closure (knownSet_subset hF hq hν θ hθ)))
      c hc
  have hΔΦ : BlocksInnerProduct (ggDiff hF ψ ν) (ξ₁ + ξ₂) = 0 := by
    rw [← hΦ]
    obtain ⟨c, hc⟩ := known_const_unipotent hF hν _ (Finset.mem_insert_self _ _)
    exact ggDiff_inner_of_const hF hq hψ hν
      (blocksVChar_isClassFunction normTwoChar_mem_blocksVChar) c hc
  have hdiff := norm_two_difference hξ₁ hξ₂ hne hξ₁X hξ₂X hIrr (ggDiff_mem_blocksVChar hF ψ ν)
    (ggDiff_inner_self hF hq hψ hν) hΔX hΔΦ
  have hhalf : (halfPlus hF ψ ν = ξ₁ ∧ halfMinus hF ψ ν = ξ₂) ∨
      (halfPlus hF ψ ν = ξ₂ ∧ halfMinus hF ψ ν = ξ₁) := by
    rcases hdiff with h | h
    · left
      constructor
      · rw [halfPlus, hΦ, h]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
        ring
      · rw [halfMinus, hΦ, h]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
        ring
    · right
      constructor
      · rw [halfPlus, hΦ, h]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
        ring
      · rw [halfMinus, hΦ, h]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
        ring
  rcases hhalf with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact ⟨hIrr, hξ₁, hξ₂, hne, hξ₁X, hξ₂X, hd₁, hd₂⟩
  · rw [h1, h2]
    refine ⟨?_, hξ₂, hξ₁, Ne.symm hne, hξ₂X, hξ₁X, hd₂, hd₁⟩
    rw [hIrr, Set.pair_comm]

@[expose] noncomputable def epsSign (F : Type) [Field F] [Fintype F] [DecidableEq F] : ℂ :=
  if IsSquare (-1 : F) then 1 else -1

theorem units_hom_apply_eq_inv_of_sq {K : Type} [Group K] {α : K →* ℂˣ} (h : α ^ 2 = 1)
    (k : K) : (α k⁻¹ : ℂ) = (α k : ℂ) := by
  rw [units_hom_apply_inv, inv_eq_of_sq_eq_one h]

theorem halfPlus_one (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {ν : F} (hν : ¬ IsSquare ν) :
    halfPlus hF ψ ν 1 = (normTwoDegree F : ℂ) / 2 := by
  rw [halfPlus, Pi.smul_apply, Pi.add_apply, normTwoChar_one hF hν, ggDiff_one, smul_eq_mul]
  ring

theorem halfMinus_one (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {ν : F} (hν : ¬ IsSquare ν) :
    halfMinus hF ψ ν 1 = (normTwoDegree F : ℂ) / 2 := by
  rw [halfMinus, Pi.smul_apply, Pi.sub_apply, normTwoChar_one hF hν, ggDiff_one, smul_eq_mul]
  ring

theorem halfPlus_unip (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {ν : F}
    (hν : ¬ IsSquare ν) {t : F} (ht : t ≠ 0) :
    halfPlus hF ψ ν (mk (unip t)) = (epsSign F + quadChar F t * quadGauss ψ) / 2 := by
  rw [halfPlus, Pi.smul_apply, Pi.add_apply, normTwoChar_of_mem_unipotent hF hν
    ⟨unip t, unip_mem_unipSL t, rfl⟩
    (fun h => ht ((mk_unip_eq_one_iff (Ring.two_ne_zero hF) t).mp h)),
    ggDiff_unip hF hψ hν ht, smul_eq_mul, epsSign]
  ring

theorem halfMinus_unip (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {ν : F}
    (hν : ¬ IsSquare ν) {t : F} (ht : t ≠ 0) :
    halfMinus hF ψ ν (mk (unip t)) = (epsSign F - quadChar F t * quadGauss ψ) / 2 := by
  rw [halfMinus, Pi.smul_apply, Pi.sub_apply, normTwoChar_of_mem_unipotent hF hν
    ⟨unip t, unip_mem_unipSL t, rfl⟩
    (fun h => ht ((mk_unip_eq_one_iff (Ring.two_ne_zero hF) t).mp h)),
    ggDiff_unip hF hψ hν ht, smul_eq_mul, epsSign]
  ring

theorem normTwoChar_of_mem_splitTorus (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
    {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    normTwoChar F ν x = if IsSquare (-1 : F) then 2 * (splitQuadChar F ⟨x, hx⟩ : ℂ) else 0 := by
  rw [normTwoChar]
  split_ifs with hm
  · rw [principal_of_mem_splitTorus _ hx hx1,
      units_hom_apply_eq_inv_of_sq (splitQuadChar_spec hF hm).2]
    ring
  · exact discrete_of_mem_splitTorus hF hν _ hx hx1

theorem normTwoChar_of_mem_nonsplitTorus (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
    {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    normTwoChar F ν x =
      if IsSquare (-1 : F) then 0 else -(2 * (nonsplitQuadChar ν ⟨x, hx⟩ : ℂ)) := by
  rw [normTwoChar]
  split_ifs with hm
  · exact principal_of_mem_nonsplitTorus hF hν _ hx hx1
  · rw [discrete_of_mem_nonsplitTorus hF hν _ hx hx1,
      units_hom_apply_eq_inv_of_sq (nonsplitQuadChar_spec hF hν hm).2]
    ring

theorem halfPlus_of_mem_splitTorus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {ν : F}
    (hν : ¬ IsSquare ν) {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    halfPlus hF ψ ν x = if IsSquare (-1 : F) then (splitQuadChar F ⟨x, hx⟩ : ℂ) else 0 := by
  rw [halfPlus, Pi.smul_apply, Pi.add_apply, normTwoChar_of_mem_splitTorus hF hν hx hx1,
    ggDiff_of_mem_splitTorus hF ψ ν hx hx1, smul_eq_mul]
  split_ifs <;> ring

theorem halfMinus_of_mem_splitTorus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {ν : F}
    (hν : ¬ IsSquare ν) {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    halfMinus hF ψ ν x = if IsSquare (-1 : F) then (splitQuadChar F ⟨x, hx⟩ : ℂ) else 0 := by
  rw [halfMinus, Pi.smul_apply, Pi.sub_apply, normTwoChar_of_mem_splitTorus hF hν hx hx1,
    ggDiff_of_mem_splitTorus hF ψ ν hx hx1, smul_eq_mul]
  split_ifs <;> ring

theorem halfPlus_of_mem_nonsplitTorus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {ν : F}
    (hν : ¬ IsSquare ν) {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    halfPlus hF ψ ν x = if IsSquare (-1 : F) then 0 else -(nonsplitQuadChar ν ⟨x, hx⟩ : ℂ) := by
  rw [halfPlus, Pi.smul_apply, Pi.add_apply, normTwoChar_of_mem_nonsplitTorus hF hν hx hx1,
    ggDiff_of_mem_nonsplitTorus hF ψ hν hx hx1, smul_eq_mul]
  split_ifs <;> ring

theorem halfMinus_of_mem_nonsplitTorus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) {ν : F}
    (hν : ¬ IsSquare ν) {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    halfMinus hF ψ ν x = if IsSquare (-1 : F) then 0 else -(nonsplitQuadChar ν ⟨x, hx⟩ : ℂ) := by
  rw [halfMinus, Pi.smul_apply, Pi.sub_apply, normTwoChar_of_mem_nonsplitTorus hF hν hx hx1,
    ggDiff_of_mem_nonsplitTorus hF ψ hν hx hx1, smul_eq_mul]
  split_ifs <;> ring

theorem quadGauss_sq_eps (hF : ringChar F ≠ 2) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    quadGauss ψ ^ 2 = epsSign F * Fintype.card F := by
  rw [quadGauss_sq hF hψ, quadChar_neg_one_eq, epsSign]

end CFSG.PSL2Table
