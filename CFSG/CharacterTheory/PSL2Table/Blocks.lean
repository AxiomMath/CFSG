module

public import CFSG.CharacterTheory.PSL2Table.BlockTools
public import CFSG.CharacterTheory.PSL2Table

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG CFSG.BrauerThirdMainTheorem.Helpers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem forall_of_families (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {P : PSL(2, F) → Prop} (hP : ∀ g h : PSL(2, F), P (h * g * h⁻¹) → P g)
    (h1 : P 1) (hU : ∀ x ∈ unipotent F, x ≠ 1 → P x)
    (hT : ∀ x ∈ splitTorus F, x ≠ 1 → P x) (hS : ∀ x ∈ nonsplitTorus ν, x ≠ 1 → P x)
    (g : PSL(2, F)) : P g := by
  have key : ∀ {H : Subgroup PSL(2, F)}, (∀ x ∈ H, x ≠ 1 → P x) → g ∈ conjSet H → P g := by
    intro H hH hg
    obtain ⟨hg1, k, hk⟩ := hg
    apply hP g k
    refine hH _ hk (fun h => hg1 ?_)
    have := congrArg (fun z => k⁻¹ * z * k) h
    simpa [mul_assoc] using this
  rcases mem_conjSet_cases hF hq hν g with rfl | h | h | h
  · exact h1
  · exact key hU h
  · exact key hT h
  · exact key hS h

theorem units_hom_value_of_sq {K : Type} [Group K] {α : K →* ℂˣ} (h : α ^ 2 = 1) (k : K) :
    (α k : ℂ) = 1 ∨ (α k : ℂ) = -1 := by
  have := congrArg (fun φ : K →* ℂˣ => ((φ k : ℂˣ) : ℂ)) h
  simp only [sq, MonoidHom.mul_apply, MonoidHom.one_apply, Units.val_mul, Units.val_one] at this
  exact mul_self_eq_one_iff.mp this

theorem units_hom_mul_sq {K : Type} [Group K] {β β₀ : K →* ℂˣ} (h0 : β₀ ^ 2 = 1) :
    (β * β₀) ^ 2 = β ^ 2 := by
  ext k
  have := congrArg (fun φ : K →* ℂˣ => ((φ k : ℂˣ) : ℂ)) h0
  simp only [sq, MonoidHom.mul_apply, MonoidHom.one_apply, Units.val_mul, Units.val_one] at this ⊢
  linear_combination (β k : ℂ) * (β k : ℂ) * this

theorem units_hom_mul_ne_self {K : Type} [Group K] {β β₀ : K →* ℂˣ} (h0 : β₀ ≠ 1) :
    β * β₀ ≠ β := by
  intro h
  apply h0
  ext k
  have := congrArg (fun φ : K →* ℂˣ => ((φ k : ℂˣ) : ℂ)) h
  simp only [MonoidHom.mul_apply, Units.val_mul] at this
  simp only [MonoidHom.one_apply, Units.val_one]
  exact mul_left_cancel₀ (Units.ne_zero (β k)) (by rw [this, mul_one])

theorem units_hom_mul_ne_inv {K : Type} [Group K] [Finite K] (hK : Nat.card K % 4 = 2)
    {β β₀ : K →* ℂˣ} (hβ : β ^ 2 ≠ 1) (h0 : β₀ ^ 2 = 1) : β * β₀ ≠ β⁻¹ := by
  intro h
  apply hβ
  ext s
  have hs := congrArg (fun φ : K →* ℂˣ => ((φ s : ℂˣ) : ℂ)) h
  have h0s := congrArg (fun φ : K →* ℂˣ => ((φ s : ℂˣ) : ℂ)) h0
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    sq, MonoidHom.one_apply, Units.val_one] at hs h0s
  simp only [sq, MonoidHom.mul_apply, MonoidHom.one_apply, Units.val_mul, Units.val_one]
  have hz : (β s : ℂ) ≠ 0 := Units.ne_zero _
  have hzw : (β s : ℂ) * β₀ s * β s = 1 := by
    rw [hs, inv_mul_cancel₀ hz]
  have h4 : (β s : ℂ) ^ 4 = 1 := by
    linear_combination (-((β s : ℂ) ^ 4)) * h0s + ((β s : ℂ) ^ 2 * β₀ s + 1) * hzw
  have hn : (β s : ℂ) ^ Nat.card K = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  obtain ⟨j, hj⟩ : ∃ j, Nat.card K = 4 * j + 2 := ⟨Nat.card K / 4, by omega⟩
  rw [hj, pow_add, pow_mul, h4, one_pow, one_mul, sq] at hn
  exact hn

theorem halfPlus_add_halfMinus (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (ν : F)
    (x : PSL(2, F)) : halfPlus hF ψ ν x + halfMinus hF ψ ν x = normTwoChar F ν x := by
  simp only [halfPlus, halfMinus, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem discrete_mul_eq_or_eq_neg (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (β : nonsplitTorus ν →* ℂˣ) {β₀ : nonsplitTorus ν →* ℂˣ}
    (h0 : β₀ ^ 2 = 1) (g : PSL(2, F)) :
    discrete (β * β₀) g = discrete β g ∨ discrete (β * β₀) g = -discrete β g := by
  apply forall_of_families hF hq hν
    (P := fun g => discrete (β * β₀) g = discrete β g ∨ discrete (β * β₀) g = -discrete β g)
  · intro g h hP
    simpa only [blocksVChar_isClassFunction (discrete_mem_blocksVChar (β * β₀)) g h,
      blocksVChar_isClassFunction (discrete_mem_blocksVChar β) g h] using hP
  · left
    rw [discrete_one hF hν, discrete_one hF hν]
  · intro x hx hx1
    left
    rw [discrete_of_mem_unipotent hF hν _ hx hx1, discrete_of_mem_unipotent hF hν _ hx hx1]
  · intro x hx hx1
    left
    rw [discrete_of_mem_splitTorus hF hν _ hx hx1, discrete_of_mem_splitTorus hF hν _ hx hx1]
  · intro x hx hx1
    rw [discrete_of_mem_nonsplitTorus hF hν _ hx hx1, discrete_of_mem_nonsplitTorus hF hν _ hx hx1]
    simp only [MonoidHom.mul_apply, Units.val_mul, units_hom_apply_eq_inv_of_sq h0]
    rcases units_hom_value_of_sq h0 ⟨x, hx⟩ with h | h
    · left
      rw [h]
      ring
    · right
      rw [h]
      ring

theorem principal_mul_eq_or_eq_neg (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (α : splitTorus F →* ℂˣ) {α₀ : splitTorus F →* ℂˣ} (h0 : α₀ ^ 2 = 1)
    (g : PSL(2, F)) :
    principal (α * α₀) g = principal α g ∨ principal (α * α₀) g = -principal α g := by
  apply forall_of_families hF hq hν
    (P := fun g => principal (α * α₀) g = principal α g ∨ principal (α * α₀) g = -principal α g)
  · intro g h hP
    simpa only [blocksVChar_isClassFunction (principal_mem_blocksVChar (α * α₀)) g h,
      blocksVChar_isClassFunction (principal_mem_blocksVChar α) g h] using hP
  · left
    rw [principal_one hF, principal_one hF]
  · intro x hx hx1
    left
    rw [principal_of_mem_unipotent hF _ hx hx1, principal_of_mem_unipotent hF _ hx hx1]
  · intro x hx hx1
    rw [principal_of_mem_splitTorus _ hx hx1, principal_of_mem_splitTorus _ hx hx1]
    simp only [MonoidHom.mul_apply, Units.val_mul, units_hom_apply_eq_inv_of_sq h0]
    rcases units_hom_value_of_sq h0 ⟨x, hx⟩ with h | h
    · left
      rw [h]
      ring
    · right
      rw [h]
      ring
  · intro x hx hx1
    left
    rw [principal_of_mem_nonsplitTorus hF hν _ hx hx1,
      principal_of_mem_nonsplitTorus hF hν _ hx hx1]

section ThreeModEight

omit [DecidableEq F] in
theorem card_PSL_of_eq_three (hF : ringChar F ≠ 2) {k : ℕ} (hk : Fintype.card F = 8 * k + 3) :
    (Nat.card PSL(2, F) : ℂ) = 4 * (8 * k + 3) * (8 * k ^ 2 + 6 * k + 1) := by
  rw [card_PSL_complex hF, hk]
  push_cast
  ring

omit [DecidableEq F] in
theorem four_dvd_card_PSL_of_eq_three (hF : ringChar F ≠ 2) {k : ℕ}
    (hk : Fintype.card F = 8 * k + 3) : 4 ∣ Nat.card PSL(2, F) := by
  refine ⟨(8 * k + 3) * (8 * k ^ 2 + 6 * k + 1), ?_⟩
  have : (Nat.card PSL(2, F) : ℂ) =
      ((4 * ((8 * k + 3) * (8 * k ^ 2 + 6 * k + 1)) : ℕ) : ℂ) := by
    rw [card_PSL_of_eq_three hF hk]
    push_cast
    ring
  exact_mod_cast this

theorem principalCoeff_mem_of_eq_three (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m)
    {k : ℕ} (hk : Fintype.card F = 8 * k + 3) (g : PSL(2, F)) :
    (1 + (8 * k + 3 : ℂ) * steinberg F g + (4 * k + 1 : ℂ) * normTwoChar F ν g) /
      (Nat.card PSL(2, F) : ℂ) ∈ BlocksLocalRing m := by
  have hsq : ¬ IsSquare (-1 : F) := by
    rw [isSquare_neg_one_iff_mod_four hF]
    omega
  have hN : Odd ((8 * k + 3) * (8 * k ^ 2 + 6 * k + 1) : ℤ) :=
    Odd.mul (⟨4 * k + 1, by ring⟩ : Odd (8 * (k : ℤ) + 3)) ⟨4 * k ^ 2 + 3 * k, by ring⟩
  have key : ∀ (x : ℂ) (n : ℤ), x = 4 * n →
      x / (Nat.card PSL(2, F) : ℂ) ∈ BlocksLocalRing m := by
    intro x n hx
    have : x / (Nat.card PSL(2, F) : ℂ) =
        (n : ℂ) / (((8 * k + 3) * (8 * k ^ 2 + 6 * k + 1) : ℤ) : ℂ) := by
      rw [hx, card_PSL_of_eq_three hF hk, mul_assoc 4]
      push_cast
      rw [mul_div_mul_left _ _ (by norm_num : (4 : ℂ) ≠ 0)]
    rw [this]
    exact div_odd_mem_localRing m hm h2 (intCast_mem_localRing m hm n) hN
  apply forall_of_families hF hq hν (P := fun g =>
    (1 + (8 * k + 3 : ℂ) * steinberg F g + (4 * k + 1 : ℂ) * normTwoChar F ν g) /
      (Nat.card PSL(2, F) : ℂ) ∈ BlocksLocalRing m)
  · intro g h hP
    simpa only [blocksVChar_isClassFunction steinberg_mem_blocksVChar g h,
      blocksVChar_isClassFunction normTwoChar_mem_blocksVChar g h] using hP
  · apply key _ (24 * k ^ 2 + 16 * k + 3)
    rw [steinberg_one, normTwoChar_one hF hν, normTwoDegree, ite_eq_right hsq, hk,
      show 8 * k + 3 - 1 = 8 * k + 2 by omega]
    push_cast
    ring
  · intro x hx hx1
    apply key _ (-k)
    rw [steinberg_of_mem_unipotent hF hx hx1, normTwoChar_of_mem_unipotent hF hν hx hx1,
      ite_eq_right hsq]
    push_cast
    ring
  · intro x hx hx1
    apply key _ (2 * k + 1)
    rw [steinberg_of_mem_splitTorus hx hx1, normTwoChar_of_mem_splitTorus hF hν hx hx1,
      ite_eq_right hsq]
    push_cast
    ring
  · intro x hx hx1
    rw [steinberg_of_mem_nonsplitTorus hν hx hx1, normTwoChar_of_mem_nonsplitTorus hF hν hx hx1,
      ite_eq_right hsq]
    rcases units_hom_value_of_sq (nonsplitQuadChar_spec hF hν hsq).2 ⟨x, hx⟩ with h | h
    · rw [h]
      apply key _ (-(4 * k + 1))
      push_cast
      ring
    · rw [h]
      apply key _ 0
      push_cast
      ring

theorem principal_criterion_of_eq_three (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {k : ℕ} (hk : Fintype.card F = 8 * k + 3) {θ : PSL(2, F) → ℂ}
    (hθ : BlocksIsClassFunction θ) (h1 : ∃ a : ℤ, Odd a ∧ θ 1 = a)
    (hS : ∀ x ∈ nonsplitTorus ν, x ≠ 1 → ∃ a : ℤ, Odd a ∧ θ x = a) (g : PSL(2, F)) :
    Even (Nat.card (ConjClasses.mk g).carrier) ∨ ∃ a : ℤ, Odd a ∧ θ g = a := by
  have hG4 := four_dvd_card_PSL_of_eq_three hF hk
  have hT : Nat.card (splitTorus F) = 4 * k + 1 := by
    have := card_splitTorus (Ring.two_ne_zero hF) (F := F)
    omega
  apply forall_of_families hF hq hν (P := fun g =>
    Even (Nat.card (ConjClasses.mk g).carrier) ∨ ∃ a : ℤ, Odd a ∧ θ g = a)
  · intro g h hP
    simpa only [card_carrier_conj, hθ g h] using hP
  · exact Or.inr h1
  · intro x hx hx1
    left
    apply even_card_carrier hG4
    obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
    have ht : t ≠ 0 := fun h => hx1 ((mk_unip_eq_one_iff (Ring.two_ne_zero hF) t).mpr h)
    rw [card_centralizer_unip hF ht, hk]
    omega
  · intro x hx hx1
    left
    apply even_card_carrier hG4
    rw [card_centralizer_splitTorus hF hq hx hx1, hT]
    split_ifs <;> omega
  · exact fun x hx hx1 => Or.inr (hS x hx hx1)

theorem psl2_blocks_of_mod_eight_eq_three (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (h8 : Fintype.card F % 8 = 3) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) :
    BlocksPrincipalBlock m PSL(2, F) = {1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} ∧
    (∀ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 →
      BlocksBlockOf m PSL(2, F) (principal α) = {principal α}) ∧
    (∀ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 →
      (β * nonsplitQuadChar ν) ^ 2 ≠ 1 ∧ discrete (β * nonsplitQuadChar ν) ≠ discrete β ∧
      BlocksBlockOf m PSL(2, F) (discrete β) =
        {discrete β, discrete (β * nonsplitQuadChar ν)}) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 8 * k + 3 := ⟨Fintype.card F / 8, by omega⟩
  have hsq : ¬ IsSquare (-1 : F) := by
    rw [isSquare_neg_one_iff_mod_four hF]
    omega
  obtain ⟨hβ01, hβ02⟩ := nonsplitQuadChar_spec hF hν hsq
  obtain ⟨-, hp, hmn, hne, -⟩ := blocksIrr_eq hF hq hν hψ
  have hSt := steinberg_mem_blocksIrr hF hq hν
  have hdeg : (normTwoDegree F : ℂ) / 2 = 4 * k + 1 := by
    rw [normTwoDegree, ite_eq_right hsq, hk, show 8 * k + 3 - 1 = 8 * k + 2 by omega]
    push_cast
    ring
  have hdP : halfPlus hF ψ ν 1 = 4 * k + 1 := by rw [halfPlus_one hF ψ hν, hdeg]
  have hdM : halfMinus hF ψ ν 1 = 4 * k + 1 := by rw [halfMinus_one hF ψ hν, hdeg]
  have hSt1 : steinberg F 1 = 8 * k + 3 := by
    rw [steinberg_one, hk]
    push_cast
    ring
  have hodd : Odd (4 * (k : ℤ) + 1) := ⟨2 * k, by ring⟩
  refine ⟨?_, fun α hα => ?_, fun β hβ => ?_⟩
  ·
    have hne1 : (1 : PSL(2, F) → ℂ) ≠ steinberg F := fun h => by
      have h' := congrFun h 1
      rw [Pi.one_apply, hSt1] at h'
      have : (1 : ℕ) = 8 * k + 3 := by exact_mod_cast h'
      omega
    have hne2 : ∀ θ : PSL(2, F) → ℂ, θ 1 = 4 * k + 1 → (1 : PSL(2, F) → ℂ) ≠ θ := fun θ hθ h => by
      have h' := congrFun h 1
      rw [Pi.one_apply, hθ] at h'
      have : (1 : ℕ) = 4 * k + 1 := by exact_mod_cast h'
      omega
    have hne3 : ∀ θ : PSL(2, F) → ℂ, θ 1 = 4 * k + 1 → steinberg F ≠ θ := fun θ hθ h => by
      have h' := congrFun h 1
      rw [hSt1, hθ] at h'
      have : 8 * k + 3 = 4 * k + 1 := by exact_mod_cast h'
      omega
    set A : Finset (PSL(2, F) → ℂ) := {1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν}
      with hA
    have hadm : BlocksAdmissible m PSL(2, F) (A : Set (PSL(2, F) → ℂ)) := by
      refine admissible_of_finset m (fun χ hχ => ?_) (fun g => ?_)
      · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hχ
        rcases hχ with rfl | rfl | rfl | rfl
        · exact trivial_mem_irr _
        · exact hSt
        · exact hp
        · exact hmn
      · rw [hA, Finset.sum_insert (by simp [hne1, hne2 _ hdP, hne2 _ hdM]),
          Finset.sum_insert (by simp [hne3 _ hdP, hne3 _ hdM]), Finset.sum_pair hne]
        convert principalCoeff_mem_of_eq_three hF hq hν m hm h2 hk g using 2
        rw [Pi.one_apply, Pi.one_apply, hSt1, hdP, hdM, ← halfPlus_add_halfMinus hF ψ ν g]
        ring
    have hsub : BlocksPrincipalBlock m PSL(2, F) ⊆ (A : Set (PSL(2, F) → ℂ)) :=
      blockOf_subset_of_admissible' m hadm (show (1 : PSL(2, F) → ℂ) ∈ (A : Set _) by simp [hA])
    have hcrit : ∀ θ ∈ ({halfPlus hF ψ ν, halfMinus hF ψ ν} : Set (PSL(2, F) → ℂ)),
        θ ∈ BlocksPrincipalBlock m PSL(2, F) := by
      rintro θ (rfl | rfl)
      · refine mem_principalBlock_of_odd m hm h2 hp
          (principal_criterion_of_eq_three hF hq hν hk
            (blocksVChar_isClassFunction (AddSubgroup.subset_closure hp))
            ⟨4 * k + 1, hodd, by rw [hdP]; push_cast; ring⟩ (fun x hx hx1 => ?_))
        rw [halfPlus_of_mem_nonsplitTorus hF ψ hν hx hx1, ite_eq_right hsq]
        rcases units_hom_value_of_sq hβ02 ⟨x, hx⟩ with h | h
        · exact ⟨-1, by decide, by rw [h]; push_cast; ring⟩
        · exact ⟨1, by decide, by rw [h]; push_cast; ring⟩
      · refine mem_principalBlock_of_odd m hm h2 hmn
          (principal_criterion_of_eq_three hF hq hν hk
            (blocksVChar_isClassFunction (AddSubgroup.subset_closure hmn))
            ⟨4 * k + 1, hodd, by rw [hdM]; push_cast; ring⟩ (fun x hx hx1 => ?_))
        rw [halfMinus_of_mem_nonsplitTorus hF ψ hν hx hx1, ite_eq_right hsq]
        rcases units_hom_value_of_sq hβ02 ⟨x, hx⟩ with h | h
        · exact ⟨-1, by decide, by rw [h]; push_cast; ring⟩
        · exact ⟨1, by decide, by rw [h]; push_cast; ring⟩
    apply Set.Subset.antisymm (by simpa [hA] using hsub)
    intro θ hθ
    rcases hθ with rfl | rfl | rfl | rfl
    · exact trivial_mem_principal m _
    · exact mem_principalBlock_of_odd m hm h2 hSt
        (principal_criterion_of_eq_three hF hq hν hk
          (blocksVChar_isClassFunction steinberg_mem_blocksVChar)
          ⟨8 * k + 3, ⟨4 * k + 1, by ring⟩, by rw [hSt1]; push_cast; ring⟩
          (fun x hx hx1 => ⟨-1, by decide, by
            rw [steinberg_of_mem_nonsplitTorus hν hx hx1]; push_cast; ring⟩))
    · exact hcrit _ (Or.inl rfl)
    · exact hcrit _ (Or.inr rfl)
  ·
    have hR := principal_mem_blocksIrr hF hq hν hα
    refine blockOf_eq_singleton m hm h2 hR (N := (8 * k + 3) * (4 * k + 1))
      (Odd.mul (⟨4 * k + 1, by ring⟩ : Odd (8 * (k : ℤ) + 3)) hodd) ?_
    rw [card_PSL_of_eq_three hF hk, principal_one hF, hk]
    push_cast
    ring
  ·
    have hS : Nat.card (nonsplitTorus ν) % 4 = 2 := by
      have := card_nonsplitTorus hF hν
      omega
    have hsq' : (β * nonsplitQuadChar ν) ^ 2 ≠ 1 := by
      rw [units_hom_mul_sq hβ02]
      exact hβ
    have hD := discrete_mem_blocksIrr hF hq hν hβ
    have hD' := discrete_mem_blocksIrr hF hq hν hsq'
    have hne' : discrete (β * nonsplitQuadChar ν) ≠ discrete β := by
      rw [Ne, discrete_eq_iff hF hq hν hβ, not_or]
      exact ⟨units_hom_mul_ne_self hβ01, units_hom_mul_ne_inv hS hβ hβ02⟩
    refine ⟨hsq', hne', ?_⟩
    refine blockOf_eq_pair m hm h2 hD hD' (Ne.symm hne') (by rw [discrete_one hF hν,
      discrete_one hF hν]) (discrete_mul_eq_or_eq_neg hF hq hν β hβ02)
      (N := (8 * k + 3) * (2 * k + 1))
      (Odd.mul (⟨4 * k + 1, by ring⟩ : Odd (8 * (k : ℤ) + 3)) ⟨k, by ring⟩) ?_
    rw [card_PSL_of_eq_three hF hk, discrete_one hF hν, hk]
    push_cast
    ring

theorem psl2_blocks_eq_of_mod_eight_eq_three (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (h8 : Fintype.card F % 8 = 3) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) :
    {B | BlocksIsBlock m PSL(2, F) B} =
      {({1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} : Set (PSL(2, F) → ℂ))} ∪
      {B | ∃ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 ∧ B = {principal α}} ∪
      {B | ∃ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 ∧
        B = {discrete β, discrete (β * nonsplitQuadChar ν)}} := by
  obtain ⟨hP, hR, hD⟩ := psl2_blocks_of_mod_eight_eq_three hF hq hν hψ h8 m hm h2
  obtain ⟨hIrr, -, hRI, hDI, -⟩ := psl2_character_table hF hq hν hψ
  have hB0 : ∀ θ ∈ BlocksPrincipalBlock m PSL(2, F),
      BlocksBlockOf m PSL(2, F) θ = {1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} :=
    fun θ hθ => (blockOf_eq_of_mem m (trivial_mem_irr _) hθ).trans hP
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    rw [hIrr] at hχ
    rcases hχ with rfl | rfl | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩ | rfl | rfl
    · exact Or.inl (Or.inl hP)
    · exact Or.inl (Or.inl (hB0 _ (by rw [hP]; simp)))
    · exact Or.inl (Or.inr ⟨α, hα, hR α hα⟩)
    · exact Or.inr ⟨β, hβ, (hD β hβ).2.2⟩
    · exact Or.inl (Or.inl (hB0 _ (by rw [hP]; simp)))
    · exact Or.inl (Or.inl (hB0 _ (by rw [hP]; simp)))
  · rintro ((rfl | ⟨α, hα, rfl⟩) | ⟨β, hβ, rfl⟩)
    · exact ⟨fun _ => 1, trivial_mem_irr _, hP.symm⟩
    · exact ⟨principal α, hRI α hα, (hR α hα).symm⟩
    · exact ⟨discrete β, hDI β hβ, ((hD β hβ).2.2).symm⟩

end ThreeModEight

section FiveModEight

omit [DecidableEq F] in
theorem card_PSL_of_eq_five (hF : ringChar F ≠ 2) {k : ℕ} (hk : Fintype.card F = 8 * k + 5) :
    (Nat.card PSL(2, F) : ℂ) = 4 * (8 * k + 5) * (8 * k ^ 2 + 10 * k + 3) := by
  rw [card_PSL_complex hF, hk]
  push_cast
  ring

omit [DecidableEq F] in
theorem four_dvd_card_PSL_of_eq_five (hF : ringChar F ≠ 2) {k : ℕ}
    (hk : Fintype.card F = 8 * k + 5) : 4 ∣ Nat.card PSL(2, F) := by
  refine ⟨(8 * k + 5) * (8 * k ^ 2 + 10 * k + 3), ?_⟩
  have : (Nat.card PSL(2, F) : ℂ) =
      ((4 * ((8 * k + 5) * (8 * k ^ 2 + 10 * k + 3)) : ℕ) : ℂ) := by
    rw [card_PSL_of_eq_five hF hk]
    push_cast
    ring
  exact_mod_cast this

theorem principalCoeff_mem_of_eq_five (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (h2 : (2 : BlocksAlgInt) ∈ m)
    {k : ℕ} (hk : Fintype.card F = 8 * k + 5) (g : PSL(2, F)) :
    (1 + (8 * k + 5 : ℂ) * steinberg F g + (4 * k + 3 : ℂ) * normTwoChar F ν g) /
      (Nat.card PSL(2, F) : ℂ) ∈ BlocksLocalRing m := by
  have hsq : IsSquare (-1 : F) := by
    rw [isSquare_neg_one_iff_mod_four hF]
    omega
  have hN : Odd ((8 * k + 5) * (8 * k ^ 2 + 10 * k + 3) : ℤ) :=
    Odd.mul (⟨4 * k + 2, by ring⟩ : Odd (8 * (k : ℤ) + 5)) ⟨4 * k ^ 2 + 5 * k + 1, by ring⟩
  have key : ∀ (x : ℂ) (n : ℤ), x = 4 * n →
      x / (Nat.card PSL(2, F) : ℂ) ∈ BlocksLocalRing m := by
    intro x n hx
    have : x / (Nat.card PSL(2, F) : ℂ) =
        (n : ℂ) / (((8 * k + 5) * (8 * k ^ 2 + 10 * k + 3) : ℤ) : ℂ) := by
      rw [hx, card_PSL_of_eq_five hF hk, mul_assoc 4]
      push_cast
      rw [mul_div_mul_left _ _ (by norm_num : (4 : ℂ) ≠ 0)]
    rw [this]
    exact div_odd_mem_localRing m hm h2 (intCast_mem_localRing m hm n) hN
  apply forall_of_families hF hq hν (P := fun g =>
    (1 + (8 * k + 5 : ℂ) * steinberg F g + (4 * k + 3 : ℂ) * normTwoChar F ν g) /
      (Nat.card PSL(2, F) : ℂ) ∈ BlocksLocalRing m)
  · intro g h hP
    simpa only [blocksVChar_isClassFunction steinberg_mem_blocksVChar g h,
      blocksVChar_isClassFunction normTwoChar_mem_blocksVChar g h] using hP
  · apply key _ (24 * k ^ 2 + 32 * k + 11)
    rw [steinberg_one, normTwoChar_one hF hν, normTwoDegree, ite_eq_left hsq, hk]
    push_cast
    ring
  · intro x hx hx1
    apply key _ (k + 1)
    rw [steinberg_of_mem_unipotent hF hx hx1, normTwoChar_of_mem_unipotent hF hν hx hx1,
      ite_eq_left hsq]
    push_cast
    ring
  · intro x hx hx1
    rw [steinberg_of_mem_splitTorus hx hx1, normTwoChar_of_mem_splitTorus hF hν hx hx1,
      ite_eq_left hsq]
    rcases units_hom_value_of_sq (splitQuadChar_spec hF hsq).2 ⟨x, hx⟩ with h | h
    · rw [h]
      apply key _ (4 * k + 3)
      push_cast
      ring
    · rw [h]
      apply key _ 0
      push_cast
      ring
  · intro x hx hx1
    apply key _ (-(2 * k + 1))
    rw [steinberg_of_mem_nonsplitTorus hν hx hx1, normTwoChar_of_mem_nonsplitTorus hF hν hx hx1,
      ite_eq_left hsq]
    push_cast
    ring

theorem principal_criterion_of_eq_five (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {k : ℕ} (hk : Fintype.card F = 8 * k + 5) {θ : PSL(2, F) → ℂ}
    (hθ : BlocksIsClassFunction θ) (h1 : ∃ a : ℤ, Odd a ∧ θ 1 = a)
    (hT : ∀ x ∈ splitTorus F, x ≠ 1 → ∃ a : ℤ, Odd a ∧ θ x = a) (g : PSL(2, F)) :
    Even (Nat.card (ConjClasses.mk g).carrier) ∨ ∃ a : ℤ, Odd a ∧ θ g = a := by
  have hG4 := four_dvd_card_PSL_of_eq_five hF hk
  have hS : Nat.card (nonsplitTorus ν) = 4 * k + 3 := by
    have := card_nonsplitTorus hF hν
    omega
  apply forall_of_families hF hq hν (P := fun g =>
    Even (Nat.card (ConjClasses.mk g).carrier) ∨ ∃ a : ℤ, Odd a ∧ θ g = a)
  · intro g h hP
    simpa only [card_carrier_conj, hθ g h] using hP
  · exact Or.inr h1
  · intro x hx hx1
    left
    apply even_card_carrier hG4
    obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
    have ht : t ≠ 0 := fun h => hx1 ((mk_unip_eq_one_iff (Ring.two_ne_zero hF) t).mpr h)
    rw [card_centralizer_unip hF ht, hk]
    omega
  · exact fun x hx hx1 => Or.inr (hT x hx hx1)
  · intro x hx hx1
    left
    apply even_card_carrier hG4
    rw [card_centralizer_nonsplitTorus hF hq hν hx hx1, hS]
    split_ifs <;> omega

theorem psl2_blocks_of_mod_eight_eq_five (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (h8 : Fintype.card F % 8 = 5) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) :
    BlocksPrincipalBlock m PSL(2, F) = {1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} ∧
    (∀ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 →
      BlocksBlockOf m PSL(2, F) (discrete β) = {discrete β}) ∧
    (∀ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 →
      (α * splitQuadChar F) ^ 2 ≠ 1 ∧ principal (α * splitQuadChar F) ≠ principal α ∧
      BlocksBlockOf m PSL(2, F) (principal α) =
        {principal α, principal (α * splitQuadChar F)}) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card F = 8 * k + 5 := ⟨Fintype.card F / 8, by omega⟩
  have hsq : IsSquare (-1 : F) := by
    rw [isSquare_neg_one_iff_mod_four hF]
    omega
  obtain ⟨hα01, hα02⟩ := splitQuadChar_spec hF hsq
  obtain ⟨-, hp, hmn, hne, -⟩ := blocksIrr_eq hF hq hν hψ
  have hSt := steinberg_mem_blocksIrr hF hq hν
  have hdeg : (normTwoDegree F : ℂ) / 2 = 4 * k + 3 := by
    rw [normTwoDegree, ite_eq_left hsq, hk]
    push_cast
    ring
  have hdP : halfPlus hF ψ ν 1 = 4 * k + 3 := by rw [halfPlus_one hF ψ hν, hdeg]
  have hdM : halfMinus hF ψ ν 1 = 4 * k + 3 := by rw [halfMinus_one hF ψ hν, hdeg]
  have hSt1 : steinberg F 1 = 8 * k + 5 := by
    rw [steinberg_one, hk]
    push_cast
    ring
  have hodd : Odd (4 * (k : ℤ) + 3) := ⟨2 * k + 1, by ring⟩
  refine ⟨?_, fun β hβ => ?_, fun α hα => ?_⟩
  ·
    have hne1 : (1 : PSL(2, F) → ℂ) ≠ steinberg F := fun h => by
      have h' := congrFun h 1
      rw [Pi.one_apply, hSt1] at h'
      have : (1 : ℕ) = 8 * k + 5 := by exact_mod_cast h'
      omega
    have hne2 : ∀ θ : PSL(2, F) → ℂ, θ 1 = 4 * k + 3 → (1 : PSL(2, F) → ℂ) ≠ θ := fun θ hθ h => by
      have h' := congrFun h 1
      rw [Pi.one_apply, hθ] at h'
      have : (1 : ℕ) = 4 * k + 3 := by exact_mod_cast h'
      omega
    have hne3 : ∀ θ : PSL(2, F) → ℂ, θ 1 = 4 * k + 3 → steinberg F ≠ θ := fun θ hθ h => by
      have h' := congrFun h 1
      rw [hSt1, hθ] at h'
      have : 8 * k + 5 = 4 * k + 3 := by exact_mod_cast h'
      omega
    set A : Finset (PSL(2, F) → ℂ) := {1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν}
      with hA
    have hadm : BlocksAdmissible m PSL(2, F) (A : Set (PSL(2, F) → ℂ)) := by
      refine admissible_of_finset m (fun χ hχ => ?_) (fun g => ?_)
      · simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hχ
        rcases hχ with rfl | rfl | rfl | rfl
        · exact trivial_mem_irr _
        · exact hSt
        · exact hp
        · exact hmn
      · rw [hA, Finset.sum_insert (by simp [hne1, hne2 _ hdP, hne2 _ hdM]),
          Finset.sum_insert (by simp [hne3 _ hdP, hne3 _ hdM]), Finset.sum_pair hne]
        convert principalCoeff_mem_of_eq_five hF hq hν m hm h2 hk g using 2
        rw [Pi.one_apply, Pi.one_apply, hSt1, hdP, hdM, ← halfPlus_add_halfMinus hF ψ ν g]
        ring
    have hsub : BlocksPrincipalBlock m PSL(2, F) ⊆ (A : Set (PSL(2, F) → ℂ)) :=
      blockOf_subset_of_admissible' m hadm (show (1 : PSL(2, F) → ℂ) ∈ (A : Set _) by simp [hA])
    have hcrit : ∀ θ ∈ ({halfPlus hF ψ ν, halfMinus hF ψ ν} : Set (PSL(2, F) → ℂ)),
        θ ∈ BlocksPrincipalBlock m PSL(2, F) := by
      rintro θ (rfl | rfl)
      · refine mem_principalBlock_of_odd m hm h2 hp
          (principal_criterion_of_eq_five hF hq hν hk
            (blocksVChar_isClassFunction (AddSubgroup.subset_closure hp))
            ⟨4 * k + 3, hodd, by rw [hdP]; push_cast; ring⟩ (fun x hx hx1 => ?_))
        rw [halfPlus_of_mem_splitTorus hF ψ hν hx hx1, ite_eq_left hsq]
        rcases units_hom_value_of_sq hα02 ⟨x, hx⟩ with h | h
        · exact ⟨1, by decide, by rw [h]; push_cast; ring⟩
        · exact ⟨-1, by decide, by rw [h]; push_cast; ring⟩
      · refine mem_principalBlock_of_odd m hm h2 hmn
          (principal_criterion_of_eq_five hF hq hν hk
            (blocksVChar_isClassFunction (AddSubgroup.subset_closure hmn))
            ⟨4 * k + 3, hodd, by rw [hdM]; push_cast; ring⟩ (fun x hx hx1 => ?_))
        rw [halfMinus_of_mem_splitTorus hF ψ hν hx hx1, ite_eq_left hsq]
        rcases units_hom_value_of_sq hα02 ⟨x, hx⟩ with h | h
        · exact ⟨1, by decide, by rw [h]; push_cast; ring⟩
        · exact ⟨-1, by decide, by rw [h]; push_cast; ring⟩
    apply Set.Subset.antisymm (by simpa [hA] using hsub)
    intro θ hθ
    rcases hθ with rfl | rfl | rfl | rfl
    · exact trivial_mem_principal m _
    · exact mem_principalBlock_of_odd m hm h2 hSt
        (principal_criterion_of_eq_five hF hq hν hk
          (blocksVChar_isClassFunction steinberg_mem_blocksVChar)
          ⟨8 * k + 5, ⟨4 * k + 2, by ring⟩, by rw [hSt1]; push_cast; ring⟩
          (fun x hx hx1 => ⟨1, by decide, by
            rw [steinberg_of_mem_splitTorus hx hx1]; push_cast; ring⟩))
    · exact hcrit _ (Or.inl rfl)
    · exact hcrit _ (Or.inr rfl)
  ·
    have hD := discrete_mem_blocksIrr hF hq hν hβ
    refine blockOf_eq_singleton m hm h2 hD (N := (8 * k + 5) * (4 * k + 3))
      (Odd.mul (⟨4 * k + 2, by ring⟩ : Odd (8 * (k : ℤ) + 5)) hodd) ?_
    rw [card_PSL_of_eq_five hF hk, discrete_one hF hν, hk]
    push_cast
    ring
  ·
    have hT : Nat.card (splitTorus F) % 4 = 2 := by
      have := card_splitTorus (Ring.two_ne_zero hF) (F := F)
      omega
    have hsq' : (α * splitQuadChar F) ^ 2 ≠ 1 := by
      rw [units_hom_mul_sq hα02]
      exact hα
    have hR := principal_mem_blocksIrr hF hq hν hα
    have hR' := principal_mem_blocksIrr hF hq hν hsq'
    have hne' : principal (α * splitQuadChar F) ≠ principal α := by
      rw [Ne, principal_eq_iff hF hq hν hα, not_or]
      exact ⟨units_hom_mul_ne_self hα01, units_hom_mul_ne_inv hT hα hα02⟩
    refine ⟨hsq', hne', ?_⟩
    refine blockOf_eq_pair m hm h2 hR hR' (Ne.symm hne') (by rw [principal_one hF,
      principal_one hF]) (principal_mul_eq_or_eq_neg hF hq hν α hα02)
      (N := (8 * k + 5) * (2 * k + 1))
      (Odd.mul (⟨4 * k + 2, by ring⟩ : Odd (8 * (k : ℤ) + 5)) ⟨k, by ring⟩) ?_
    rw [card_PSL_of_eq_five hF hk, principal_one hF, hk]
    push_cast
    ring

theorem psl2_blocks_eq_of_mod_eight_eq_five (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (h8 : Fintype.card F % 8 = 5) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (h2 : (2 : BlocksAlgInt) ∈ m) :
    {B | BlocksIsBlock m PSL(2, F) B} =
      {({1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} : Set (PSL(2, F) → ℂ))} ∪
      {B | ∃ β : nonsplitTorus ν →* ℂˣ, β ^ 2 ≠ 1 ∧ B = {discrete β}} ∪
      {B | ∃ α : splitTorus F →* ℂˣ, α ^ 2 ≠ 1 ∧
        B = {principal α, principal (α * splitQuadChar F)}} := by
  obtain ⟨hP, hD, hR⟩ := psl2_blocks_of_mod_eight_eq_five hF hq hν hψ h8 m hm h2
  obtain ⟨hIrr, -, hRI, hDI, -⟩ := psl2_character_table hF hq hν hψ
  have hB0 : ∀ θ ∈ BlocksPrincipalBlock m PSL(2, F),
      BlocksBlockOf m PSL(2, F) θ = {1, steinberg F, halfPlus hF ψ ν, halfMinus hF ψ ν} :=
    fun θ hθ => (blockOf_eq_of_mem m (trivial_mem_irr _) hθ).trans hP
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    rw [hIrr] at hχ
    rcases hχ with rfl | rfl | ⟨α, hα, rfl⟩ | ⟨β, hβ, rfl⟩ | rfl | rfl
    · exact Or.inl (Or.inl hP)
    · exact Or.inl (Or.inl (hB0 _ (by rw [hP]; simp)))
    · exact Or.inr ⟨α, hα, (hR α hα).2.2⟩
    · exact Or.inl (Or.inr ⟨β, hβ, hD β hβ⟩)
    · exact Or.inl (Or.inl (hB0 _ (by rw [hP]; simp)))
    · exact Or.inl (Or.inl (hB0 _ (by rw [hP]; simp)))
  · rintro ((rfl | ⟨β, hβ, rfl⟩) | ⟨α, hα, rfl⟩)
    · exact ⟨fun _ => 1, trivial_mem_irr _, hP.symm⟩
    · exact ⟨discrete β, hDI β hβ, (hD β hβ).symm⟩
    · exact ⟨principal α, hRI α hα, ((hR α hα).2.2).symm⟩

end FiveModEight

end CFSG.PSL2Table
