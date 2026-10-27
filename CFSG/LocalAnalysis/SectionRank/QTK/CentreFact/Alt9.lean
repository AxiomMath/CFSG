module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Pair
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup Equiv

@[expose] def alt9a : Perm (Fin 9) := swap 0 1 * swap 1 2

@[expose] def alt9b : Perm (Fin 9) := swap 3 4 * swap 4 5

@[expose] def alt9x : Perm (Fin 9) := swap 0 1 * swap 2 8

@[expose] def alt9y : Perm (Fin 9) := swap 0 2 * swap 1 8

@[expose] def alt9d₁ : Perm (Fin 9) := swap 0 1 * swap 6 7

@[expose] def alt9d₂ : Perm (Fin 9) := swap 3 4 * swap 6 7

theorem alt9_signs : Perm.sign alt9a = 1 ∧ Perm.sign alt9b = 1 ∧ Perm.sign alt9x = 1 ∧
    Perm.sign alt9y = 1 ∧ Perm.sign alt9d₁ = 1 ∧ Perm.sign alt9d₂ = 1 := by
  decide +kernel

theorem alt9_rels : alt9a ^ 3 = 1 ∧ alt9b ^ 3 = 1 ∧ alt9a * alt9b = alt9b * alt9a ∧
    alt9x ^ 2 = 1 ∧ alt9y ^ 2 = 1 ∧ alt9x * alt9y = alt9y * alt9x ∧ alt9x ≠ 1 ∧
    alt9a * alt9x * alt9a⁻¹ = alt9x * alt9y ∧ alt9a * alt9y * alt9a⁻¹ = alt9x ∧
    alt9a⁻¹ * alt9x * alt9a = alt9y ∧ alt9a⁻¹ * alt9y * alt9a = alt9x * alt9y ∧
    alt9b * alt9x = alt9x * alt9b ∧ alt9b * alt9y = alt9y * alt9b ∧
    alt9d₁ * alt9a * alt9d₁⁻¹ = alt9a⁻¹ ∧ alt9d₁ * alt9b * alt9d₁⁻¹ = alt9a ^ 0 * alt9b ^ 1 ∧
    alt9d₂ * alt9b * alt9d₂⁻¹ = alt9b⁻¹ := by
  decide +kernel

theorem alt9_ind : ∀ i j : ℕ, i < 3 → j < 3 → alt9a ^ i * alt9b ^ j = 1 → i = 0 ∧ j = 0 := by
  intro i j hi hj
  interval_cases i <;> interval_cases j <;> decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_center_of_alt_nine (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    (e : ↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin 9)) : ¬ 3 ∣ Nat.card (center ↥Y) := by
  obtain ⟨sa, sb, sx, sy, s₁, s₂⟩ := alt9_signs
  obtain ⟨ra, rb, rab, rx2, ry2, rxy, rx1, rax, ray, rax', ray', rbx, rby, r₁a, r₁b, r₂b⟩ :=
    alt9_rels
  let A : alternatingGroup (Fin 9) := ⟨alt9a, sa⟩
  let B : alternatingGroup (Fin 9) := ⟨alt9b, sb⟩
  let X : alternatingGroup (Fin 9) := ⟨alt9x, sx⟩
  let Z : alternatingGroup (Fin 9) := ⟨alt9y, sy⟩
  let D₁ : alternatingGroup (Fin 9) := ⟨alt9d₁, s₁⟩
  let D₂ : alternatingGroup (Fin 9) := ⟨alt9d₂, s₂⟩
  have hXZ : Commute X Z := Subtype.ext rxy
  have hXi : X ≠ 1 := fun h => rx1 (congrArg Subtype.val h)
  have hXs : X ∈ zpowers X ⊔ zpowers Z := mem_sup_left (mem_zpowers X)
  have hZs : Z ∈ zpowers X ⊔ zpowers Z := mem_sup_right (mem_zpowers Z)
  refine not_dvd_card_center_of_pair_equiv he e Nat.prime_three (by norm_num)
    (R := zpowers X ⊔ zpowers Z) ?_
    (IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_sq (Subtype.ext rx2))
      (isPGroup_zpowers_of_sq (Subtype.ext ry2))
      (zpowers_le.2 (mem_normalizer_zpowers hXZ.symm)))
    (a := A) (b := B) (d₁ := D₁) (d₂ := D₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (k := 0) (l := 1) ?_
    (by norm_num) ?_
  · intro h
    rw [eq_bot_iff] at h
    exact hXi (Subgroup.mem_bot.mp (h hXs))
  · refine mem_normalizer_sup_zpowers ?_ ?_ ?_ ?_
    · rw [show A * X * A⁻¹ = X * Z from Subtype.ext rax]; exact mul_mem hXs hZs
    · rw [show A * Z * A⁻¹ = X from Subtype.ext ray]; exact hXs
    · rw [show A⁻¹ * X * A = Z from Subtype.ext rax']; exact hZs
    · rw [show A⁻¹ * Z * A = X * Z from Subtype.ext ray']; exact mul_mem hXs hZs
  · exact mem_normalizer_sup_of_commute (Subtype.ext rbx) (Subtype.ext rby)
  · exact Subtype.ext ra
  · exact Subtype.ext rb
  · exact Subtype.ext rab
  · intro i j hi hj h
    exact alt9_ind i j hi hj (congrArg Subtype.val h)
  · exact Subtype.ext r₁a
  · exact Subtype.ext r₁b
  · exact Subtype.ext r₂b

end CFSG.SectionRank.QTK.CentreFact
