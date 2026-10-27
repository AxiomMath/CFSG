module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBBasic
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
import CFSG.RankThree.PartTwo.Sec4.Census.Alternating46

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup Equiv

@[expose] def alt10a : Perm (Fin 10) := swap 0 1 * swap 1 2

@[expose] def alt10b : Perm (Fin 10) := swap 4 5 * swap 5 6

@[expose] def alt10t : Perm (Fin 10) := swap 3 7 * swap 8 9

@[expose] def alt10d₁ : Perm (Fin 10) := swap 0 1 * swap 7 8

@[expose] def alt10d₂ : Perm (Fin 10) := swap 4 5 * swap 7 8

theorem alt10_signs : Perm.sign alt10a = 1 ∧ Perm.sign alt10b = 1 ∧ Perm.sign alt10t = 1 ∧
    Perm.sign alt10d₁ = 1 ∧ Perm.sign alt10d₂ = 1 := by
  decide +kernel

theorem alt10_rels : alt10a ^ 3 = 1 ∧ alt10b ^ 3 = 1 ∧ alt10a * alt10b = alt10b * alt10a ∧
    alt10t ^ 2 = 1 ∧ alt10t ≠ 1 ∧ alt10a * alt10t = alt10t * alt10a ∧
    alt10b * alt10t = alt10t * alt10b ∧ alt10d₁ * alt10a * alt10d₁⁻¹ = alt10a⁻¹ ∧
    alt10d₁ * alt10b * alt10d₁⁻¹ = alt10b ∧ alt10d₂ * alt10b * alt10d₂⁻¹ = alt10b⁻¹ := by
  decide +kernel

theorem alt10_ind : ∀ i j : ℕ, i < 3 → j < 3 → alt10a ^ i * alt10b ^ j = 1 → i = 0 ∧ j = 0 := by
  intro i j hi hj
  interval_cases i <;> interval_cases j <;> decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem le_nine_of_alt (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G} {n : ℕ}
    (e : ↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin n)) : n ≤ 9 := by
  by_contra h9
  have hn : 10 ≤ n := by omega
  by_cases h3 : 3 ∣ Nat.card (center ↥Y)
  · obtain ⟨sa, sb, st, s₁, s₂⟩ := alt10_signs
    obtain ⟨ra, rb, rab, rt, rt1, rat, rbt, r₁a, r₁b, r₂b⟩ := alt10_rels
    set ι := altEmbed hn
    have hι := altEmbed_injective hn
    let A : alternatingGroup (Fin 10) := ⟨alt10a, sa⟩
    let B : alternatingGroup (Fin 10) := ⟨alt10b, sb⟩
    let T : alternatingGroup (Fin 10) := ⟨alt10t, st⟩
    let D₁ : alternatingGroup (Fin 10) := ⟨alt10d₁, s₁⟩
    let D₂ : alternatingGroup (Fin 10) := ⟨alt10d₂, s₂⟩
    have key : ∀ x y : alternatingGroup (Fin 10), (x : Perm (Fin 10)) = y → ι x = ι y :=
      fun x y h => congrArg ι (Subtype.ext h)
    refine not_dvd_card_center_of_signed_inv he e Nat.prime_three (by norm_num)
      (t := ι T) (a := ι A) (b := ι B) (d₁ := ι D₁) (d₂ := ι D₂) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ h3
    · rw [← map_pow]; exact (key _ 1 rt).trans (map_one ι)
    · intro h
      exact rt1 (congrArg Subtype.val (hι (h.trans (map_one ι).symm)))
    · rw [Commute, SemiconjBy, ← map_mul, ← map_mul]; exact key _ _ rat
    · rw [Commute, SemiconjBy, ← map_mul, ← map_mul]; exact key _ _ rbt
    · rw [← map_pow]; exact (key _ 1 ra).trans (map_one ι)
    · rw [← map_pow]; exact (key _ 1 rb).trans (map_one ι)
    · rw [← map_mul, ← map_mul]; exact key _ _ rab
    · intro i j hi hj h
      rw [← map_pow, ← map_pow, ← map_mul] at h
      exact alt10_ind i j hi hj (congrArg Subtype.val (hι (h.trans (map_one ι).symm)))
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]; exact key _ _ r₁a
    · rw [← map_inv, ← map_mul, ← map_mul]; exact key _ _ r₁b
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]; exact key _ _ r₂b
  · exact false_of_three_le_localRank he e Nat.prime_three (by norm_num) h3
      (CFSG.RankThree.PartTwo.Sec4.Census.three_le_localRank_alternating hn)

end CFSG.SectionRank.QTK.CoverB
