module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3
import CFSG.Quasithin.Background.A3FactsClassical

public section

namespace CFSG.SectionRank.QTK

open Subgroup Equiv

theorem isPGroup_sup_zpowers_of_sq_comm {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : Commute a b) :
    IsPGroup 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_sq ha) (isPGroup_zpowers_of_sq hb)
    (Subgroup.zpowers_le.2 (mem_normalizer_zpowers hab.symm))

theorem one_le_localRank_alternating_6 :
    1 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (alternatingGroup (Fin 6)) := by
  let a : alternatingGroup (Fin 6) := ⟨swap 0 1 * swap 2 3, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  let b : alternatingGroup (Fin 6) := ⟨swap 0 2 * swap 1 3, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  let x : alternatingGroup (Fin 6) := ⟨swap 0 1 * swap 1 2, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  have ha : a ^ 2 = 1 := Subtype.ext (by decide)
  have hb : b ^ 2 = 1 := Subtype.ext (by decide)
  have hab : Commute a b := Subtype.ext (by decide)
  have hx3 : x ^ 3 = 1 := Subtype.ext (by decide)
  have hx1 : x ≠ 1 := fun h => absurd (congrArg (fun y : alternatingGroup (Fin 6) =>
    (y : Perm (Fin 6)) 0) h) (by decide)
  have hP1 : a ∈ zpowers a ⊔ zpowers b := mem_sup_left (mem_zpowers a)
  have hP2 : b ∈ zpowers a ⊔ zpowers b := mem_sup_right (mem_zpowers b)
  have hxN : x ∈ normalizer ((zpowers a ⊔ zpowers b : Subgroup _) : Set _) := by
    refine mem_normalizer_sup_zpowers ?_ ?_ ?_ ?_
    · rw [show x * a * x⁻¹ = a * b from Subtype.ext (by decide)]
      exact mul_mem hP1 hP2
    · rw [show x * b * x⁻¹ = a from Subtype.ext (by decide)]
      exact hP1
    · rw [show x⁻¹ * a * x = b from Subtype.ext (by decide)]
      exact hP2
    · rw [show x⁻¹ * b * x = a * b from Subtype.ext (by decide)]
      exact mul_mem hP1 hP2
  have hne : (zpowers a ⊔ zpowers b : Subgroup _) ≠ ⊥ := fun h => by
    have ha1 : a = 1 := Subgroup.mem_bot.mp (h ▸ hP1)
    exact absurd (congrArg (fun y : alternatingGroup (Fin 6) => (y : Perm (Fin 6)) 0) ha1)
      (by decide)
  exact one_le_localRank_of_mem_normalizer (by norm_num) hne
    (isPGroup_sup_zpowers_of_sq_comm ha hb hab) hxN (orderOf_eq_prime hx3 hx1)

theorem one_le_localRank_alternating_7 :
    1 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (alternatingGroup (Fin 7)) := by
  let a : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 2 3, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  let b : alternatingGroup (Fin 7) := ⟨swap 0 2 * swap 1 3, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  let x : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 1 2, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  have ha : a ^ 2 = 1 := Subtype.ext (by decide)
  have hb : b ^ 2 = 1 := Subtype.ext (by decide)
  have hab : Commute a b := Subtype.ext (by decide)
  have hx3 : x ^ 3 = 1 := Subtype.ext (by decide)
  have hx1 : x ≠ 1 := fun h => absurd (congrArg (fun y : alternatingGroup (Fin 7) =>
    (y : Perm (Fin 7)) 0) h) (by decide)
  have hP1 : a ∈ zpowers a ⊔ zpowers b := mem_sup_left (mem_zpowers a)
  have hP2 : b ∈ zpowers a ⊔ zpowers b := mem_sup_right (mem_zpowers b)
  have hxN : x ∈ normalizer ((zpowers a ⊔ zpowers b : Subgroup _) : Set _) := by
    refine mem_normalizer_sup_zpowers ?_ ?_ ?_ ?_
    · rw [show x * a * x⁻¹ = a * b from Subtype.ext (by decide)]
      exact mul_mem hP1 hP2
    · rw [show x * b * x⁻¹ = a from Subtype.ext (by decide)]
      exact hP1
    · rw [show x⁻¹ * a * x = b from Subtype.ext (by decide)]
      exact hP2
    · rw [show x⁻¹ * b * x = a * b from Subtype.ext (by decide)]
      exact mul_mem hP1 hP2
  have hne : (zpowers a ⊔ zpowers b : Subgroup _) ≠ ⊥ := fun h => by
    have ha1 : a = 1 := Subgroup.mem_bot.mp (h ▸ hP1)
    exact absurd (congrArg (fun y : alternatingGroup (Fin 7) => (y : Perm (Fin 7)) 0) ha1)
      (by decide)
  exact one_le_localRank_of_mem_normalizer (by norm_num) hne
    (isPGroup_sup_zpowers_of_sq_comm ha hb hab) hxN (orderOf_eq_prime hx3 hx1)

theorem one_le_localRank_alternating_8 :
    1 ≤ CFSG.Assembly.RankThreeEven.localRank 3 (alternatingGroup (Fin 8)) := by
  let a : alternatingGroup (Fin 8) := ⟨swap 0 1 * swap 2 3, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  let b : alternatingGroup (Fin 8) := ⟨swap 0 2 * swap 1 3, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  let x : alternatingGroup (Fin 8) := ⟨swap 0 1 * swap 1 2, by
    rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide)]
    rfl⟩
  have ha : a ^ 2 = 1 := Subtype.ext (by decide)
  have hb : b ^ 2 = 1 := Subtype.ext (by decide)
  have hab : Commute a b := Subtype.ext (by decide)
  have hx3 : x ^ 3 = 1 := Subtype.ext (by decide)
  have hx1 : x ≠ 1 := fun h => absurd (congrArg (fun y : alternatingGroup (Fin 8) =>
    (y : Perm (Fin 8)) 0) h) (by decide)
  have hP1 : a ∈ zpowers a ⊔ zpowers b := mem_sup_left (mem_zpowers a)
  have hP2 : b ∈ zpowers a ⊔ zpowers b := mem_sup_right (mem_zpowers b)
  have hxN : x ∈ normalizer ((zpowers a ⊔ zpowers b : Subgroup _) : Set _) := by
    refine mem_normalizer_sup_zpowers ?_ ?_ ?_ ?_
    · rw [show x * a * x⁻¹ = a * b from Subtype.ext (by decide)]
      exact mul_mem hP1 hP2
    · rw [show x * b * x⁻¹ = a from Subtype.ext (by decide)]
      exact hP1
    · rw [show x⁻¹ * a * x = b from Subtype.ext (by decide)]
      exact hP2
    · rw [show x⁻¹ * b * x = a * b from Subtype.ext (by decide)]
      exact mul_mem hP1 hP2
  have hne : (zpowers a ⊔ zpowers b : Subgroup _) ≠ ⊥ := fun h => by
    have ha1 : a = 1 := Subgroup.mem_bot.mp (h ▸ hP1)
    exact absurd (congrArg (fun y : alternatingGroup (Fin 8) => (y : Perm (Fin 8)) 0) ha1)
      (by decide)
  exact one_le_localRank_of_mem_normalizer (by norm_num) hne
    (isPGroup_sup_zpowers_of_sq_comm ha hb hab) hxN (orderOf_eq_prime hx3 hx1)

theorem oddLocalWitness_alternating {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) :
    OddLocalWitness (alternatingGroup (Fin n)) := by
  refine ⟨3, Nat.prime_three, by norm_num,
    CFSG.Quasithin.A3Facts.two_le_pRank_alternating (by omega), ?_⟩
  rcases hn with rfl | rfl | rfl
  · exact one_le_localRank_alternating_6
  · exact one_le_localRank_alternating_7
  · exact one_le_localRank_alternating_8

end CFSG.SectionRank.QTK
