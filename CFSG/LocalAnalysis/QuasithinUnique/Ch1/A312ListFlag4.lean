module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag3
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Classification

theorem maxBlock_eq_or_disjoint {I : Set ℕ} {n a m a₂ m₂ : ℕ}
    (h : a + m ≤ n) (h₂ : a₂ + m₂ ≤ n) (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    (ha₂ : a₂ = 0 ∨ a₂ ∈ I) (hb₂ : a₂ + m₂ = n ∨ a₂ + m₂ ∈ I)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) (hno₂ : ∀ c ∈ I, ¬ (a₂ < c ∧ c < a₂ + m₂)) :
    (a₂ = a ∧ m₂ = m) ∨ a₂ + m₂ ≤ a ∨ a + m ≤ a₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, h1, h2⟩ := hcon
  rcases lt_trichotomy a a₂ with hlt | heq | hgt
  · have hI : a₂ ∈ I := ha₂.resolve_left (by omega)
    exact hno a₂ hI ⟨hlt, by omega⟩
  · subst heq
    rcases lt_trichotomy (a + m₂) (a + m) with hlt | heq | hgt
    · have hI : a + m₂ ∈ I := hb₂.resolve_left (by omega)
      exact hno _ hI ⟨by omega, hlt⟩
    · exact hne rfl (by omega)
    · have hI : a + m ∈ I := hb.resolve_left (by omega)
      exact hno₂ _ hI ⟨by omega, hgt⟩
  · have hI : a ∈ I := ha.resolve_left (by omega)
    exact hno₂ a hI ⟨hgt, by omega⟩

variable {n : ℕ} {K : Type*} [Field K]

theorem blkAt_zero (a : ℕ) (h : a + 0 ≤ n) (A : Matrix (Fin n) (Fin n) K) :
    blkAt a 0 h A = 1 := by
  ext i j
  exact i.elim0

theorem isPGroup_unitriangular_charTwo [Finite K] [CharP K 2] (hn : 1 ≤ n) :
    IsPGroup 2 ↥(unitriangular n K) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) hn
  have := P.isPGroup'
  rw [hP] at this
  exact this

theorem unitriangular_of_bigBlockHom [Finite K] (hK : Nat.card K = 2) (hn5 : n ≤ 5) {I : Set ℕ}
    {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m) (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) (x : ↥(perfectCore (flagStabilizer n K I)))
    (hx : bigBlockHom I a m h ha hb x = 1) :
    (x : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K := by
  refine mem_unitriangular_of_blocks (perfectCore_le _ x.2) fun a₂ m₂ h₂ ha₂ hb₂ hno₂ => ?_
  by_cases hm₂ : m₂ = 0
  · subst hm₂
    exact blkAt_zero a₂ h₂ _
  · rcases maxBlock_eq_or_disjoint h h₂ ha hb ha₂ hb₂ hno hno₂ with
      ⟨rfl, rfl⟩ | hd | hd
    · exact congrArg Subtype.val hx
    · exact blkAt_eq_one_of_small hK h₂ ha₂ hb₂ (by omega) (perfectCore_le _)
        (Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)) x
    · exact blkAt_eq_one_of_small hK h₂ ha₂ hb₂ (by omega) (perfectCore_le _)
        (Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)) x

theorem perfectCore_eq_bot_of_small [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hn : 1 ≤ n)
    {I : Set ℕ} (hsmall : ∀ a m : ℕ, a + m ≤ n → (a = 0 ∨ a ∈ I) → (a + m = n ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2) :
    perfectCore (flagStabilizer n K I) = ⊥ := by
  have hperf : Group.IsPerfect ↥(perfectCore (flagStabilizer n K I)) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  have hle : perfectCore (flagStabilizer n K I) ≤ unitriangular n K := fun x hx =>
    mem_unitriangular_of_blocks (perfectCore_le _ hx) fun a m h ha hb hno =>
      blkAt_eq_one_of_small hK h ha hb (hsmall a m h ha hb hno) (perfectCore_le _) hperf ⟨x, hx⟩
  have hsolv : Group.IsSolvable ↥(perfectCore (flagStabilizer n K I)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (isPGroup_unitriangular_charTwo (K := K) hn).isNilpotent
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have h1 := (isSolvable_iff_perfectCore_eq_bot (perfectCore (flagStabilizer n K I))).mp hsolv
  rw [perfectCore_eq_self_of_perfect (Subgroup.isPerfect_iff.mp hperf)] at h1
  exact h1

end Classification

end CFSG.QuasithinUnique.Vol2Native.A312L
