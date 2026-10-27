module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import all Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GorensteinWalter

theorem a7t_involution : BenderSuzuki.PFAppendixIII.IsInvolution a7t := by
  unfold BenderSuzuki.PFAppendixIII.IsInvolution
  constructor <;> decide

theorem factorization_two_2520 :
    (2520 : ℕ).factorization 2 = 3 := by
  rw [show 2520 = 2 ^ 3 * 315 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]

lemma conj_mem_centralizer_conj
    {G : Type*} [Group G] (g t x : G)
    (hx : x ∈ Subgroup.centralizer ({t} : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc
    (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
    _ = g * (t * x) * g⁻¹ := by rw [hx]
    _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group

theorem a7t_centralizer_card :
    Nat.card (Subgroup.centralizer ({a7t} : Set A7)) = 24 := by
  let C : Subgroup (Equiv.Perm (Fin 7)) :=
    Subgroup.centralizer ({(a7t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))
  let A : Subgroup (Equiv.Perm (Fin 7)) := alternatingGroup (Fin 7)
  have hAindex : A.index = 2 := alternatingGroup.index_eq_two
  have hcC : (Equiv.swap (4 : Fin 7) 5) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y = (a7t : Equiv.Perm (Fin 7)) := by simpa using hy
    subst y
    decide
  have hcA : (Equiv.swap (4 : Fin 7) 5) ∉ A := by
    intro h
    change Equiv.Perm.sign (Equiv.swap (4 : Fin 7) 5) = 1 at h
    norm_num [Equiv.Perm.sign_swap] at h
    all_goals exact (by decide : (4 : Fin 7) ≠ 5) h
  let D : Subgroup (Equiv.Perm (Fin 7)) := Lattice.inf C A
  have hrel : D.relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨Equiv.swap (4 : Fin 7) 5, hcC, ?_⟩
    intro b hbC
    have hbcC : b * Equiv.swap (4 : Fin 7) 5 ∈ C := C.mul_mem hbC hcC
    by_cases hbA : b ∈ A
    · right
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbC, hbA⟩
      · intro hbc
        have hbcA : b * Equiv.swap (4 : Fin 7) 5 ∈ A :=
          (Subgroup.mem_inf.mp hbc).2
        have hiff : b * Equiv.swap (4 : Fin 7) 5 ∈ A ↔
            (b ∈ A ↔ Equiv.swap (4 : Fin 7) 5 ∈ A) :=
          Subgroup.mul_mem_iff_of_index_two hAindex
        have hbnot : ¬ b ∈ A := by
          intro hbA'
          exact hcA ((hiff.mp hbcA).1 hbA')
        exact hbnot hbA
    · left
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbcC, by
          exact (Subgroup.mul_mem_iff_of_index_two hAindex).2
            (iff_of_false hbA hcA)⟩
      · intro hbD
        exact hbA ((Subgroup.mem_inf.mp hbD).2)
  have hrel' : (D.subgroupOf C).index = 2 := by
    exact hrel
  have hcycleType : (a7t : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
    decide
  have hperm : Nat.card C = 48 := by
    rw [Equiv.Perm.nat_card_centralizer, hcycleType]
    norm_num
  have hDleC : D ≤ C := inf_le_left
  have hcardSub : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleC).toEquiv
  have hcardC : Nat.card D * 2 = Nat.card C := by
    have h := Subgroup.card_mul_index (D.subgroupOf C)
    rw [hcardSub, hrel'] at h
    exact h
  have hcard24 : Nat.card D = 24 := by omega
  have hmap : (Subgroup.centralizer ({a7t} : Set A7)).map A7.subtype = D := by
    ext p
    constructor
    · rintro ⟨x, hxC, rfl⟩
      constructor
      · change (x : Equiv.Perm (Fin 7)) ∈ C
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyP : y = (a7t : Equiv.Perm (Fin 7)) := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hxC) a7t (by simp)
        exact congrArg Subtype.val hcomm
      · exact x.2
    · rintro ⟨hpC, hpA⟩
      refine ⟨⟨p, hpA⟩, ?_, rfl⟩
      have hx : (⟨p, hpA⟩ : A7) ∈ Subgroup.centralizer ({a7t} : Set A7) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyA : y = a7t := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hpC)
          (a7t : Equiv.Perm (Fin 7)) (by simp)
        exact Subtype.ext hcomm
      exact hx
  have hcardMap : Nat.card (Subgroup.centralizer ({a7t} : Set A7)) =
      Nat.card ((Subgroup.centralizer ({a7t} : Set A7)).map A7.subtype) := by
    exact Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({a7t} : Set A7)) A7.subtype
        A7.subtype_injective).toEquiv
  rw [hcardMap, hmap, hcard24]

end CFSG.GorensteinWalter
