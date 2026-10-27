module

public import CFSG.ClassicalInvolution.Q3.WeakBalance
public import CFSG.ClassicalInvolution.Q3.StrongBalance

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_mem_signalizerFunctorEk_of_mem {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {x : G} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ F ∈ signalizerFunctorEk 2 2 A, x ∈ F := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : ∀ y ∈ A, y * y = 1 := fun y hy => by
    rw [← pow_two]
    exact hA.2 y hy
  obtain ⟨n, hn⟩ := (isPGroup_two_of_mul_self_eq_one hsq).exists_card_eq
  have h4 : 2 ^ (1 + 1) ∣ Nat.card ↥A := by
    rw [hn]
    refine Nat.pow_dvd_pow 2 ?_
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set x' : ↥A := ⟨x, hx⟩ with hx'
  have hord : orderOf x' = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using hsq x hx)
    · intro h
      exact hx1 (congrArg Subtype.val h)
  have hHc : Nat.card (Subgroup.zpowers x') = 2 ^ 1 := by
    rw [Nat.card_zpowers, hord]
    norm_num
  obtain ⟨K, hKc, hHK⟩ := Sylow.exists_subgroup_card_pow_succ (G := ↥A) (p := 2) (n := 1) h4 hHc
  refine ⟨K.map A.subtype, ⟨?_, ?_⟩, ?_⟩
  · intro y hy
    obtain ⟨z, -, rfl⟩ := hy
    exact z.2
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hKc]
  · exact ⟨x', hHK (Subgroup.mem_zpowers x'), rfl⟩

theorem le_centralizer_involutionOddCore_of_covered (hΩ : ConjInvariant Ω)
    (hO : LocalOddCentralizer3 Ω) {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAY : ∀ b ∈ A, b ≠ 1 → A ≤ centralizingLayer Ω {b})
    (hnc : ∀ b ∈ A, b ≠ 1 → b ∉ Subgroup.center G) (hSB : StronglyBalanced A)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) {x : G} (hx : x ∈ A) (hx1 : x ≠ 1)
    {L : Subgroup G} (hLΩ : L ∈ Ω) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    {F : Subgroup G} (hF : F ∈ signalizerFunctorEk 2 2 A) (hxF : x ∈ F)
    (hLF : L ≤ Subgroup.centralizer (F : Set G)) :
    L ≤ Subgroup.centralizer (involutionOddCore x : Set G) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hcomm : ⁅r, u⁆ ∈ deltaCore F := by
    refine mem_deltaCore_iff.mpr fun b hb hb1 => ?_
    by_cases hbx : b = x
    · subst hbx
      have : ⁅r, u⁆ = r * (u * r⁻¹ * u⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact (involutionOddCore b).mul_mem hr
        (conj_mem_oddCoreIn (hLx hu) ((involutionOddCore b).inv_mem hr))
    · have hbA : b ∈ A := hF.1 hb
      have hrb : r ∈ involutionOddCore x ⊓ Subgroup.centralizer ({b} : Set G) :=
        ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hSB x hx hx1 hr) b hbA).symm⟩
      have hLb : L ≤ Subgroup.centralizer ({b} : Set G) :=
        hLF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
      have hLY : L ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hLΩ, hLb⟩
      exact commutator_mem_involutionOddCore_of_localOddCentralizer3 hΩ hO (hnc b hbA hb1)
        (hAY b hbA hb1 hx) (orderOf_eq_prime (hA.2 x hx) hx1) hrb ⟨hLY hu, hLx hu⟩
  rw [hΔ F hF, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  exact hcomm

theorem localOddCentral3_of_covered (hΩ : ConjInvariant Ω) (hO : LocalOddCentralizer3 Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAY : ∀ b ∈ A, b ≠ 1 → A ≤ centralizingLayer Ω {b})
    (hnc : ∀ b ∈ A, b ≠ 1 → b ∉ Subgroup.center G) (hSB : StronglyBalanced A)
    (hΔ : ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥) {x : G} (hx : x ∈ A) (hx1 : x ≠ 1)
    (hcov : ∀ L ∈ Ω, L ≤ Subgroup.centralizer ({x} : Set G) →
      ∃ F ∈ signalizerFunctorEk 2 2 A, x ∈ F ∧ L ≤ Subgroup.centralizer (F : Set G)) :
    LocalOddCentral Ω {x} :=
  localOddCentral3_of_members_centralize hΩ fun L hLΩ hLx => by
    obtain ⟨F, hF, hxF, hLF⟩ := hcov L hLΩ hLx
    exact le_centralizer_involutionOddCore_of_covered hΩ hO hA hAY hnc hSB hΔ hx hx1 hLΩ hLx hF
      hxF hLF

end CFSG.ClassicalInvolution.Q3
