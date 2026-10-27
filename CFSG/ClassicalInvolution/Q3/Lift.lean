module

public import CFSG.LieType.CentralExt.SL2Lift
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

section Pow

variable {Y : Type} [Group Y]

theorem commutator_pow_of_central {x y : Y} (hc : ∀ k : ℕ, ⁅x ^ k, y⁆ ∈ Subgroup.center Y)
    (n : ℕ) : ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ⁅x ^ n * x, y⁆ = x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ * ⁅x ^ n, y⁆ := by
      simp only [commutatorElement_def]
      group
    have hx : ⁅x, y⁆ ∈ Subgroup.center Y := by simpa using hc 1
    have h2 : x ^ n * ⁅x, y⁆ * (x ^ n)⁻¹ = ⁅x, y⁆ := by
      rw [Subgroup.mem_center_iff.mp hx (x ^ n)]
      group
    rw [pow_succ, h1, h2, ih, pow_succ']

end Pow

section Commute

variable {Y : Type} [Group Y] [Finite Y]

theorem commutes_of_commutes_oddQuotient3
    (hZ : classicalInvolutionOddCore Y ≤ Subgroup.center Y)
    (h3 : ¬ 3 ∣ Nat.card (classicalInvolutionOddCore Y)) {K : Subgroup Y}
    (hK : ∀ x ∈ K, x ^ 12 = 1) {y : Y}
    (hc : ∀ x ∈ K, ⁅x, y⁆ ∈ classicalInvolutionOddCore Y) {x : Y} (hx : x ∈ K) :
    ⁅x, y⁆ = 1 := by
  have hcen : ∀ k : ℕ, ⁅x ^ k, y⁆ ∈ Subgroup.center Y := fun k =>
    hZ (hc _ (K.pow_mem hx k))
  have hpow : ⁅x, y⁆ ^ 12 = 1 := by
    rw [← commutator_pow_of_central hcen, hK x hx]
    simp
  have hmem := hc x hx
  have hodd : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  have hord : orderOf ⁅x, y⁆ ∣ Nat.card (classicalInvolutionOddCore Y) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  have hd12 : orderOf ⁅x, y⁆ ∣ 12 := orderOf_dvd_of_pow_eq_one hpow
  have hoddo : Odd (orderOf ⁅x, y⁆) := hodd.of_dvd_nat hord
  have h3o : ¬ 3 ∣ orderOf ⁅x, y⁆ := fun h => h3 (h.trans hord)
  have hmemdiv : orderOf ⁅x, y⁆ ∈ Nat.divisors 12 := by
    simp [Nat.mem_divisors, hd12]
  have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [hdiv] at hmemdiv
  have h1 : orderOf ⁅x, y⁆ = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemdiv
    rcases hmemdiv with h | h | h | h | h | h
    · exact h
    · rw [h] at hoddo; exact absurd hoddo (by decide)
    · rw [h] at h3o; exact absurd (dvd_refl 3) h3o
    · rw [h] at hoddo; exact absurd hoddo (by decide)
    · rw [h] at hoddo; exact absurd hoddo (by decide)
    · rw [h] at hoddo; exact absurd hoddo (by decide)
  exact orderOf_eq_one_iff.mp h1

private theorem sl2Three_pow_twelve : ∀ x : SL(2, ZMod 3), x ^ 12 = 1 := by decide +kernel

theorem pow_twelve_of_equiv_sl2Three {K : Type} [Group K] (e : K ≃* SL(2, ZMod 3)) (x : K) :
    x ^ 12 = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  exact sl2Three_pow_twelve _

theorem commutes_of_equiv_sl2Three
    (hZ : classicalInvolutionOddCore Y ≤ Subgroup.center Y)
    (h3 : ¬ 3 ∣ Nat.card (classicalInvolutionOddCore Y)) {K L : Subgroup Y}
    (hK : Nonempty (↥K ≃* SL(2, ZMod 3)))
    (hc : ∀ x ∈ K, ∀ y ∈ L, ⁅x, y⁆ ∈ classicalInvolutionOddCore Y) : ⁅K, L⁆ = ⊥ := by
  obtain ⟨e⟩ := hK
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot]
  refine commutes_of_commutes_oddQuotient3 hZ h3 (K := K) (y := y) (fun z hz => ?_)
    (fun z hz => hc z hz y hy) hx
  have := pow_twelve_of_equiv_sl2Three e ⟨z, hz⟩
  exact congrArg Subtype.val this

end Commute

section Lift

theorem exists_hom_lift_sl2Three {X Y : Type} [Group X] [Group Y] [Finite Y] (π : Y →* X)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center Y) (h2 : IsPGroup 2 π.ker)
    (J : Subgroup X) (e : SL(2, ZMod 3) ≃* J) :
    ∃ β : SL(2, ZMod 3) →* Y, Function.Injective β ∧ ∀ s, π (β s) = (e s : X) := by
  have hk : ringChar (ZMod 3) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  let α : SL(2, ZMod 3) →* X := J.subtype.comp e.toMonoidHom
  obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hπ hcen h2 α
  have hαinj : Function.Injective α := Subtype.val_injective.comp e.injective
  have hcomp : ∀ s, π (β s) = α s := fun s => DFunLike.congr_fun hβ s
  refine ⟨β, fun a b hab => hαinj ?_, fun s => hcomp s⟩
  rw [← hcomp, ← hcomp, hab]

theorem exists_subgroup_lift_sl2Three {X Y : Type} [Group X] [Group Y] [Finite Y] (π : Y →* X)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center Y) (h2 : IsPGroup 2 π.ker)
    (J : Subgroup X) (e : SL(2, ZMod 3) ≃* J) :
    ∃ J' : Subgroup Y, J'.map π = J ∧ Nonempty (SL(2, ZMod 3) ≃* J') := by
  obtain ⟨β, hβinj, hβ⟩ := exists_hom_lift_sl2Three π hπ hcen h2 J e
  refine ⟨β.range, ?_, ⟨MonoidHom.ofInjective hβinj⟩⟩
  ext x
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    rw [hβ]
    exact (e s).2
  · intro hx
    obtain ⟨s, hs⟩ := e.surjective ⟨x, hx⟩
    exact ⟨β s, ⟨s, rfl⟩, by rw [hβ, hs]⟩

end Lift

end CFSG.ClassicalInvolution.Q3
