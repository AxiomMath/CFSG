module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Star
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4L6Conj

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
open scoped commutatorElement

section G2

variable {G : Type} [Group G]

theorem invol_not_mem_center {I : Subgroup G} (hZ : Odd (Nat.card (center ↥I))) {w : G}
    (hwI : w ∈ I) (hw2 : w * w = 1) (hw1 : w ≠ 1) : (⟨w, hwI⟩ : ↥I) ∉ center ↥I := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw1' : (⟨w, hwI⟩ : ↥I) ≠ 1 := fun h' => hw1 (congrArg Subtype.val h')
  have h2 : orderOf (⟨w, hwI⟩ : ↥I) = 2 :=
    orderOf_eq_prime (by
      have : ((⟨w, hwI⟩ : ↥I) ^ 2 : ↥I) = 1 := by
        rw [pow_two]
        exact Subtype.ext hw2
      exact this) hw1'
  have h3 : orderOf (⟨(⟨w, hwI⟩ : ↥I), hc⟩ : ↥(center ↥I)) ∣ Nat.card ↥(center ↥I) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, h2] at h3
  exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h3)

theorem comm_eq_of_invol [Finite G] {I : Subgroup G} (hq : IsQuasisimple ↥I)
    (hZ : Odd (Nat.card (center ↥I))) {w : G} (hwI : w ∈ I) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    ⁅I, zpowers w⁆ = I := by
  refine commutator_eq_of_not_le_centralizer hq
    (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hwI)) ?_
  intro h
  apply invol_not_mem_center hZ hwI hw2 hw1
  rw [Subgroup.mem_center_iff]
  intro j
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_zpowers w)) (j : G) j.2)

theorem g2_J [Finite G] (hstar : KStarL34) {I : Subgroup G} (hq : IsQuasisimple ↥I)
    (hLie : IsL34Quotient ↥I) (hZ : Odd (Nat.card (center ↥I))) {w : G} (hwI : w ∈ I)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G}
    (hQN : Q ≤ normalizer (I : Set G)) (hQp : IsPGroup p ↥Q) (hQw : ∀ x ∈ Q, w * x = x * w)
    (hQnorm : ∀ y ∈ I, y * w = w * y → y ∈ normalizer (Q : Set G)) :
    Q ≤ centralizer (I : Set G) := by
  by_contra hnc
  have hwN : w ∈ normalizer (I : Set G) := Subgroup.le_normalizer hwI
  have hIw : ⁅I, zpowers w⁆ = I := comm_eq_of_invol hq hZ hwI hw2 hw1
  obtain ⟨-, -, -, hninn⟩ := star_J hstar hq hLie hZ hwN hw2 hIw hp hp2 hQN hQp hnc hQw hQnorm
  exact hninn (alphaZ_mem_innSub hwI)

end G2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L6
