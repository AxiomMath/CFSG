module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDRecognition
public import CFSG.ClassicalInvolution.RouteD.TypeF4Main

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem routeD_typeTwistedD [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 6 ≤ n)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaMinus (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (j : Fin (n - 2 - 1) → Subgroup G) (hjK : ∀ i, Commutes K (j i))
    (hjperf : ∀ i : Fin (n - 2 - 1), 1 ≤ i.val → ⁅j i, j i⁆ = j i)
    (hjt : ∀ i : Fin (n - 2 - 1), 1 ≤ i.val → j i ≤ Subgroup.centralizer ({t} : Set G))
    (hjcomm : ∀ i k : Fin (n - 2 - 1), i.val + 1 < k.val → ∀ u ∈ j i, ∀ v ∈ j k, u * v = v * u)
    (hjpair : ∀ i k : Fin (n - 2 - 1), i.val + 1 = k.val → k.val + 2 < n - 2 →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (j i) (j k))
    (hjtw : ∀ i k : Fin (n - 2 - 1), i.val + 3 = n - 2 → k.val + 2 = n - 2 →
      ∃ W, TwistedB2BlockPair (minusCoeffs_irr p f) W (j i) (j k))
    (hβj : ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j ⟨0, by omega⟩)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = n := by
  have hn3 : 3 ≤ n := by omega
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hβj' : ∀ i : Fin (n - 2 - 1), 1 ≤ i.val → Commutes β (j i) := fun i hi =>
    commutes_partner_of_perfect hp2 hq hMFZ hS3 hΩ hK hsingle hz hD4 hP1 hβ ht hKβ (hjperf i hi)
      (hjt i hi) (fun y hy x hx => hjK i x hx y hy)
  let U : Fin (n - 1) → Subgroup G := fun k =>
    if h0 : k.val = 0 then K else if h1 : k.val = 1 then β else j ⟨k.val - 2, by omega⟩
  have hU0 : U (twIdx0 hn3) = K := by simp [U, twIdx0]
  have hU1 : U (twIdx1 hn3) = β := by simp [U, twIdx1]
  have hUj : ∀ k : Fin (n - 1), (h : 2 ≤ k.val) → U k = j ⟨k.val - 2, by omega⟩ := by
    intro k h
    simp only [U]
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  have hUj' : ∀ i : Fin (n - 2 - 1), U ⟨i.val + 2, by omega⟩ = j i := by
    intro i
    rw [hUj _ (by simp only; omega)]
    congr 1
  refine routeD_typeTwistedD_of_chain hp2 hq hn hg6 hΩ hK hsingle hconn hz hshape hP1 U
    (by rw [hU0]; exact hK) ?_ ?_ ?_
  · intro a b hab u hu v hv
    rcases Nat.lt_or_ge a.val 2 with ha | ha
    · rcases Nat.lt_or_ge a.val 1 with ha0 | ha1
      · obtain rfl : a = twIdx0 hn3 := Fin.ext (by simp only [twIdx0]; omega)
        rw [hU0] at hu
        rw [hUj b (by omega)] at hv
        exact hjK _ u hu v hv
      · obtain rfl : a = twIdx1 hn3 := Fin.ext (by simp only [twIdx1]; omega)
        rw [hU1] at hu
        rw [hUj b (by omega)] at hv
        exact hβj' ⟨b.val - 2, by omega⟩ (by simp only; omega) u hu v hv
    · rw [hUj a ha] at hu
      rw [hUj b (by omega)] at hv
      exact hjcomm _ _ (by simp only; omega) u hu v hv
  · intro a b hab hb
    rcases Nat.lt_or_ge a.val 2 with ha | ha
    · rcases Nat.lt_or_ge a.val 1 with ha0 | ha1
      · obtain rfl : a = twIdx0 hn3 := Fin.ext (by simp only [twIdx0]; omega)
        obtain rfl : b = twIdx1 hn3 := Fin.ext (by simp only [twIdx0, twIdx1] at hab ⊢; omega)
        rw [hU0, hU1]
        exact hKβ
      · obtain rfl : a = twIdx1 hn3 := Fin.ext (by simp only [twIdx1]; omega)
        rw [hU1, hUj b (by simp only [twIdx1] at hab; omega)]
        have hb0 : (⟨b.val - 2, by omega⟩ : Fin (n - 2 - 1)) = ⟨0, by omega⟩ :=
          Fin.ext (by simp only [twIdx1] at hab ⊢; omega)
        rw [hb0]
        exact hβj
    · rw [hUj a ha, hUj b (by omega)]
      exact hjpair _ _ (by simp only; omega) (by simp only; omega)
  · intro a b ha hb
    rw [hUj a (by omega), hUj b (by omega)]
    exact hjtw _ _ (by simp only; omega) (by simp only; omega)

end CFSG.ClassicalInvolution.RouteD
