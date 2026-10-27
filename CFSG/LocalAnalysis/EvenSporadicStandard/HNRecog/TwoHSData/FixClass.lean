module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import CFSG.Sporadic.HeldB.FixCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.HeldB (fixCard fixCard_conj sum_fixCard_eq)

theorem card_centralizer_mul_le {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) (p₀ : Fin n)
    (htrans : ∀ p : Fin n, ∃ g ∈ P, g p = p₀) {x : Equiv.Perm (Fin n)} (hx : x ∈ P)
    (M : Finset (Equiv.Perm (Fin n)))
    (hM : ∀ y ∈ M, y ∈ conjClass P x ∧ y p₀ = p₀) :
    Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n)))) * (n * M.card) ≤
      Nat.card ↥P * (Finset.univ.filter fun p : Fin n => x p = p).card := by
  classical
  set X : Finset (Equiv.Perm (Fin n)) := (Set.toFinite (conjClass P x)).toFinset with hX
  set CC : ℕ := Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n)))) with hCC
  have hmemX : ∀ y, y ∈ X ↔ y ∈ conjClass P x := by
    intro y
    rw [hX, Set.Finite.mem_toFinset]
  have htrans' : ∀ q : Fin n, ∃ h ∈ P, h p₀ = q := by
    intro q
    obtain ⟨g, hgP, hgq⟩ := htrans q
    exact ⟨g⁻¹, P.inv_mem hgP, by rw [Equiv.Perm.inv_eq_iff_eq]; exact hgq.symm⟩
  have hXconj : ∀ y ∈ X, ∀ h ∈ P, h * y * h⁻¹ ∈ X := by
    intro y hy h hhP
    rw [hmemX] at hy ⊢
    obtain ⟨g, hgP, rfl⟩ := mem_conjClass.mp hy
    exact ⟨h * g, P.mul_mem hhP hgP, by group⟩
  have hfixconst : ∀ y ∈ X, fixCard y = fixCard x := by
    intro y hy
    obtain ⟨g, _hgP, rfl⟩ := mem_conjClass.mp ((hmemX y).mp hy)
    exact fixCard_conj g x
  have hsum : ∑ y ∈ X, fixCard y = X.card * fixCard x := by
    rw [Finset.sum_congr rfl hfixconst, Finset.sum_const_nat (fun _ _ => rfl)]
  have hdouble := sum_fixCard_eq (G := P) p₀ htrans' X hXconj
  have hMsub : M ⊆ X.filter (fun y => y p₀ = p₀) := by
    intro y hy
    obtain ⟨hyX, hyp0⟩ := hM y hy
    exact Finset.mem_filter.mpr ⟨(hmemX y).mpr hyX, hyp0⟩
  have hMle : M.card ≤ (X.filter fun y => y p₀ = p₀).card := Finset.card_le_card hMsub
  have hkey : n * M.card ≤ X.card * fixCard x := by
    calc n * M.card ≤ n * (X.filter fun y => y p₀ = p₀).card := Nat.mul_le_mul_left n hMle
      _ = X.card * fixCard x := hdouble.symm.trans hsum
  have hXC : X.card * CC = Nat.card ↥P := by
    have h2 : X.card = (conjClass P x).ncard := by
      rw [hX]
      exact (Set.ncard_eq_toFinset_card (conjClass P x) (Set.toFinite (conjClass P x))).symm
    rw [h2, hCC]
    exact ncard_conjClass_mul_card P x
  change CC * (n * M.card) ≤ Nat.card ↥P * fixCard x
  calc CC * (n * M.card) ≤ CC * (X.card * fixCard x) := Nat.mul_le_mul_left CC hkey
    _ = Nat.card ↥P * fixCard x := by rw [← mul_assoc, mul_comm CC X.card, hXC]

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
