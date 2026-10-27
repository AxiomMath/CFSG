module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupTorus

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.LinearModel
  CFSG.BenderSuzuki.MatrixGroups

theorem map_centralizer_singleton {K G : Type*} [Group K] [Group G] (e : K ≃* G) (x : K) :
    (centralizer ({x} : Set K)).map e.toMonoidHom = centralizer ({e x} : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have := congrArg e h
    simpa using this
  · intro h
    apply e.injective
    simpa using h

theorem BenderType.linear_odd_element {K : Type*} [Group K] {n : ℕ} (h : BenderType K n 1 1)
    {x : K} (hx : x ≠ 1) (hxodd : Odd (orderOf x)) :
    IsCyclic ↥(centralizer ({x} : Set K)) ∧
      (Nat.card ↥(centralizer ({x} : Set K)) = 2 ^ n - 1 ∨
        Nat.card ↥(centralizer ({x} : Set K)) = 2 ^ n + 1) ∧
      (∀ a : K, a * x * a⁻¹ = x⁻¹ → ∀ y ∈ centralizer ({x} : Set K), a * y * a⁻¹ = y⁻¹) ∧
      ∃ w : K, w * w = 1 ∧ (∀ y ∈ centralizer ({x} : Set K), w * y * w⁻¹ = y⁻¹) ∧
        ∀ R : Subgroup K, R ≤ centralizer ({x} : Set K) → R ≠ ⊥ →
          normalizer (R : Set K) = centralizer ({x} : Set K) ⊔ zpowers w := by
  cases h with
  | linear n hn e =>
    have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have hx' : e x ≠ 1 := fun h1 => hx (e.injective (by rw [h1, map_one]))
    have hxodd' : Odd (orderOf (e x)) := by rwa [MulEquiv.orderOf_eq]
    obtain ⟨hcyc, hcardC, hinv⟩ :=
      psl2_even_odd_element_full_centralizer n hn hcard (e x) hx' hxodd'
    obtain ⟨w', hw'sq, hw'inv, hw'N⟩ :=
      psl2_even_odd_element_torus_normalizer n hn hcard (e x) hx' hxodd'
    have hmap := map_centralizer_singleton e x
    refine ⟨?_, ?_, ?_, e.symm w', ?_, ?_, ?_⟩
    · have : IsCyclic ↥((centralizer ({x} : Set K)).map e.toMonoidHom) := by rw [hmap]; exact hcyc
      exact (MulEquiv.isCyclic (MulEquiv.subgroupMap e (centralizer ({x} : Set K)))).mpr this
    · have hc : Nat.card ↥(centralizer ({x} : Set K)) =
          Nat.card ↥(centralizer ({e x} : Set (PSL2MatrixGroup (GaloisField 2 n)))) := by
        rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
      rw [hc, hcard] at *
      exact hcardC
    · intro a ha y hy
      have h1 : e a * e x * (e a)⁻¹ = (e x)⁻¹ := by
        have := congrArg e ha
        simpa using this
      have hy' : e y ∈ centralizer ({e x} : Set (PSL2MatrixGroup (GaloisField 2 n))) := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hy
      have := hinv (e a) h1 (e y) hy'
      apply e.injective
      simpa using this
    · rw [← map_mul, hw'sq, map_one]
    · intro y hy
      have hy' : e y ∈ centralizer ({e x} : Set (PSL2MatrixGroup (GaloisField 2 n))) := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hy
      have := hw'inv (e y) hy'
      apply e.injective
      simpa using this
    · intro R hR hR1
      have hRmap : R.map e.toMonoidHom ≤
          centralizer ({e x} : Set (PSL2MatrixGroup (GaloisField 2 n))) := by
        rw [← hmap]
        exact Subgroup.map_mono hR
      have hRne : R.map e.toMonoidHom ≠ ⊥ := by
        intro hbot
        apply hR1
        exact (Subgroup.map_eq_bot_iff_of_injective R e.injective).mp hbot
      have hN := hw'N (R.map e.toMonoidHom) hRmap hRne
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [Subgroup.map_equiv_normalizer_eq R e, hN, Subgroup.map_sup, hmap]
      congr 1
      rw [MonoidHom.map_zpowers]
      simp

end CFSG.GH74.Uniqueness.Bender
