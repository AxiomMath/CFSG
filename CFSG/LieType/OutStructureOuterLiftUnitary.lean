module

public import CFSG.LieType.OutStructureOuterLiftLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem outerPElementLifts_primeFormP_of_not_dvd {p₀ f N : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p₀ f K) (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ p₀ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hdiv : ¬ p ∣ Nat.gcd N (p₀ ^ f + 1)) :
    OuterPElementLifts (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hC1 := isPrimeFormGram_one (K := K) (n := N)
  obtain ⟨-, -, -, -, -, hff, -, -, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC1 hN hq
  obtain ⟨-, -, -, hOut, -, -⟩ := unitary_full_diagonal_outer_order h hN hq
  have hfcard : Nat.card (K ≃+* K) = 2 * f := (card_ringAut_and_isCyclic h.prime K h.card).1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hfcard]; have := h.one_le; omega)
  have hψ : Function.Injective
      ((QuotientGroup.mk' (inner (primeFormP h ((1 : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K)))).comp (primeFormFieldHom h hC1)) := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hI := (QuotientGroup.eq_one_iff _).mp hσ
    obtain ⟨s, hs⟩ := (hinn _).mp hI
    have h1 := hff 1 σ
    rw [map_one, one_mul] at h1
    have h2 := hff ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one] at h2
    rw [← h1, MonoidHom.coe_comp, Function.comp_apply] at *
    rw [hs, h2]
  let S : Sylow p (K ≃+* K) := default
  have hidx : ¬ p ∣ ((S : Subgroup (K ≃+* K)).map
      ((QuotientGroup.mk' (inner (primeFormP h ((1 : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K)))).comp (primeFormFieldHom h hC1))).index := by
    intro hpd
    have hf0 : 2 * f ≠ 0 := by have := h.one_le; omega
    have hcard : Nat.card (Outer (primeFormP h ((1 : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K))) =
        ((S : Subgroup (K ≃+* K)).map
          ((QuotientGroup.mk' (inner (primeFormP h ((1 : GL (Fin N) K) :
            Matrix (Fin N) (Fin N) K)))).comp (primeFormFieldHom h hC1))).index *
          p ^ (2 * f).factorization p := by
      rw [← Subgroup.index_mul_card, Subgroup.card_map_of_injective hψ,
        Sylow.card_eq_multiplicity S, hfcard]
    have h1 : p ^ ((2 * f).factorization p + 1) ∣ (2 * f) * Nat.gcd N (p₀ ^ f + 1) := by
      rw [← hOut, hcard, pow_succ, mul_comm (p ^ _) p]
      exact Nat.mul_dvd_mul_right hpd _
    have hcop : Nat.Coprime (p ^ ((2 * f).factorization p + 1)) (Nat.gcd N (p₀ ^ f + 1)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdiv)
    exact Nat.pow_succ_factorization_not_dvd hf0 hp (hcop.dvd_of_dvd_mul_right h1)
  intro y hy
  exact exists_lift_orderOf_eq_of_sylow_map
    (QuotientGroup.mk' (inner (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))))
    (QuotientGroup.mk'_surjective _) (primeFormFieldHom h hC1) hψ (S : Subgroup (K ≃+* K))
    S.isPGroup' hidx hy

theorem exists_orderOf_eq_not_mem_of_primeFormP {X : Type} [Group X] [Finite X]
    {L : Subgroup X} [L.Normal] (hL : CFSG.IsComponent L) {p₀ f N : ℕ} {K : Type} [Field K]
    [Finite K] (h : UnitaryFieldData p₀ f K)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃*
      primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))
    (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ p₀ ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (hdiv : ¬ p ∣ Nat.gcd N (p₀ ^ f + 1))
    (hnot : ¬ CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPClosedMod p
        (L ⊔ Subgroup.centralizer (L : Set X)))
    (hc : ¬ ∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p) :
    ∃ x : X, orderOf x = p ∧ x ∉ L ⊔ Subgroup.centralizer (L : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hC : ¬ p ∣ Nat.card (Subgroup.centralizer (L : Set X)) := by
    intro hd
    obtain ⟨c, hcp⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.centralizer (L : Set X)) p hd
    exact hc ⟨c, c.2, by rw [Subgroup.orderOf_coe, hcp]⟩
  exact exists_orderOf_eq_not_mem_of_outerPElementLifts hL inferInstance hp
    (OuterPElementLifts.of_mulEquiv e
      (outerPElementLifts_primeFormP_of_not_dvd h hN hq hp hdiv)) hC hnot

end CFSG.LieType.OutStructure
