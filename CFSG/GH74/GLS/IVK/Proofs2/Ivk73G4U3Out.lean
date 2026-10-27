module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

namespace GHInv

theorem hOut_of_mulEquiv {A B : Type} [Group A] [Group B] (φ : Outer A ≃* Outer B)
    (h : ∀ E : Subgroup (Outer B), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1) :
    ∀ E : Subgroup (Outer A), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1 := by
  intro E hE
  have h1 := h (E.map φ.toMonoidHom) (by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, hE e he, map_one])
  rwa [Subgroup.card_map_of_injective φ.injective] at h1

end GHInv

theorem uni3_hOut {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hX : StatedClassicalModel X .PSU 3 p f) :
    ∀ E : Subgroup (Outer X), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 2 ^ 1 := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.GH74.KGroups.L3Eps.exists_primeFormP_equiv hX
  have hp : p.Prime := h.prime
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : p ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self p (by have := h.one_le; omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  apply GHInv.hOut_of_mulEquiv (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e)
  have hn : 3 ≤ 3 := le_rfl
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  set T := primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hT
  have : Finite K := h.finite
  obtain ⟨-, -, -, -, -, -, hFsurj, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  have hout := (unitary_full_diagonal_outer_order h hn hq).2.2.2.1
  set ρ := primeFormFieldFactor h hC hn hq with hρ
  have hle : inner T ≤ ρ.ker := by
    intro α hα
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    rw [MonoidHom.mem_ker]
    have := primeFormFieldFactor_apply h hC hn hq ⟨s, s.2.1⟩ 1
    rwa [map_one, mul_one] at this
  let ρ' : Outer T →* (K ≃+* K) := QuotientGroup.lift (inner T) ρ hle
  have hsurj : Function.Surjective ρ' := by
    intro g
    obtain ⟨a, ha⟩ := hFsurj g
    exact ⟨QuotientGroup.mk a, by simpa [ρ'] using ha⟩
  obtain ⟨hGal, hcyc⟩ := card_ringAut_and_isCyclic hp K h.card
  have hfin : Finite (MulAut T) :=
    Finite.of_injective (fun f : MulAut T => (f : T → T)) DFunLike.coe_injective
  have hker : Nat.card (ρ'.ker) = Nat.gcd 3 (p ^ f + 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ'.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ' hsurj).toEquiv, hGal,
      hout] at h1
    have hf0 : 0 < 2 * f := by have := h.one_le; omega
    exact (Nat.eq_of_mul_eq_mul_left hf0 h1).symm
  have hkodd : Odd (Nat.card ρ'.ker) := by
    rw [hker]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  intro E hE
  let ψ : ↥E →* (K ≃+* K) := ρ'.comp E.subtype
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro ε hε
    have hεker : (ε : Outer T) ∈ ρ'.ker := hε
    have hε2 : (ε : Outer T) * ε = 1 := hE ε ε.2
    have h2 : orderOf (ε : Outer T) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact hε2
    have h3 : orderOf (⟨(ε : Outer T), hεker⟩ : ρ'.ker) ∣ Nat.card ρ'.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h3
    have h4 : orderOf (ε : Outer T) ∣ Nat.gcd 2 (Nat.card ρ'.ker) := Nat.dvd_gcd h2 h3
    have h5 : Nat.gcd 2 (Nat.card ρ'.ker) = 1 :=
      (Nat.coprime_two_left.2 hkodd)
    rw [h5, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact Subtype.ext h4
  have hcard : Nat.card ↥E = Nat.card ↥ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
  rw [hcard]
  refine GHInv.card_le_two_of_isCyclic hcyc ψ.range ?_
  rintro _ ⟨ε, rfl⟩
  have hεε : ε * ε = 1 := Subtype.ext (hE ε ε.2)
  rw [← map_mul, hεε, map_one]

theorem ivk73_u3 {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    Ivk73Empty (fun X _ => LieModel X .PSU 3 p f) := by
  intro N _ _ L K Q h hL
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hL
  exact h.false_of_comp_mem (uni3_hOut hp2 hst) (comp_mem_uni hp hp2 h5 hst)

end CFSG.GH74.GLS.IVK
