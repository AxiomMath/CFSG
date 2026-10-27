module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamOut
public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamL3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace U3Out

theorem outer_commutator_cube {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hX : StatedClassicalModel X .PSU 3 p f) :
    ∀ τ ∈ ⁅(⊤ : Subgroup (Outer X)), (⊤ : Subgroup (Outer X))⁆, τ ^ 3 = 1 := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.GH74.KGroups.L3Eps.exists_primeFormP_equiv hX
  have hp : p.Prime := h.prime
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : p ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self p (by have := h.one_le; omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hn : 3 ≤ 3 := le_rfl
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  set T := primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hT
  have : Finite K := h.finite
  suffices hTcube : ∀ τ ∈ ⁅(⊤ : Subgroup (Outer T)), (⊤ : Subgroup (Outer T))⁆, τ ^ 3 = 1 by
    intro τ hτ
    let E := CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
    have h1 : E τ ∈ ⁅(⊤ : Subgroup (Outer T)), (⊤ : Subgroup (Outer T))⁆ := by
      have h2 : (⁅(⊤ : Subgroup (Outer X)), (⊤ : Subgroup (Outer X))⁆).map E.toMonoidHom ≤
          ⁅(⊤ : Subgroup (Outer T)), (⊤ : Subgroup (Outer T))⁆ := by
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact h2 ⟨τ, hτ, rfl⟩
    have h3 := hTcube _ h1
    apply E.injective
    rw [map_pow, h3, map_one]
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
  have hcomm : ⁅(⊤ : Subgroup (Outer T)), (⊤ : Subgroup (Outer T))⁆ ≤ ρ'.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (ringAut_mul_comm K _ _)
  intro τ hτ
  have hτk : τ ∈ ρ'.ker := hcomm hτ
  have hfin' : Finite (Outer T) := Quotient.finite _
  have h1 : (⟨τ, hτk⟩ : ρ'.ker) ^ Nat.card ρ'.ker = 1 := pow_card_eq_one'
  have h2 : τ ^ Nat.card ρ'.ker = 1 := congrArg Subtype.val h1
  rw [hker] at h2
  have h3 : orderOf τ ∣ Nat.gcd 3 (p ^ f + 1) := orderOf_dvd_of_pow_eq_one h2
  exact orderOf_dvd_iff_pow_eq_one.1 (h3.trans (Nat.gcd_dvd_left 3 _))

end U3Out


theorem lem711_u3_ge5 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    Lem711Empty (fun X _ => LieModel X .PSU 3 p f) := by
  intro X _ _ L K x y h hL
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hL
  have hxL : x ∈ L := h.x_mem_L_of_outer_commutator_cube (U3Out.outer_commutator_cube hp2 hst)
  exact h.false_of_comp_mem_of_mem hxL (IVK.comp_mem_uni hp hp2 h5 hst)

theorem lem711_u33 : Lem711Empty (fun X _ => LieModel X .PSU 3 3 1) := by
  intro X _ _ L K x y h hL
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hL
  obtain ⟨h1, -⟩ := unitary_model_outer_two_part_bound ↥L 3 3 1 hst
  have hcard : Nat.card ↥L = 6048 := by
    have h2 : (Nat.card ↥L : ℤ) = 6048 := by
      have h3 : (Nat.gcd 3 (3 ^ 1 + 1) : ℤ) = 1 := by norm_num
      rw [h3, mul_one] at h1
      rw [h1]
      norm_num [Finset.prod_Icc_succ_top]
    exact_mod_cast h2
  exact h.false_of_card (by rw [hcard]; norm_num)

theorem lem711_u3 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Lem711Empty (fun X _ => LieModel X .PSU 3 p f) := by
  rcases L3Aut.odd_prime_pow_eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
  · exact lem711_u33
  · exact lem711_u3_ge5 hp hp2 h5

end CFSG.GH74.GLS
