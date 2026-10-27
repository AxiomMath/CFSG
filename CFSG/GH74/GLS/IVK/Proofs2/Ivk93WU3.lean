module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WQuat
import CFSG.RankThree.SubgroupLists.TwoRankPSUThree
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem ivk93w_psu3_twoRank_le_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    CFSG.Assembly.twoRank (StatedProj (StatedSU 3 (p ^ f) K)) ≤ 2 :=
  CFSG.RankThree.SubgroupLists.twoRank_statedProj_statedSU_three_le_two hp hp2 hK

theorem ivk93w_uni3_outer_commutator_odd {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hX : StatedClassicalModel X .PSU 3 p f) : Odd (Nat.card (commutator (Outer X))) := by
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
  let ι : Outer X ≃* Outer T := equivalence e
  have hcomm : commutator (Outer X) ≤ (ρ'.comp ι.toMonoidHom).ker := by
    change ⁅(⊤ : Subgroup (Outer X)), (⊤ : Subgroup (Outer X))⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (IsCyclic.isMulCommutative (α := RingAut K)).is_comm.comm _ _
  have hker2 : Nat.card (ρ'.comp ι.toMonoidHom).ker = Nat.card ρ'.ker := by
    rw [← MonoidHom.comap_ker]
    have h1 := Subgroup.comap_equiv_eq_map_symm ι ρ'.ker
    have h2 : Nat.card ↥(Subgroup.comap (ι : Outer X →* Outer T) ρ'.ker) = Nat.card ↥ρ'.ker := by
      rw [h1]
      exact Subgroup.card_map_of_injective (f := (ι.symm : Outer T →* Outer X)) ι.symm.injective
    exact h2
  exact Odd.of_dvd_nat (hker2 ▸ hkodd) (Subgroup.card_dvd_of_le hcomm)

theorem ivk93w_u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93WEmptyQ (fun X _ => LieModel X .PSU 3 p f) := by
  intro p f hp hp2 hf J _ _ hJ x q B h hB hQ
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  have hquat := hQ (ivk93w_uni3_outer_commutator_odd hp2 hst)
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hst
  have : Finite (StatedProj (StatedSU 3 (p ^ f) K)) := Finite.of_equiv _ φ.toEquiv
  have h3 := (Ivk93W.of_equiv φ h).three_le_twoRank (Ivk93WQuat.of_equiv φ hquat)
  have h2 := ivk93w_psu3_twoRank_le_two hp hp2 hK
  omega

end CFSG.GH74.GLS.IVK.Proofs2
