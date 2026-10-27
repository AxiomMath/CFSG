module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Ree.G2ExceptionalCosetInvolutions
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartTwo.Census.Carrier.G2Three (H3 R3 tH X0H orbitElt card_R3 card_X0H
  card_S2H X0H_le_centralizer orbitElt_injective orbitElt_conj exists_conj_of_mem_S2H
  card_centralizer_mul_le exists_conj_of_sylow adjointEquivR3)

theorem card_centralizer_map_equiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (s : X) :
    Nat.card (centralizer {e s}) = Nat.card (centralizer {s}) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)).symm
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    show e x * e s = e s * e x
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply e.injective
    rwa [map_mul, map_mul]

theorem mulAut_mul_conj_mul_inv {X : Type*} [Group X] (θ : MulAut X) (c : X) :
    θ * MulAut.conj c * θ⁻¹ = MulAut.conj (θ c) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]


section Centralizer


theorem card_centralizer_tH : Nat.card (centralizer {tH}) = 576 := by
  have hH : Nat.card H3 = 4245696 := card_R3
  have h : Nat.card (centralizer {tH}) * 7371 ≤ 4245696 :=
    hH ▸ card_centralizer_mul_le orbitElt orbitElt_injective orbitElt_conj
  have h2 : Nat.card X0H ≤ Nat.card (centralizer {tH}) := Subgroup.card_le_of_le X0H_le_centralizer
  rw [card_X0H] at h2
  omega

theorem card_centralizer_H3 {s : H3} (hs : orderOf s = 2) :
    Nat.card (centralizer {s}) = 576 := by
  obtain ⟨g, rfl⟩ := exists_conj_of_sylow card_R3 card_S2H exists_conj_of_mem_S2H hs
  have h := card_centralizer_map_equiv (MulAut.conj g) tH
  rw [MulAut.conj_apply] at h
  rw [h, card_centralizer_tH]

theorem card_centralizer_of_orderOf_eq_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {s : adjointGroup Tag.G2 K} (hs : orderOf s = 2) :
    Nat.card (centralizer {s}) = 576 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨φ⟩ : Nonempty (K ≃+* ZMod 3) := ⟨FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, hK, ZMod.card])⟩
  obtain ⟨e⟩ : Nonempty (adjointGroup Tag.G2 K ≃* H3) :=
    ⟨(CFSG.TauCetiBridge.adjointGroupCongr (τ := Tag.G2) φ).trans adjointEquivR3⟩
  have h1 := @card_centralizer_map_equiv _ H3 _ R3.toGroup e s
  have h2 : orderOf (e s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
  rw [← h1]
  exact card_centralizer_H3 h2

end Centralizer

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3)
include hK

theorem aut_cases (α : MulAut (adjointGroup ReeTag.G2.tag K)) :
    (∃ g, α = MulAut.conj g) ∨ ∃ g, α = MulAut.conj g * ReeTag.G2.finiteExceptionalAut K := by
  obtain ⟨-, hnf, -⟩ := CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form le_rfl K
    (by rw [hK, pow_one])
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf α
  rcases (show (k : ℕ) = 0 ∨ (k : ℕ) = 1 by omega) with hk | hk
  · left
    refine ⟨g, ?_⟩
    rw [hgk]
    simp only [hk, pow_zero, mul_one]
  · right
    refine ⟨g, ?_⟩
    rw [hgk]
    simp only [hk, pow_one]

theorem phi_sq : ReeTag.G2.finiteExceptionalAut K ^ 2 = 1 := by
  obtain ⟨hord, -⟩ := CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form le_rfl K
    (by rw [hK, pow_one])
  rw [show (2 : ℕ) = 2 * 1 from rfl, ← hord]
  exact pow_orderOf_eq_one _

theorem phi_not_mem_range : ReeTag.G2.finiteExceptionalAut K ∉
    (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range := by
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker⟩, -⟩ :=
    CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form le_rfl K (by rw [hK, pow_one])
  intro hmem
  rw [← hker, MonoidHom.mem_ker] at hmem
  have h := hΘ (ReeTag.G2.finiteExceptionalAut K) 1 1 (by rw [map_one, one_mul, pow_one])
  rw [hmem] at h
  have h' := congrArg Multiplicative.toAdd h
  simp only [toAdd_one, toAdd_ofAdd, Nat.cast_one] at h'
  exact absurd h'.symm (by decide)

theorem exists_conj_eq_conj_mul_phi (g : adjointGroup ReeTag.G2.tag K)
    (hα : (MulAut.conj g * ReeTag.G2.finiteExceptionalAut K) ^ 2 = 1) :
    ∃ b : adjointGroup ReeTag.G2.tag K, MulAut.conj b * ReeTag.G2.finiteExceptionalAut K *
      (MulAut.conj b)⁻¹ = MulAut.conj g * ReeTag.G2.finiteExceptionalAut K := by
  set φ := ReeTag.G2.finiteExceptionalAut K with hφ
  obtain ⟨-, -, -, -, -, -, hodd⟩ :=
    CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form le_rfl K (by rw [hK, pow_one])
  obtain ⟨-, hF, -⟩ := hodd 0 rfl
  rw [pow_one] at hF
  rw [← hφ] at hF
  have hα' : (MulAut.conj g * ReeTag.G2.finiteReeAut K 0) ^ 2 = 1 := by rw [← hF]; exact hα
  obtain ⟨ψ, hψ⟩ := G2_exceptional_coset_involution_conj 0 K (by rw [hK]; norm_num) g hα'
  rw [← hF] at hψ
  have hφ2 : φ * φ = 1 := by rw [← sq]; exact phi_sq hK
  have hφinv : φ⁻¹ = φ := inv_eq_of_mul_eq_one_right hφ2
  have hconj : ∀ (θ : MulAut (adjointGroup ReeTag.G2.tag K)) (c : adjointGroup ReeTag.G2.tag K),
      θ * MulAut.conj c * θ⁻¹ = MulAut.conj (θ c) :=
    mulAut_mul_conj_mul_inv
  rcases aut_cases hK ψ with ⟨b', rfl⟩ | ⟨b', rfl⟩
  ·
    refine ⟨b'⁻¹, ?_⟩
    rw [map_inv]
    calc (MulAut.conj b')⁻¹ * φ * (MulAut.conj b')⁻¹⁻¹ =
        (MulAut.conj b')⁻¹ * (MulAut.conj b' * (MulAut.conj g * φ) * (MulAut.conj b')⁻¹) *
          MulAut.conj b' := by rw [hψ, inv_inv]
      _ = MulAut.conj g * φ := by group
  ·
    refine ⟨φ⁻¹ b'⁻¹, ?_⟩
    have h1 : MulAut.conj g * φ = φ⁻¹ * ((MulAut.conj b')⁻¹ * φ * MulAut.conj b') * φ := by
      have := hψ
      calc MulAut.conj g * φ = (MulAut.conj b' * φ)⁻¹ *
            ((MulAut.conj b' * φ) * (MulAut.conj g * φ) * (MulAut.conj b' * φ)⁻¹) *
              (MulAut.conj b' * φ) := by group
        _ = (MulAut.conj b' * φ)⁻¹ * φ * (MulAut.conj b' * φ) := by rw [this]
        _ = φ⁻¹ * ((MulAut.conj b')⁻¹ * φ * MulAut.conj b') * φ := by group
    have h2 : φ⁻¹ * (MulAut.conj b')⁻¹ * φ = MulAut.conj (φ⁻¹ b'⁻¹) := by
      rw [← hconj φ⁻¹ b'⁻¹, map_inv, inv_inv]
    rw [h1, ← h2]
    group

end Aut

end CFSG.LocalAnalysis.EvenBN.LinearThree.G2Three
