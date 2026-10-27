module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Classify

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)

theorem comm_of_card_le_four {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 4) (a b : G) :
    a * b = b * a := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hc : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 := by omega
  rcases hc with hc | hc | hc | hc
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 hc).1
    exact Subsingleton.elim _ _
  · haveI : Fact (Nat.Prime (Nat.card G)) := ⟨by rw [hc]; exact Nat.prime_two⟩
    haveI := isCyclic_of_prime_card (p := Nat.card G) rfl
    exact IsMulCommutative.is_comm.comm a b
  · haveI : Fact (Nat.Prime (Nat.card G)) := ⟨by rw [hc]; exact Nat.prime_three⟩
    haveI := isCyclic_of_prime_card (p := Nat.card G) rfl
    exact IsMulCommutative.is_comm.comm a b
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (by rw [hc]; norm_num) a b

section Small

variable {S : Type} [Group S] [Finite S] {σ : MulAut S}

theorem quotient_card_le_four (D : Subgroup ↥(fixedSubgroup σ))
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) (hC : Nat.card (fixedSubgroup σ) ≤ 1440) :
    Nat.card (↥(fixedSubgroup σ) ⧸ D) ≤ 4 := by
  obtain ⟨e⟩ := hD
  have h1 : Nat.card ↥D = 360 := by rw [Nat.card_congr e.toEquiv, a6sq_card]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup D
  rw [h1] at h2
  omega

theorem commutator_le_of_small (D : Subgroup ↥(fixedSubgroup σ)) (hDn : D.Normal)
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) (hC : Nat.card (fixedSubgroup σ) ≤ 1440) :
    commutator ↥(fixedSubgroup σ) ≤ D := by
  haveI := hDn
  have hcomm := comm_of_card_le_four (quotient_card_le_four D hD hC)
  have h1 : commutator ↥(fixedSubgroup σ) = ⁅(⊤ : Subgroup ↥(fixedSubgroup σ)), ⊤⁆ := rfl
  rw [h1, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ D
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hcomm (QuotientGroup.mk g₁) (QuotientGroup.mk g₂)]
  group

theorem a6Hyp_of_small (D : Subgroup ↥(fixedSubgroup σ)) (hDn : D.Normal)
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) (hC : Nat.card (fixedSubgroup σ) ≤ 1440) :
    A6Hyp σ D := by
  refine ⟨hDn, hD, ?_⟩
  intro P hP
  have h1 := commutator_le_of_small D hDn hD hC
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅(⊤ : Subgroup ↥(fixedSubgroup σ)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
    _ ≤ D := h1

theorem a6_commutator_eq_top : commutator (alternatingGroup (Fin 6)) = ⊤ := by
  haveI := a6sq_simple
  haveI : (commutator (alternatingGroup (Fin 6))).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6))) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := a6sq_nonab
    apply hab
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ commutator (alternatingGroup (Fin 6)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    calc a * b = a * b * a⁻¹ * b⁻¹ * b * a := by group
      _ = b * a := by rw [hmem]; group
  · exact h

theorem commutator_eq_of_small (D : Subgroup ↥(fixedSubgroup σ)) (hDn : D.Normal)
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) (hC : Nat.card (fixedSubgroup σ) ≤ 1440) :
    commutator ↥(fixedSubgroup σ) = D := by
  refine le_antisymm (commutator_le_of_small D hDn hD hC) ?_
  obtain ⟨e⟩ := hD
  have hperf : commutator ↥D = ⊤ := by
    have h1 : (commutator ↥D).map e.toMonoidHom = commutator (alternatingGroup (Fin 6)) := by
      have h2 : commutator ↥D = ⁅(⊤ : Subgroup ↥D), ⊤⁆ := rfl
      have h3 : commutator (alternatingGroup (Fin 6)) =
          ⁅(⊤ : Subgroup (alternatingGroup (Fin 6))), ⊤⁆ := rfl
      rw [h2, h3, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    rw [a6_commutator_eq_top] at h1
    exact Subgroup.map_injective e.injective (by rw [h1, Subgroup.map_top_of_surjective _ e.surjective])
  intro x hx
  exact a6sq_range_le_derived D.subtype hperf ⟨⟨x, hx⟩, rfl⟩

theorem a6small_derived_iso (D : Subgroup ↥(fixedSubgroup σ)) (hDn : D.Normal)
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) (hC : Nat.card (fixedSubgroup σ) ≤ 1440) :
    Nonempty (↥(commutator ↥(autCentralizer σ)) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := hD
  let φ : ↥(autCentralizer σ) ≃* ↥(fixedSubgroup σ) :=
    MulEquiv.subgroupCongr (autCentralizer_eq_fixedSubgroup σ)
  have h : (commutator ↥(autCentralizer σ)).map φ.toMonoidHom = commutator ↥(fixedSubgroup σ) := by
    have h1 : commutator ↥(autCentralizer σ) = ⁅(⊤ : Subgroup ↥(autCentralizer σ)), ⊤⁆ := rfl
    have h2 : commutator ↥(fixedSubgroup σ) = ⁅(⊤ : Subgroup ↥(fixedSubgroup σ)), ⊤⁆ := rfl
    rw [h1, h2, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  have hcd := commutator_eq_of_small D hDn ⟨e⟩ hC
  refine ⟨?_⟩
  exact (((commutator ↥(autCentralizer σ)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (h.trans hcd))).trans e

end Small

end CFSG.ComponentClassification.CatFC
