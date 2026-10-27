module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4Stab

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def cenGTwo (K : Type) [Field K] : Subgroup (VEnd K) :=
  TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) ⊓ centralizer {gTwo K}

theorem cenOne_le_cenGTwo : cenOne K ≤ cenGTwo K := by
  intro g hg
  obtain ⟨hg12, hc1⟩ := mem_inf.mp hg
  obtain ⟨hO, hc2⟩ := mem_inf.mp hg12
  refine mem_inf.mpr ⟨hO, mem_centralizer_singleton_iff.mpr ?_⟩
  have h2 := mem_centralizer_singleton_iff.mp hc2
  have h1 := mem_centralizer_singleton_iff.mp hc1
  rw [gTwo, ← mul_assoc, h2, mul_assoc, h1, ← mul_assoc]

theorem card_cenGTwo_le [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (cenGTwo K) ≤ Nat.card K ^ 2 * Nat.card (cenOne K) := by
  have := finite_VEnd (K := K)
  have hHc : Nat.card ((cenOne K).subgroupOf (cenGTwo K)) = Nat.card (cenOne K) :=
    Nat.card_congr (subgroupOfEquivOfLe cenOne_le_cenGTwo).toEquiv
  have hconj : ∀ g : cenGTwo K, (g : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 2 true)
      (oddZ 3 K) * (g : VEnd K)⁻¹ ∈ Set.range fun p : K × K => eichler (quadOdd 3 K)
        (oddVec 3 K 2 true) (oddZ 3 K + p.1 • oddVec 3 K 0 true + p.2 • oddVec 3 K 1 true) := by
    intro g
    obtain ⟨hgO, hgc⟩ := mem_inf.mp g.2
    obtain ⟨a, b, hab⟩ := exists_conj_eichTwo h2
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO)
      (mem_centralizer_singleton_iff.mp hgc)
    exact ⟨(a, b), hab.symm⟩
  have hcomm : ∀ a b : cenGTwo K, ((a⁻¹ * b : cenGTwo K) : VEnd K) ∈ cenOne K ↔
      (a : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * (a : VEnd K)⁻¹ =
        (b : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
          (b : VEnd K)⁻¹ := by
    intro a b
    obtain ⟨habO, habc⟩ := mem_inf.mp (a⁻¹ * b).2
    have hg := mem_centralizer_singleton_iff.mp habc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hg
    rw [gTwo] at hg
    constructor
    · intro hk
      obtain ⟨hk12, -⟩ := mem_inf.mp hk
      obtain ⟨-, hk2⟩ := mem_inf.mp hk12
      have h1 := mem_centralizer_singleton_iff.mp hk2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc (a : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * (a : VEnd K)⁻¹ =
            a * (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * ((a : VEnd K)⁻¹ * b)) *
              (b : VEnd K)⁻¹ := by group
        _ = a * ((a : VEnd K)⁻¹ * b * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K)) *
              (b : VEnd K)⁻¹ := by rw [h1]
        _ = (b : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
              (b : VEnd K)⁻¹ := by group
    · intro h
      have h1 : (a : VEnd K)⁻¹ * b * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) =
          eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) * ((a : VEnd K)⁻¹ * b) := by
        calc (a : VEnd K)⁻¹ * b * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) =
              (a : VEnd K)⁻¹ * ((b : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 2 true)
                (oddZ 3 K) * (b : VEnd K)⁻¹) * b := by group
          _ = (a : VEnd K)⁻¹ * ((a : VEnd K) * eichler (quadOdd 3 K) (oddVec 3 K 2 true)
                (oddZ 3 K) * (a : VEnd K)⁻¹) * b := by rw [h]
          _ = eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
                ((a : VEnd K)⁻¹ * b) := by group
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨habO, mem_centralizer_singleton_iff.mpr ?_⟩,
        mem_centralizer_singleton_iff.mpr ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (a : VEnd K)⁻¹ * b * eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) =
            (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K))⁻¹ *
              ((a : VEnd K)⁻¹ * b * eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
                eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true)) := by
            rw [h1]; group
        _ = (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K))⁻¹ *
              ((a : VEnd K)⁻¹ * b * (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
                eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true))) := by group
        _ = (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K))⁻¹ *
              (eichler (quadOdd 3 K) (oddVec 3 K 2 true) (oddZ 3 K) *
                eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) *
                  ((a : VEnd K)⁻¹ * b)) := by rw [hg]
        _ = eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) *
              ((a : VEnd K)⁻¹ * b) := by group
  let f : cenGTwo K ⧸ (cenOne K).subgroupOf (cenGTwo K) → Set.range fun p : K × K =>
      eichler (quadOdd 3 K) (oddVec 3 K 2 true)
        (oddZ 3 K + p.1 • oddVec 3 K 0 true + p.2 • oddVec 3 K 1 true) :=
    Quotient.lift (s := QuotientGroup.leftRel ((cenOne K).subgroupOf (cenGTwo K)))
      (fun g => ⟨_, hconj g⟩) (fun a b hab => Subtype.ext
        ((hcomm a b).mp (mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab))))
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    exact QuotientGroup.eq.mpr (mem_subgroupOf.mpr ((hcomm a b).mpr
      (congrArg Subtype.val hxy)))
  calc Nat.card (cenGTwo K) =
        Nat.card (cenGTwo K ⧸ (cenOne K).subgroupOf (cenGTwo K)) *
          Nat.card ((cenOne K).subgroupOf (cenGTwo K)) :=
        card_eq_card_quotient_mul_card_subgroup _
    _ ≤ Nat.card (K × K) * Nat.card (cenOne K) := by
        rw [hHc]
        exact Nat.mul_le_mul_right _ ((Nat.card_le_card_of_injective f hf).trans
          (Finite.card_range_le _))
    _ = Nat.card K ^ 2 * Nat.card (cenOne K) := by rw [Nat.card_prod, _root_.sq]

theorem card_cenGTwo_le_mul [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card (cenGTwo K) ≤ 2 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1) := by
  calc Nat.card (cenGTwo K) ≤ Nat.card K ^ 2 * Nat.card (cenOne K) := card_cenGTwo_le h2
    _ ≤ Nat.card K ^ 2 * (Nat.card K ^ 3 * Nat.card (leviSet K)) :=
        Nat.mul_le_mul_left _ (card_cenOne_le h2)
    _ ≤ Nat.card K ^ 2 * (Nat.card K ^ 3 * (2 * (Nat.card SL(2, K) * Nat.card K))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (card_leviSet_le h2))
    _ = 2 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1) := by
        rw [LieType.Steinberg.card_specialLinearGroup_fin_two]
        ring

end CFSG.ComponentClassification.HarrisLit.T1.S74
