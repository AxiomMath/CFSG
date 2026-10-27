module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHFive
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

abbrev quotCommGroupOfCentral {G : Type} [Group G] {R F : Subgroup G}
    [(F.subgroupOf R).Normal] (hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ F) :
    CommGroup (↥R ⧸ F.subgroupOf R) :=
  { (inferInstance : Group (↥R ⧸ F.subgroupOf R)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with
      | H p =>
        induction b using QuotientGroup.induction_on with
        | H q =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
            Subgroup.mem_subgroupOf]
          simpa [mul_assoc] using hcomm (q : G)⁻¹ (R.inv_mem q.2) (p : G)⁻¹ (R.inv_mem p.2) }

theorem needsFive_of_quot {G : Type} [Group G] [Finite G] {R F : Subgroup G} {ξ : G}
    (hξR : ξ ∈ R) (hξF : ξ ∈ F) (hFR : F ≤ R)
    (hFc : ∀ x ∈ F, ∀ r ∈ R, r * x = x * r)
    (hsq : ∀ r ∈ R, r * r ∈ F) (hcomm : ∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ F)
    (hcard : Nat.card ↥R = 32 * Nat.card ↥F) :
    ∀ X : Finset G, (↑X : Set G) ⊆ ↑R → X.card ≤ 4 →
      Subgroup.closure (X : Set G) ⊔ Subgroup.zpowers ξ ≠ R := by
  classical
  intro X hXR hX4 hcl
  haveI : (F.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * (n : G) = (n : G) * (g : G) := hFc _ hn _ g.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, mul_inv_cancel_right]
    exact hn⟩
  have hsqQ : ∀ a : ↥R ⧸ F.subgroupOf R, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H p =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hsq p.1 p.2
  let ψ : ↥R →* ↥R ⧸ F.subgroupOf R := QuotientGroup.mk' (F.subgroupOf R)
  let g : G → ↥R ⧸ F.subgroupOf R := fun x => if h : x ∈ R then ψ ⟨x, h⟩ else 1
  obtain ⟨S, hS, hSY⟩ := @exists_finset_closure_le (↥R ⧸ F.subgroupOf R)
    (quotCommGroupOfCentral hcomm) hsqQ (X.image g)
  have hS16 : S.card ≤ 16 := by
    have hY : (X.image g).card ≤ 4 := Finset.card_image_le.trans hX4
    calc S.card ≤ 2 ^ (X.image g).card := hS
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hY
      _ = 16 := by norm_num
  let K : Subgroup (↥R ⧸ F.subgroupOf R) := Subgroup.closure ((X.image g : Finset _) : Set _)
  let H : Subgroup G := (K.comap ψ).map R.subtype
  have hXH : (X : Set G) ⊆ H := by
    intro x hx
    have hxX : x ∈ X := Finset.mem_coe.1 hx
    have hxR : x ∈ R := hXR hx
    refine Subgroup.mem_map.2 ⟨⟨x, hxR⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hgx : ψ ⟨x, hxR⟩ = g x := by simp [g, hxR]
    rw [hgx]
    exact Subgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_image_of_mem g hxX))
  have hξH : ξ ∈ H := by
    refine Subgroup.mem_map.2 ⟨⟨ξ, hξR⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : ψ ⟨ξ, hξR⟩ = 1 := by
      show ((⟨ξ, hξR⟩ : ↥R) : ↥R ⧸ F.subgroupOf R) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hξF
    rw [h1]
    exact one_mem K
  have hRH : closure (X : Set G) ⊔ zpowers ξ ≤ H :=
    sup_le ((Subgroup.closure_le H).2 hXH) (zpowers_le.2 hξH)
  rw [hcl] at hRH
  have hall : ∀ p : ↥R, ψ p ∈ K := by
    intro p
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.1 (hRH p.2)
    have hqp' : q = p := Subtype.ext hqp
    rw [hqp'] at hq
    exact Subgroup.mem_comap.1 hq
  have hall' : ∀ q : ↥R ⧸ F.subgroupOf R, q ∈ S := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    exact hSY _ (hall p)
  have hFpos : 0 < Nat.card ↥F := Nat.card_pos
  have hQcard : Nat.card (↥R ⧸ F.subgroupOf R) = 32 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (F.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFR).toEquiv, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hFpos h1.symm
  letI : Fintype (↥R ⧸ F.subgroupOf R) := Fintype.ofFinite _
  have hsub : (Finset.univ : Finset (↥R ⧸ F.subgroupOf R)) ⊆ S := fun q _ => hall' q
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hQcard] at hle
  omega

end CFSG.EvenSporadicStandard.Fin76b
