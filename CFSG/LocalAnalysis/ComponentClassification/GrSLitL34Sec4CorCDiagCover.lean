module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCCover

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X]

theorem eq_or_eq_of_le_sup_sup {C N₁ N₂ N₃ N₄ T : Subgroup X} (h₁ : N₁ ≤ C) (h₂ : N₂ ≤ C)
    (h₃ : N₃ ≤ C) (h₄ : N₄ ≤ C) (hc₁ : IsPComponent 2 (N₁.subgroupOf C))
    (hc₂ : IsPComponent 2 (N₂.subgroupOf C)) (hc₃ : IsPComponent 2 (N₃.subgroupOf C))
    (hc₄ : IsPComponent 2 (N₄.subgroupOf C)) (hT₁ : T ≤ N₁ ⊔ N₂) (hT₂ : T ≤ N₃ ⊔ N₄)
    (hTperf : ⁅T, T⁆ = T) (hTO : ¬ T ≤ (pPrimeCore 2 C).map C.subtype) :
    N₁ = N₃ ∨ N₁ = N₄ ∨ N₂ = N₃ ∨ N₂ = N₄ := by
  by_contra h
  push Not at h
  obtain ⟨h13, h14, h23, h24⟩ := h
  have hCN : C ≤ normalizer (((pPrimeCore 2 C).map C.subtype : Subgroup X) : Set X) :=
    fun g hg => normalizer_le_normalizer_map_of_characteristic C (pPrimeCore 2 C)
      (le_normalizer hg)
  have hpair : ∀ {K L : Subgroup X}, K ≤ C → L ≤ C → IsPComponent 2 (K.subgroupOf C) →
      IsPComponent 2 (L.subgroupOf C) → K ≠ L → ∀ x ∈ K, ∀ m ∈ L,
        x⁻¹ * m⁻¹ * x * m ∈ (pPrimeCore 2 C).map C.subtype := by
    intro K L hK hL hKc hLc hne x hx m hm
    have h3 : ⁅x⁻¹, m⁻¹⁆ ∈ ⁅K, L⁆ := commutator_mem_commutator (inv_mem hx) (inv_mem hm)
    have h4 := commutator_le_oddIn_of_ne hK hL hKc hLc hne h3
    rwa [commutatorElement_def, inv_inv, inv_inv] at h4
  have h12 : ∀ {L : Subgroup X}, L ≤ C → IsPComponent 2 (L.subgroupOf C) → N₁ ≠ L → N₂ ≠ L →
      ∀ m ∈ L, ∀ x ∈ N₁ ⊔ N₂, x⁻¹ * m⁻¹ * x * m ∈ (pPrimeCore 2 C).map C.subtype :=
    fun hL hLc h1 h2 m hm => forall_sup_of_forall hCN h₁ h₂
      (fun x hx => hpair h₁ hL hc₁ hLc h1 x hx m hm) fun x hx => hpair h₂ hL hc₂ hLc h2 x hx m hm
  have hstep : ∀ x ∈ N₁ ⊔ N₂, ∀ m ∈ N₃ ⊔ N₄,
      m⁻¹ * x⁻¹ * m * x ∈ (pPrimeCore 2 C).map C.subtype := by
    intro x hx
    refine forall_sup_of_forall hCN h₃ h₄ (fun m hm => ?_) fun m hm => ?_
    · have h5 := inv_mem (h12 h₃ hc₃ h13 h23 m hm x hx)
      rwa [show (x⁻¹ * m⁻¹ * x * m)⁻¹ = m⁻¹ * x⁻¹ * m * x by group] at h5
    · have h5 := inv_mem (h12 h₄ hc₄ h14 h24 m hm x hx)
      rwa [show (x⁻¹ * m⁻¹ * x * m)⁻¹ = m⁻¹ * x⁻¹ * m * x by group] at h5
  apply hTO
  rw [← hTperf, commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h3 := hstep g₂⁻¹ (hT₁ (inv_mem hg₂)) g₁⁻¹ (hT₂ (inv_mem hg₁))
  rwa [inv_inv, inv_inv, ← commutatorElement_def] at h3

theorem le_of_perfect_of_le_sup_odd {A N W : Subgroup X} (hNA : N ≤ normalizer (A : Set X))
    (hNodd : Odd (Nat.card N)) (hWp : ⁅W, W⁆ = W) (hW : W ≤ A ⊔ N) : W ≤ A := by
  set H := A ⊔ N with hH
  have hAH : A ≤ H := le_sup_left
  have hNH : N ≤ H := le_sup_right
  have hAn : (A.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAH).mpr (sup_le le_normalizer hNA)
  set π := QuotientGroup.mk' (A.subgroupOf H) with hπ
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion hNH)) := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf H) q
    have hh : (h : X) ∈ ((A ⊔ N : Subgroup X) : Set X) := h.2
    rw [coe_mul_of_right_le_normalizer_left A N hNA] at hh
    obtain ⟨α, hα, n, hn, hαn⟩ := hh
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    have h1 : (((Subgroup.inclusion hNH ⟨n, hn⟩)⁻¹ * h : H) : X) = n⁻¹ * α * n⁻¹⁻¹ := by
      simp only [coe_mul, coe_inv, Subgroup.coe_inclusion]
      rw [← hαn]
      group
    rw [h1]
    exact (mem_normalizer_iff.mp (inv_mem (hNA hn)) α).mp hα
  have hQodd : Odd (Nat.card (↥H ⧸ A.subgroupOf H)) :=
    Odd.of_dvd_nat hNodd (card_dvd_of_surjective _ hsurj)
  have hQs : Group.IsSolvable (↥H ⧸ A.subgroupOf H) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd
  have hWH : W ≤ H := hW
  have hWperf : Group.IsPerfect ↥W := (Subgroup.isPerfect_iff (H := W)).mpr hWp
  have hWHp : Group.IsPerfect ↥(W.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hWH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hWH).symm.surjective
  have himp : Group.IsPerfect ↥((W.subgroupOf H).map π) :=
    Group.IsPerfect.ofSurjective (π.subgroupMap_surjective _)
  have hbot : (W.subgroupOf H).map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥((W.subgroupOf H).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have hs : Group.IsSolvable ↥((W.subgroupOf H).map π) := inferInstance
    exact Group.IsPerfect.not_isSolvable _ hs
  intro w hw
  have h1 : π ⟨w, hWH hw⟩ = 1 := by
    have h2 : π ⟨w, hWH hw⟩ ∈ (W.subgroupOf H).map π := ⟨⟨w, hWH hw⟩, hw, rfl⟩
    rw [hbot] at h2
    exact h2
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end CFSG.ComponentClassification.GSThmB.CorC
