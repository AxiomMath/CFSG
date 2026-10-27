module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate}

theorem sec5qc_img_le {φ : ↥L →* omegaGroup hQ} (hoc : OddCentralCover φ) {z : G}
    (hzL : z ∈ L) (hz2 : orderOf z = 2) (D : Om6Par Q (sec5cdPhi φ ⟨z, hzL⟩))
    {K₁ K₂ : Subgroup G} (h₁ : Sl23PocketIn L z K₁) (h₂ : Sl23PocketIn L z K₂)
    (hQ₁ : Nonempty (↥(twoCoreIn K₁) ≃* QuaternionGroup 2))
    (hcard : Nat.card ↥(twoCoreIn K₁ ⊔ twoCoreIn K₂) = 32) :
    twoCoreIn D.L ⊔ twoCoreIn D.R ≤
      ((twoCoreIn K₁ ⊔ twoCoreIn K₂).subgroupOf L).map (sec5cdPhi φ) := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  let zL : ↥L := ⟨z, hzL⟩
  have hzLord : orderOf zL = 2 := (Subgroup.orderOf_mk z hzL).trans hz2
  have hKL : ∀ K : Subgroup G, Sl23PocketIn L z K → K ≤ L :=
    fun K hK => hK.2.1.trans inf_le_left
  have hmod : ∀ K : Subgroup G, Sl23PocketIn L z K → IsSL23Mod ↥(K.subgroupOf L) := fun K hK =>
    isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hKL K hK)).symm hK.2.2.2
  have hcases := fun K (hK : Sl23PocketIn L z K) => sec5pu_img_cases hoc hzL hzz D hK
  have hc24 := fun K (hK : Sl23PocketIn L z K) => sec5pu_card_img hzL D (hcases K hK)
  have htw : ∀ K K' : Subgroup G, Sl23PocketIn L z K → Sl23PocketIn L z K' →
      (K.subgroupOf L).map (sec5cdPhi φ) = (K'.subgroupOf L).map (sec5cdPhi φ) →
      twoCoreIn K = twoCoreIn K' := by
    intro K K' hK hK' himg
    have hmap : (K.subgroupOf L).map φ = (K'.subgroupOf L).map φ := by
      apply Subgroup.map_injective (omegaGroup hQ).subtype_injective
      rw [Subgroup.map_map, Subgroup.map_map]
      exact himg
    have h := sec5pu_twoCoreIn_eq hoc hzLord hK.1 hK'.1 (hmod K hK) (hmod K' hK') hmap
      (hc24 K hK)
    rw [← sec5pu_map_twoCoreIn_subgroupOf (hKL K hK),
      ← sec5pu_map_twoCoreIn_subgroupOf (hKL K' hK'), h]
  have hne : (K₁.subgroupOf L).map (sec5cdPhi φ) ≠ (K₂.subgroupOf L).map (sec5cdPhi φ) := by
    intro heq
    have h12 := htw K₁ K₂ h₁ h₂ heq
    obtain ⟨e⟩ := hQ₁
    have h8 : Nat.card ↥(twoCoreIn K₁) = 8 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [← h12, sup_idem, h8] at hcard
    omega
  have hDLle : D.L ≤ omegaGroup hQ := by
    have h := D.le_omega_cent
    rw [show D.nd = hQ from Subsingleton.elim _ _] at h
    exact le_sup_left.trans (h.trans inf_le_left)
  have hDRle : D.R ≤ omegaGroup hQ := by
    have h := D.le_omega_cent
    rw [show D.nd = hQ from Subsingleton.elim _ _] at h
    exact le_sup_right.trans (h.trans inf_le_left)
  have hcoreL : ∀ K (hK : Sl23PocketIn L z K),
      (K.subgroupOf L).map (sec5cdPhi φ) = D.L →
      (twoCoreIn (K.subgroupOf L)).map (sec5cdPhi φ) = twoCoreIn D.L := by
    intro K hK hKDL
    have hmapφ := sec5pu_map_twoCoreIn hoc hzLord hK.1 (hmod K hK) (hc24 K hK)
    have hmapι : (twoCoreIn (K.subgroupOf L)).map (sec5cdPhi φ) =
        (twoCoreIn ((K.subgroupOf L).map φ)).map (omegaGroup hQ).subtype := by
      change (twoCoreIn (K.subgroupOf L)).map ((omegaGroup hQ).subtype.comp φ) = _
      rw [← Subgroup.map_map, hmapφ]
    have hJ : (K.subgroupOf L).map φ = D.L.subgroupOf (omegaGroup hQ) := by
      apply Subgroup.map_injective (omegaGroup hQ).subtype_injective
      rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hDLle]
      exact hKDL
    rw [hmapι, hJ, sec5pu_map_twoCoreIn_subgroupOf hDLle]
  have hcoreR : ∀ K (hK : Sl23PocketIn L z K),
      (K.subgroupOf L).map (sec5cdPhi φ) = D.R →
      (twoCoreIn (K.subgroupOf L)).map (sec5cdPhi φ) = twoCoreIn D.R := by
    intro K hK hKDR
    have hmapφ := sec5pu_map_twoCoreIn hoc hzLord hK.1 (hmod K hK) (hc24 K hK)
    have hmapι : (twoCoreIn (K.subgroupOf L)).map (sec5cdPhi φ) =
        (twoCoreIn ((K.subgroupOf L).map φ)).map (omegaGroup hQ).subtype := by
      change (twoCoreIn (K.subgroupOf L)).map ((omegaGroup hQ).subtype.comp φ) = _
      rw [← Subgroup.map_map, hmapφ]
    have hJ : (K.subgroupOf L).map φ = D.R.subgroupOf (omegaGroup hQ) := by
      apply Subgroup.map_injective (omegaGroup hQ).subtype_injective
      rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hDRle]
      exact hKDR
    rw [hmapι, hJ, sec5pu_map_twoCoreIn_subgroupOf hDRle]
  have hImg₁ : (twoCoreIn (K₁.subgroupOf L)).map (sec5cdPhi φ) ≤
      ((twoCoreIn K₁ ⊔ twoCoreIn K₂).subgroupOf L).map (sec5cdPhi φ) := by
    apply Subgroup.map_mono
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ twoCoreIn K₁ := by
      have hm := Subgroup.mem_map_of_mem L.subtype hx
      rwa [sec5pu_map_twoCoreIn_subgroupOf (hKL K₁ h₁)] at hm
    exact (le_sup_left : twoCoreIn K₁ ≤ twoCoreIn K₁ ⊔ twoCoreIn K₂) hx'
  have hImg₂ : (twoCoreIn (K₂.subgroupOf L)).map (sec5cdPhi φ) ≤
      ((twoCoreIn K₁ ⊔ twoCoreIn K₂).subgroupOf L).map (sec5cdPhi φ) := by
    apply Subgroup.map_mono
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ twoCoreIn K₂ := by
      have hm := Subgroup.mem_map_of_mem L.subtype hx
      rwa [sec5pu_map_twoCoreIn_subgroupOf (hKL K₂ h₂)] at hm
    exact (le_sup_right : twoCoreIn K₂ ≤ twoCoreIn K₁ ⊔ twoCoreIn K₂) hx'
  rcases hcases K₁ h₁ with hc₁ | hc₁ <;> rcases hcases K₂ h₂ with hc₂ | hc₂
  · exact absurd (hc₁.trans hc₂.symm) hne
  · refine sup_le ?_ ?_
    · rw [← hcoreL K₁ h₁ hc₁]; exact hImg₁
    · rw [← hcoreR K₂ h₂ hc₂]; exact hImg₂
  · refine sup_le ?_ ?_
    · rw [← hcoreL K₂ h₂ hc₂]; exact hImg₂
    · rw [← hcoreR K₁ h₁ hc₁]; exact hImg₁
  · exact absurd (hc₁.trans hc₂.symm) hne

end CFSG.OddStandard.SmallF3.Omega
