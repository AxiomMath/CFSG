module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqCore
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PUniqModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactPocketsUniq6_of (hS : Asc82SchurU43) : Asc82FactPocketsUniq6 := by
  intro G _ _ L z hL hI K₁ K₂ h₁ h₂ _ hQ₁ _ _ hcard _
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  have hoc : OddCentralCover φ := hφ.oddCentralCover hL
  have hz2 : orderOf z = 2 := hI.1
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (h₁.2.1 h₁.1)).1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  let zL : ↥L := ⟨z, hzL⟩
  have hzLord : orderOf zL = 2 := (Subgroup.orderOf_mk z hzL).trans hz2
  have hφzz : φ zL * φ zL = 1 := by
    rw [← map_mul, show zL * zL = 1 from Subtype.ext hzz, map_one]
  have hφz1 : φ zL ≠ 1 := by
    intro h
    have h2 := l34g_x_orderOf_map hoc hzLord
    rw [h, orderOf_one] at h2
    omega
  have hI4 : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ zL) :=
    (t5_isI4PlusIn_iff hL hφ hzL hz2).mp hI
  have hztt : ((φ zL : omegaGroup hQ) : OGroup Q) * ((φ zL : omegaGroup hQ) : OGroup Q) = 1 :=
    congrArg Subtype.val hφzz
  have hzt4 : invType ((φ zL : omegaGroup hQ) : OGroup Q) = (4, 1) :=
    (t5_isI4PlusIn_omega_iff hdim hsgn hztt hφz1).mp hI4
  let D : Om6Par Q (sec5cdPhi φ zL) := Om6Par.mk' hQ hdim hsgn hztt hzt4
  have hKL : ∀ K : Subgroup G, Sl23PocketIn L z K → K ≤ L := fun K hK => hK.2.1.trans inf_le_left
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
  have himg : ∀ K : Subgroup G, Sl23PocketIn L z K →
      (K.subgroupOf L).map (sec5cdPhi φ) = (K₁.subgroupOf L).map (sec5cdPhi φ) ∨
      (K.subgroupOf L).map (sec5cdPhi φ) = (K₂.subgroupOf L).map (sec5cdPhi φ) := by
    intro K hK
    rcases hcases K hK with h | h <;> rcases hcases K₁ h₁ with h1 | h1 <;>
      rcases hcases K₂ h₂ with h2 | h2
    · exact Or.inl (h.trans h1.symm)
    · exact Or.inl (h.trans h1.symm)
    · exact Or.inr (h.trans h2.symm)
    · exact absurd (h1.trans h2.symm) hne
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inl (h.trans h1.symm)
    · exact Or.inl (h.trans h1.symm)
  refine ⟨fun K hK => ?_, ?_⟩
  · rcases himg K hK with h | h
    · exact Or.inl (htw K K₁ hK h₁ h)
    · exact Or.inr (htw K K₂ hK h₂ h)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hgodd⟩
    obtain ⟨hgL, hgc⟩ := Subgroup.mem_inf.mp hg
    let gL : ↥L := ⟨g, hgL⟩
    have hmem : sec5cdPhi φ gL ∈ D.L ⊔ D.R := by
      rw [D.twoRes_eq]
      have hcomm : gL * zL = zL * gL :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgc)
      refine Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨(φ gL).2, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (map_mul (sec5cdPhi φ) _ _).symm.trans
          ((congrArg (sec5cdPhi φ) hcomm).trans (map_mul (sec5cdPhi φ) _ _))
      · have hg' : Odd (orderOf gL) := by rw [← Subgroup.orderOf_coe gL]; exact hgodd
        exact Odd.of_dvd_nat hg' (orderOf_map_dvd _ gL)
    have hsup : D.L ⊔ D.R =
        (K₁.subgroupOf L).map (sec5cdPhi φ) ⊔ (K₂.subgroupOf L).map (sec5cdPhi φ) := by
      rcases hcases K₁ h₁ with h1 | h1 <;> rcases hcases K₂ h₂ with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]
      · rw [h1, h2, sup_comm]
      · exact absurd (h1.trans h2.symm) hne
    rw [hsup, ← Subgroup.map_sup] at hmem
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hmem
    have hn : k⁻¹ * gL ∈ CFSG.oddCore ↥L := by
      rw [← hφ.ker_eq, MonoidHom.mem_ker]
      apply Subtype.ext
      have h1 : sec5cdPhi φ (k⁻¹ * gL) = 1 := by
        rw [map_mul, map_inv, hkg, inv_mul_cancel]
      exact h1
    have hgk : g = (k : G) * ((k⁻¹ * gL : ↥L) : G) := by
      show (gL : G) = ((k * (k⁻¹ * gL) : ↥L) : G)
      rw [mul_inv_cancel_left]
    have hkG : (k : G) ∈ K₁ ⊔ K₂ := by
      have h := Subgroup.mem_map_of_mem L.subtype hk
      rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (hKL K₁ h₁),
        Subgroup.map_subgroupOf_eq_of_le (hKL K₂ h₂)] at h
    have hnG : ((k⁻¹ * gL : ↥L) : G) ∈ oddCoreIn L := Subgroup.mem_map_of_mem L.subtype hn
    have hk' : (k : G) ∈ oddCoreIn L ⊔ K₁ ⊔ K₂ :=
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right : K₁ ⊔ K₂ ≤ oddCoreIn L ⊔ K₁ ⊔ K₂) hkG
    have hn' : ((k⁻¹ * gL : ↥L) : G) ∈ oddCoreIn L ⊔ K₁ ⊔ K₂ :=
      (le_sup_left.trans le_sup_left : oddCoreIn L ≤ oddCoreIn L ⊔ K₁ ⊔ K₂) hnG
    rw [hgk]
    exact Subgroup.mul_mem _ hk' hn'

end CFSG.OddStandard.SmallF3.Omega
