module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109CInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace FactsC

theorem eq_conj_of_conj_eq {a b r g₁ g₂ : P45} (h₁ : g₁ * a * g₁⁻¹ = r) (h₂ : g₂ * b * g₂⁻¹ = r) :
    b = (g₂⁻¹ * g₁) * a * (g₂⁻¹ * g₁)⁻¹ := by
  rw [← h₁] at h₂
  calc b = g₂⁻¹ * (g₂ * b * g₂⁻¹) * g₂ := by group
    _ = g₂⁻¹ * (g₁ * a * g₁⁻¹) * g₂ := by rw [h₂]
    _ = (g₂⁻¹ * g₁) * a * (g₂⁻¹ * g₁)⁻¹ := by group

end FactsC

namespace PspFrame

variable {G : Type} [Group G] {L : Subgroup G} (F : PspFrame L)

theorem mem_sup_iff {w : G} (hw : w ∈ normalizer (L : Set G)) :
    w ∈ L ⊔ centralizer (L : Set G) ↔ F.φ ⟨w, hw⟩ ∈ QP45.originalSubgroup := by
  have h := F.sup_subgroupOf_eq
  constructor
  · intro hmem
    have h1 : (⟨w, hw⟩ : ↥(normalizer (L : Set G))) ∈
        (L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := hmem
    rw [h] at h1
    exact h1
  · intro hmem
    have h1 : (⟨w, hw⟩ : ↥(normalizer (L : Set G))) ∈ QP45.originalSubgroup.comap F.φ := hmem
    rw [← h] at h1
    exact h1

theorem phi_sq_eq_one {w : G} (hw : w ∈ normalizer (L : Set G))
    (hww : w * w ∈ centralizer (L : Set G)) : F.φ ⟨w, hw⟩ * F.φ ⟨w, hw⟩ = 1 := by
  have hwwN : w * w ∈ normalizer (L : Set G) := (normalizer (L : Set G)).mul_mem hw hw
  have h1 := (F.ker_iff ⟨w * w, hwwN⟩).2 hww
  rw [show (⟨w * w, hwwN⟩ : ↥(normalizer (L : Set G))) = ⟨w, hw⟩ * ⟨w, hw⟩ from rfl,
    map_mul] at h1
  exact h1

theorem exists_conj_of_phi_eq {s w : G} (hs : s ∈ normalizer (L : Set G))
    (hw : w ∈ normalizer (L : Set G)) {h : P45} (hh : h ∈ QP45.originalSubgroup)
    (hφ : F.φ ⟨w, hw⟩ = h * F.φ ⟨s, hs⟩ * h⁻¹) :
    ∃ l ∈ L, (l⁻¹ * s * l)⁻¹ * w ∈ centralizer (L : Set G) := by
  obtain ⟨l0, hl0⟩ := F.ψ_surj hh
  refine ⟨((l0⁻¹ : ↥L) : G), (l0⁻¹).2, ?_⟩
  have hx : ((l0⁻¹ : ↥L) : G)⁻¹ * s * ((l0⁻¹ : ↥L) : G) = (l0 : G) * s * (l0 : G)⁻¹ := by simp
  rw [hx]
  have h1 : F.φ ((⟨(l0 : G), Subgroup.le_normalizer l0.2⟩ * ⟨s, hs⟩ *
      ⟨(l0 : G), Subgroup.le_normalizer l0.2⟩⁻¹)⁻¹ * ⟨w, hw⟩ :
        ↥(normalizer (L : Set G))) = 1 := by
    have hl : F.φ ⟨(l0 : G), Subgroup.le_normalizer l0.2⟩ = h := by
      rw [← hl0]
      rfl
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hl, hφ]
    group
  exact (F.ker_iff _).1 h1

end PspFrame

theorem asc82FactCTy_of_cert :
    Asc82FactCTy := by
  intro G _ _ L hL w hwN hww
  obtain ⟨F⟩ := exists_pspFrame hL
  have hsq := F.phi_sq_eq_one hwN hww
  have hmem := F.mem_sup_iff hwN
  constructor
  · intro hout
    have hP : F.φ ⟨w, hwN⟩ ∉ QP45.originalSubgroup := fun h => hout (hmem.2 h)
    have hne : F.φ ⟨w, hwN⟩ ≠ 1 := fun h => hP (h ▸ Subgroup.one_mem _)
    rcases MoInv.invCent_cases (F.mem_A ⟨w, hwN⟩) hsq hne with h | h | h | h
    · exact absurd ((MoInv.mem_P_iff_of_invCent h).2 (Or.inl rfl)) hP
    · exact absurd ((MoInv.mem_P_iff_of_invCent h).2 (Or.inr rfl)) hP
    · exact Or.inl ((TyDict.inducesTypeSome_two_plus_iff hL F w).2 ⟨hwN, h⟩)
    · exact Or.inr ((TyDict.inducesTypeSome_four_minus_iff hL F w).2 ⟨hwN, h⟩)
  · intro h hin
    have hP := hmem.1 hin
    rcases h with h | h
    · obtain ⟨hwN', hI⟩ := (TyDict.inducesTypeSome_two_plus_iff hL F w).1 h
      have := (MoInv.mem_P_iff_of_invCent hI).1 hP
      omega
    · obtain ⟨hwN', hI⟩ := (TyDict.inducesTypeSome_four_minus_iff hL F w).1 h
      have := (MoInv.mem_P_iff_of_invCent hI).1 hP
      omega

theorem asc82FactCLay_of_cert :
    Asc82FactCLay := by
  intro G _ _ L hL w hw
  exact layerCent_ne_bot_of_inducesTypeSome hL hw

theorem asc82FactCI2p_of_cert :
    Asc82FactCI2p := by
  intro G _ _ L hL s w hs hw
  obtain ⟨F⟩ := exists_pspFrame hL
  obtain ⟨hsN, hsI⟩ := (TyDict.inducesTypeSome_two_plus_iff hL F s).1 hs
  obtain ⟨hwN, hwI⟩ := (TyDict.inducesTypeSome_two_plus_iff hL F w).1 hw
  obtain ⟨g₁, hg₁, hg₁e⟩ := MoInv.exists_conj_r3 hsI
  obtain ⟨g₂, hg₂, hg₂e⟩ := MoInv.exists_conj_r3 hwI
  exact F.exists_conj_of_phi_eq hsN hwN
    (QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem hg₂) hg₁)
    (FactsC.eq_conj_of_conj_eq hg₁e hg₂e)

theorem asc82FactCI2m_of_cert :
    Asc82FactCI2m := by
  intro G _ _ L hL u v huL hvL hu hv
  obtain ⟨F⟩ := exists_pspFrame hL
  obtain ⟨huN, huI⟩ := (TyDict.inducesTypeSome_two_minus_iff hL F u).1 hu
  obtain ⟨hvN, hvI⟩ := (TyDict.inducesTypeSome_two_minus_iff hL F v).1 hv
  obtain ⟨g₁, hg₁, hg₁e⟩ := MoInv.exists_conj_yB huI
  obtain ⟨g₂, hg₂, hg₂e⟩ := MoInv.exists_conj_yB hvI
  have hrel := FactsC.eq_conj_of_conj_eq hg₁e hg₂e
  obtain ⟨l0, hl0⟩ := F.ψ_surj
    (QP45.originalSubgroup.mul_mem (QP45.originalSubgroup.inv_mem hg₂) hg₁)
  refine ⟨((l0⁻¹ : ↥L) : G), (l0⁻¹).2, ?_⟩
  have key : F.ψ (l0 * ⟨u, huL⟩ * l0⁻¹) = F.ψ ⟨v, hvL⟩ := by
    rw [map_mul, map_mul, map_inv, hl0]
    exact hrel.symm
  have h2 := congrArg Subtype.val (F.ψ_injective key)
  simpa using h2

end CFSG.OddStandard.SmallF3.Omega
