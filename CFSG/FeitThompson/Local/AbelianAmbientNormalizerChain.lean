module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.AbelianAmbientCharacteristicChain
import CFSG.FeitThompson.Local.AbelianAmbientTauTwoFitting
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem normalizer_le_normalizer_of_characteristic_subgroupOf {H K : Subgroup G} (hHK : H ≤ K)
    (h : (H.subgroupOf K).Characteristic) :
    normalizer (K : Set G) ≤ normalizer (H : Set G) := by
  have := h
  have hmap := normalizer_le_normalizer_map_subtype K (H.subgroupOf K)
  rwa [Subgroup.map_subgroupOf_eq_of_le hHK] at hmap

theorem FBG_abelian_ambient_normalizer_chain
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_abelian_ambient_normalizer_chain.{u} := by
  intro G _ _ hG M p A E P E₁ E₂ E₃ K hsetup hdec
  obtain ⟨-, -, -, -, hKZ, hAP, hPE₂, hE₂K, hKF, hAchar, hPchar, hE₂char, hKchar⟩ :=
    FBG_abelian_ambient_characteristic_chain h₁ h₂ h₃ h₄ h₅ G hG M p A E P E₁ E₂ E₃ K hsetup hdec
  obtain ⟨-, hNF, -, -, hFeq, -⟩ :=
    FBG_abelian_ambient_tau_two_fitting h₁ h₃ h₄ h₅ G hG M p A E P hsetup
  have hPA : normalizer (P : Set G) ≤ normalizer (A : Set G) :=
    normalizer_le_normalizer_of_characteristic_subgroupOf hAP hAchar
  have hE₂P : normalizer (E₂ : Set G) ≤ normalizer (P : Set G) :=
    normalizer_le_normalizer_of_characteristic_subgroupOf hPE₂ hPchar
  have hKE₂ : normalizer (K : Set G) ≤ normalizer (E₂ : Set G) :=
    normalizer_le_normalizer_of_characteristic_subgroupOf hE₂K hE₂char
  have hFK : normalizer ((mixedFitting E : Subgroup G) : Set G) ≤ normalizer (K : Set G) :=
    normalizer_le_normalizer_of_characteristic_subgroupOf hKF hKchar
  have hAF : normalizer (A : Set G) ≤ normalizer ((mixedFitting E : Subgroup G) : Set G) := by
    have hle := le_normalizer_mixedFitting (normalizer (A : Set G))
    rwa [hFeq] at hle
  have eAP : normalizer (A : Set G) = normalizer (P : Set G) :=
    le_antisymm (hAF.trans (hFK.trans (hKE₂.trans hE₂P))) hPA
  have ePE₂ : normalizer (P : Set G) = normalizer (E₂ : Set G) :=
    le_antisymm (hPA.trans (hAF.trans (hFK.trans hKE₂))) hE₂P
  have eE₂K : normalizer (E₂ : Set G) = normalizer (K : Set G) :=
    le_antisymm (hE₂P.trans (hPA.trans (hAF.trans hFK))) hKE₂
  have eKF : normalizer (K : Set G) = normalizer ((mixedFitting E : Subgroup G) : Set G) :=
    le_antisymm (hKE₂.trans (hE₂P.trans (hPA.trans hAF))) hFK
  have eAK : normalizer (A : Set G) = normalizer (K : Set G) := by rw [eAP, ePE₂, eE₂K]
  refine ⟨eAP, ePE₂, eE₂K, eKF, ?_, ?_, ?_⟩
  ·
    obtain ⟨hMc, hp, hpσ, hAM, hplane, -, hsd, hAE, -, -, -⟩ := id hsetup
    have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
    exact (h₃ G hGosm p M A E ⟨hMc, hp, hpσ, hAM, hplane⟩ ⟨hMc, hsd⟩ hAE).1
  ·
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    rw [eAK]
  ·
    refine (eAP ▸ hNF).trans (Subgroup.le_centralizer_iff.1 ?_)
    exact hKZ.trans (by rw [centreIn_eq]; exact inf_le_right)

end

end CFSG.FeitThompson.Proofs
