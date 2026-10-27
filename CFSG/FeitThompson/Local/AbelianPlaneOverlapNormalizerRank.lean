module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.AbelianAmbientNormalizerChain
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

theorem FNI_abelian_plane_overlap_normalizer_rank
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_overlap_ambient_sylows.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FNI_plane_normalizer_overlap_prime_maximum.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_abelian_plane_overlap_normalizer_rank.{u} := by
  intro G _ _ hG p M A E P hsetup hPsyl hPab hAP q hq hqrel hqcard
  have hp : p.Prime := hsetup.prime
  have : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup G := hG.isSimpleGroup
  have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hGfbg : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  have hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) E :=
    ⟨hsetup.decomp.2.2.2.1, hsetup.decomp.2.2.1, disjoint_iff.2 hsetup.decomp.2.2.2.2⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hsetup.isCoatom, hsd⟩
  have hplane : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane⟩
  obtain ⟨E₁, E₂, E₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hGosm M E hsc
  have hdec : CFSG.FeitThompson.IsTauHallDecomposition
      M E E₁ E₂ E₃ (E₂ ⊔ E₃) :=
    ⟨hsplit.le_E₁, hsplit.le_E₂, hsplit.le_E₃, hsplit.isHall_E₁, hsplit.isHall_E₂,
      hsplit.isHall_E₃, hsplit.outer, hsplit.inner, rfl⟩
  have hAsetup : CFSG.FeitThompson.IsAbelianAmbientSetup M p A E P :=
    ⟨hsetup.isCoatom, hp, hsetup.notMem_sigma, hsetup.le_M_A, hsetup.isPlane,
      hsetup.decomp.2.1, hsd, hsetup.le_E_A, hPab, ⟨Sylow.ofCard P hPsyl, Sylow.coe_ofCard _ _⟩,
      hAP⟩
  obtain ⟨hNAP, -, -, -, -, -, -⟩ := FBG_abelian_ambient_normalizer_chain h₁ h₂ h₃ h₄ h₇ G hGfbg
    M p A E P E₁ E₂ E₃ (E₂ ⊔ E₃) hAsetup hdec
  have hAcard : Nat.card A = p ^ 2 := hplane.isElementaryAbelianPlane.natCard'
  have hPbot : P ≠ ⊥ := by
    intro hb
    rw [hb, le_bot_iff] at hAP
    rw [hAP, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1, rfl⟩⟩] at hAcard
    exact absurd hAcard.symm (by simpa using (Nat.one_lt_pow two_ne_zero hp.one_lt).ne')
  have hPp : IsPGroup p P := IsPGroup.of_card hPsyl
  have hNlt : normalizer (P : Set G) ≠ ⊤ :=
    (normalizer_lt_top_of_isPGroup hG.not_isMulCommutative hp hPbot hPp).ne
  obtain ⟨T, hT, hNT⟩ := exists_isCoatom_ge_of_ne_top hNlt
  have hNAT : normalizer (A : Set G) ≤ T := hNAP ▸ hNT
  obtain ⟨⟨P₁, hP₁syl, -, hTP₁⟩, -⟩ :=
    h₅ G hGosm p M A E T hplane hsc hsetup.le_E_A hT hNAT q hq hqrel hqcard
  have hP₁card : Nat.card P₁ = p ^ (Nat.card G).factorization p :=
    (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).1 hP₁syl
  have hPT : P ≤ T := le_trans le_normalizer hNT
  have hPP₁ : P ≤ P₁ :=
    le_of_isPGroup_of_le_normalizer_of_natCard_eq hp hP₁card hPp (hPT.trans hTP₁)
  have hPeq : P = P₁ := Subgroup.eq_of_le_of_card_ge hPP₁ (by rw [hP₁card, hPsyl])
  have hTN : T = normalizer (P : Set G) := le_antisymm (hPeq ▸ hTP₁) hNT
  obtain ⟨x, hx, hxord⟩ := exists_mem_orderOf_eq_of_dvd hq hqcard
  have hQ₀ : Nat.card (zpowers x) = q := by rw [Nat.card_zpowers, hxord]
  obtain ⟨hqτ, -⟩ :=
    h₆ G hGosm p M A E T hplane hsc hsetup.le_E_A hT hNAT q hq hqrel hqcard (zpowers x)
      (zpowers_le.2 hx) hQ₀
  rw [← hTN]
  exact elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hqτ

end

end CFSG.FeitThompson.Proofs
