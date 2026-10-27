module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PlaneMaximalOvergroups
import CFSG.FeitThompson.Local.ExceptionalSylowAbelian
import CFSG.FeitThompson.Local.ExceptionalPlaneFixedFreeLines
import CFSG.FeitThompson.Local.NonuniqueLinesAlphaCoreTrivial
import CFSG.FeitThompson.Local.ExceptionalPlaneMaximalElementaryAbelian
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open CFSG.FeitThompson.Prep08
open Subgroup

universe u

theorem FNI_outside_sigma_plane_sylow
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FPL_global_sylow_normalizer_derived.{u})
    (h₃ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₄ : Statements.FTS_nonunique_line_centralizer_bounds.{u})
    (h₅ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FNI_outside_sigma_plane_sylow.{u} := by
  intro G _ _ hG p M A hAplane
  obtain ⟨hM, hp, hpσ, hAM, hAplane2⟩ := hAplane
  have := hG.isSimpleGroup
  have hAea : IsElementaryAbelian p A :=
    isElementaryAbelian_of_nonempty_mulEquiv_pi hAplane2
  have hAcard : Nat.card ↥A = p ^ 2 := hAplane2.natCard'
  have hG8 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hG7 : IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hplane8 : Prep08.IsPlaneAt p A := ⟨hAea, hAcard⟩
  obtain ⟨A₀, hA₀A, hA₀card, hNA₀⟩ :=
    (FTS_plane_maximal_overgroups h₁ h₂ h₄ h₅ G hG8 M A p hM hp hAM hplane8).2 hpσ
  have hpdvd : p ∣ Nat.card ↥M := hA₀card ▸ Subgroup.card_dvd_of_le (hA₀A.trans hAM)
  obtain ⟨e⟩ := hAplane2
  have hconfig : ∀ P : Subgroup G, P ≤ M → A ≤ P →
      Nat.card ↥P = p ^ (Nat.card ↥M).factorization p →
      IsExceptionalPlaneConfig p M A₀ A P := fun P hPM hAP hPcard =>
    ⟨hM, hp, hpσ, hA₀A, hAP, hPM, hA₀card, ⟨e⟩, ⟨hPM, hPcard⟩, hNA₀⟩
  obtain ⟨P₀, hP₀syl, hAP₀⟩ := exists_isSylowOf_ge hp hAM (IsPGroup.of_card hAcard)
  have hP₀M := hP₀syl.le
  have hP₀card : Nat.card ↥P₀ = p ^ (Nat.card ↥M).factorization p :=
    (isSylowOf_iff_natCard hp hP₀M).1 hP₀syl
  have hc₀ := hconfig P₀ hP₀M hAP₀ hP₀card
  obtain ⟨hrank, -, hCM, -⟩ := exceptional_maximal_plane hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable_of_ne_top hM hp hpσ hA₀card hA₀A hAP₀ hP₀M hP₀card hAea hAcard
    hNA₀
  have hmax : Maximal (IsElementaryAbelian p) A :=
    maximal_isElementaryAbelian_of_centralizer_le hp hAea hAcard hCM hrank
  refine ⟨hrank, (maximal_congr fun _ => isElementaryAbelian_iff_isElementaryAbelianSubgroup).1
    hmax, ?_, ?_⟩
  · intro P hPsyl
    have hPM := hPsyl.le
    have hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p :=
      (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hPM).1 hPsyl
    refine ⟨(FTS_exceptional_sylow_abelian h₁ h₃ h₅ G hG7 p M A₀ A P₀ hc₀).2 P ⟨hPM, hPcard⟩,
      fun hAP => ?_⟩
    obtain ⟨hAset, -, -⟩ := FTS_exceptional_plane_fixed_free_lines h₁ h₃ h₅ G hG7 p M A₀ A P
      (hconfig P hPM hAP hPcard)
    exact ⟨hAset, not_normalizer_le_of_notMem_sigmaPrimes hp hpσ hpdvd hPM hPcard⟩
  ·
    obtain ⟨-, -, A₁, -, hA₁A, -, -, hA₁card, -, hA₁free, -⟩ :=
      FTS_exceptional_plane_fixed_free_lines h₁ h₃ h₅ G hG7 p M A₀ A P₀ hc₀
    exact ⟨A₁, hA₁A, hA₁card, hA₁free⟩

end

end CFSG.FeitThompson.Proofs
