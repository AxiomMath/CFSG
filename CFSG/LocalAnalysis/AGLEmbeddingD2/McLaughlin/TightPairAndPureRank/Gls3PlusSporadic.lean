module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusGLB
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.NativeFinite
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase
public import CFSG.Quasithin.EmptyFaithful.S1421QA15N1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeIdent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2HS
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi24
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusTh
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusLy
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusSuz
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2M22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi22
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusON
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusJ3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2M23
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusHN
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BRowsOf
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Mathieu
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2J2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Ru
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreJ4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreHe

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

section Core

theorem sporGammaOneAt_of_core {s : TauCeti.SporadicName} [Finite (NativeSporadic.Carrier s)]
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group)) {p : ℕ} (hp : p.Prime)
    (h : ∀ S : Sylow p (NativeSporadic.Carrier s),
      GLBCore p 2 (S : Subgroup (NativeSporadic.Carrier s)) = ⊤) : SporGammaOneAt s p := by
  intro K _ _ ⟨e⟩ T
  obtain ⟨f⟩ := hbr
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S⟩ : Nonempty (Sylow p (NativeSporadic.Carrier s)) := inferInstance
  refine glbCore_eq_top_of_mulEquiv hp (e.trans f.symm) S.isPGroup' ?_ T
  exact eq_top_iff.mpr (by rw [← h S]; exact glbCore_anti p (by norm_num) _)

theorem sporGammaOneAt_of_coreSup {s : TauCeti.SporadicName} [Finite (NativeSporadic.Carrier s)]
    (hbr : Nonempty (NativeSporadic.Carrier s ≃* s.Group))
    (hrk : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier s)))
    (h : ∀ S : Sylow 3 (NativeSporadic.Carrier s), ∀ A : Subgroup (NativeSporadic.Carrier s),
      A ≤ (S : Subgroup (NativeSporadic.Carrier s)) → IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
        GLBCore 3 2 (S : Subgroup (NativeSporadic.Carrier s)) ⊔ GLBCore 3 1 A = ⊤) :
    SporGammaOneAt s 3 := by
  intro K _ _ ⟨e⟩ T
  obtain ⟨f⟩ := hbr
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hEa, hEc⟩ := exists_elem_of_pRank (G := NativeSporadic.Carrier s) (p := 3)
    (by norm_num) ⊤
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 2)
    (by rw [hEc]; exact pow_dvd_pow 3 hrk)
  set A : Subgroup (NativeSporadic.Carrier s) := A₀.map E.subtype with hA
  have hAE : A ≤ E := Subgroup.map_subtype_le A₀
  have hAa : IsElemAbelian 3 A := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, ⟨x, -, rfl⟩⟩ ⟨_, ⟨y, -, rfl⟩⟩
      apply Subtype.ext
      change (x : NativeSporadic.Carrier s) * y = y * x
      exact congrArg Subtype.val (hEa.1.is_comm.comm x y)
    · rintro _ ⟨x, -, rfl⟩
      exact hEa.2 x x.2
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [hA, Subgroup.card_map_of_injective E.subtype_injective, hA₀]
  obtain ⟨S, hAS⟩ := (isPGroup_of_isElemAbelian hAa).exists_le_sylow
  have hcore : GLBCore 3 1 (S : Subgroup (NativeSporadic.Carrier s)) = ⊤ :=
    eq_top_iff.mpr (by
      rw [← h S A hAS hAa hAc]
      exact sup_le (glbCore_anti 3 (by norm_num) _) (glbCore_mono 3 1 hAS))
  exact glbCore_eq_top_of_mulEquiv Nat.prime_three (e.trans f.symm) S.isPGroup' hcore T

end Core


set_option linter.unusedSectionVars false

theorem sporGammaOneAt_three (s : TauCeti.SporadicName) (h11 : s ≠ .M11) (hJ1 : s ≠ .J1) :
    SporGammaOneAt s 3 := by
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  have hfin : ∀ t : TauCeti.SporadicName, t ≠ .M → Finite (NativeSporadic.Carrier t) :=
    CFSG.Sporadic.finite_carrier_of_ne_M
  cases s
  case M11 => exact absurd rfl h11
  case J1 => exact absurd rfl hJ1
  case M => exact CFSG.AGLEmbedding.MonsterThree.sporGammaOneAt_M_three
  case M12 =>
    have := hfin .M12 (by decide)
    exact sporGammaOneAt_of_core hbr Nat.prime_three glbCore_M12_three
  case J4 =>
    have := hfin .J4 (by decide)
    exact sporGammaOneAt_of_core hbr Nat.prime_three glbCore_J4_three
  case He =>
    have := hfin .He (by decide)
    exact sporGammaOneAt_of_core hbr Nat.prime_three glbCore_He_three
  case M24 =>
    have := hfin .M24 (by decide)
    exact sporGammaOneAt_of_coreSup hbr (CFSG.Quasithin.two_le_pRank_M24_1515e)
      glbCore_sup_M24_three
  case J2 =>
    have := hfin .J2 (by decide)
    exact sporGammaOneAt_of_coreSup hbr (CFSG.Quasithin.two_le_pRank_J2_1515e)
      glbCore_sup_J2_three
  case Ru =>
    have := hfin .Ru (by decide)
    exact sporGammaOneAt_of_coreSup hbr (CFSG.Quasithin.two_le_pRank_Ru_1515e)
      glbCore_sup_Ru_three
  case M22 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_M22_three
  case M23 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_M23_three
  case HS => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_HS_three
  case J3 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_J3_three
  case McL => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_McL_three
  case Co1 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Co1_three
  case Co2 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Co2_three
  case Co3 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Co3_three
  case Suz => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Suz_three
  case Fi22 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Fi22_three
  case Fi23 => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Fi23_three
  case Fi24Prime =>
    exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Fi24_three
  case HN => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_HN_three
  case Ly => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Ly_three
  case Th => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_Th_three
  case ONan => exact sporGammaOneAt_of_fusion Nat.prime_three hbr fusionGenerationOf_ON_three
  case B =>
    exact sporGammaOneAt_of_fusion Nat.prime_three hbr
      (BCox.fusionGenerationOf_B_three card_B_pos)

theorem gls3PlusCase_sporadic_of_ne (s : TauCeti.SporadicName) (h11 : s ≠ .M11) (hJ1 : s ≠ .J1) :
    Gls3PlusCase (.sporadic s) :=
  gls3PlusCase_of_glbCore _ fun K _ _ _ _ he T => sporGammaOneAt_three s h11 hJ1 K he T

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
