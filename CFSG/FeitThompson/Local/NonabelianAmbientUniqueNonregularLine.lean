module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NonabelianAmbientPlaneCentralizer
import CFSG.FeitThompson.Local.NonregularPlaneLineUniqueCentralizer
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PrimeFixedMinimalQuotient
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.CentralPlaneConstrainedTransitivity
import CFSG.FeitThompson.OddOrder.ExponentComplementCyclicHallAction
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise

variable {G : Type*} [Group G] {p : ℕ}

theorem le_of_forall_inf_centralizer_singleton_le [Finite G] (hp : p.Prime) {A Q Z : Subgroup G}
    (hAcard : Nat.card A = p ^ 2) (hAexp : ∀ x ∈ A, x ^ p = 1)
    (hAN : A ≤ normalizer (Q : Set G)) (hQsolv : Group.IsSolvable Q)
    (hpQ : ¬ p ∣ Nat.card Q)
    (hle : ∀ a ∈ A, a ≠ 1 → Q ⊓ centralizer ({a} : Set G) ≤ Z) :
    Q ≤ Z := by
  have := hQsolv
  have hexp : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (by simpa using hAexp (a : G) a.2)
  set ρ : A →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hAN) with hρ
  have hkey := iSup_autFixedSubgroup_eq_top hp hAcard hexp ρ hpQ
  have hW : (⨆ (a : A) (_ : a ≠ 1), autFixedSubgroup (ρ a)) ≤ Z.subgroupOf Q := by
    refine iSup₂_le fun a ha y hy => ?_
    have h1 := congrArg Subtype.val (mem_autFixedSubgroup.1 hy)
    rw [hρ] at h1
    simp only [MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion] at h1
    have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    exact hle (a : G) a.2 ha'
      ⟨y.2, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h1).symm⟩
  rw [hkey] at hW
  intro x hx
  exact hW (mem_top (⟨x, hx⟩ : Q))

theorem map_conj_inv_eq_self_of_mem_centralizer {A : Subgroup G} {g : G}
    (hg : g ∈ centralizer (A : Set G)) : A.map (MulAut.conj g⁻¹ : G →* G) = A := by
  have key : ∀ a ∈ A, g⁻¹ * a * g = a := by
    intro a ha
    have h : a * g = g * a := mem_centralizer_iff.1 hg a ha
    calc g⁻¹ * a * g = g⁻¹ * (a * g) := by group
      _ = g⁻¹ * (g * a) := by rw [h]
      _ = a := by group
  refine le_antisymm ?_ fun x hx => ?_
  · rintro x ⟨a, ha, rfl⟩
    have h2 : (MulAut.conj g⁻¹ : G →* G) a = a := by simpa using key a ha
    rw [h2]; exact ha
  · exact ⟨x, hx, by simpa using key x hx⟩

theorem mem_normalizer_inf_of_mem_of_mem {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conj_smul_eq] at hH hK ⊢
  rw [smul_inf, hH, hK]

theorem mem_normalizer_centralizer_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conj_smul_eq] at hg ⊢
  rw [← centralizer_conj_smul, hg]

theorem eq_of_le_of_le_of_ne_of_natCard_eq_sq [Finite G] (hp : p.Prime) {A A₀ B : Subgroup G}
    (hAcard : Nat.card A = p ^ 2) (hA₀card : Nat.card A₀ = p) (h₀B : A₀ ≤ B) (hBA : B ≤ A)
    (hne : B ≠ A) : B = A₀ := by
  have hdvd : Nat.card B ∣ p ^ 2 := hAcard ▸ Subgroup.card_dvd_of_le hBA
  have hdvd0 : p ∣ Nat.card B := hA₀card ▸ Subgroup.card_dvd_of_le h₀B
  obtain ⟨k, hk⟩ := hdvd0
  have hk' : k ∣ p := by
    have h1 : p * k ∣ p * p := by rw [← hk, ← pow_two]; exact hdvd
    exact (mul_dvd_mul_iff_left hp.ne_zero).1 h1
  rcases (hp.eq_one_or_self_of_dvd k hk') with rfl | rfl
  · exact (Subgroup.eq_of_le_of_card_ge h₀B (by simp [hk, hA₀card])).symm
  · exact absurd (Subgroup.eq_of_le_of_card_ge hBA (by rw [hAcard, hk, ← pow_two])) hne

theorem le_conj_smul_of_conj_inv_smul_le {H K : Subgroup G} {g : G}
    (h : MulAut.conj g⁻¹ • H ≤ K) : H ≤ MulAut.conj g • K := by
  have h2 : MulAut.conj g • (MulAut.conj g⁻¹ • H) ≤ MulAut.conj g • K := smul_mono_right _ h
  rwa [smul_smul, show MulAut.conj g * MulAut.conj g⁻¹ = 1 by
    rw [← map_mul, mul_inv_cancel, map_one], one_smul] at h2

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson

universe u

theorem FNI_nonabelian_ambient_unique_nonregular_line
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u} := by
  intro G _ _ hG p M A E hOSP hSC hAE hnonab
  have hp : p.Prime := hOSP.prime
  have hfp := Fact.mk hp
  have := hG.isSimpleGroup
  have hFin : Fintype G := Fintype.ofFinite G
  have hM : IsCoatom M := hOSP.isCoatom
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG03 : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG08 : CFSG.FeitThompson.Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hsemi := hSC.isInternalSemidirectProduct
  have hsetup : CFSG.FeitThompson.Prep03.IsPlaneSetup G p M A E :=
    ⟨hG03, hM, hp, hOSP.notMem_sigmaPrimes, hOSP.le, hOSP.isElementaryAbelianPlane,
      ⟨hsemi.left_le, hsemi.right_le, hsemi.le_normalizer, hsemi.sup_eq,
        disjoint_iff.1 hsemi.disjoint⟩, hAE⟩
  have hplane08 : CFSG.FeitThompson.Prep08.IsPlaneAt p A :=
    ⟨isElementaryAbelian_iff_isElementaryAbelianSubgroup.2
      hOSP.isElementaryAbelianPlane.isElementaryAbelianSubgroup,
      hOSP.isElementaryAbelianPlane.natCard'⟩
  have hAcard : Nat.card A = p ^ 2 := hOSP.isElementaryAbelianPlane.natCard'
  have hAexp : ∀ x ∈ A, x ^ p = 1 :=
    hOSP.isElementaryAbelianPlane.isElementaryAbelianSubgroup.pow_eq_one
  obtain ⟨hEnormA, hlines, -, -, -⟩ := h₂ G hG p M A E hOSP hSC hAE
  obtain ⟨hSnil, hSCA, -⟩ := h₆ G hG08 M A p hM hp hOSP.notMem_sigmaPrimes hOSP.le hplane08
  have hSne : sigmaCore M ≠ ⊥ := (FBG_sigma_core_nontrivial h₁ G hG02 M hM).2
  have hSsolv : Group.IsSolvable (sigmaCore M) := by have := hSnil; infer_instance
  have hpS : ¬ p ∣ Nat.card (sigmaCore M) :=
    not_dvd_natCard_sigmaCore_of_notMem_sigmaPrimes hp hOSP.notMem_sigmaPrimes
  have hANS : A ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    hOSP.le.trans hsemi.le_normalizer
  have hAp : IsPGroup p A := IsPGroup.of_card hAcard
  obtain ⟨P', hP'⟩ := (hAp.of_equiv (subgroupOfEquivOfLe hAE).symm).exists_le_sylow
  set P : Subgroup G := (P' : Subgroup ↥E).map E.subtype with hPdef
  have hAP : A ≤ P := fun x hx =>
    ⟨⟨x, hAE hx⟩, hP' (show (⟨x, hAE hx⟩ : ↥E) ∈ A.subgroupOf E from hx), rfl⟩
  have hPsyl : CFSG.FeitThompson.Prep03.IsSylowOf p P E := by
    refine ⟨Subgroup.map_subtype_le _, ?_⟩
    rw [hPdef, Subgroup.card_subtype]
    exact P'.card_eq_multiplicity
  obtain ⟨R', hPR⟩ := (P'.isPGroup'.map E.subtype).exists_le_sylow
  set R : Subgroup G := (R' : Subgroup G) with hRdef
  obtain ⟨Q, hQ, hQnc⟩ := hnonab
  obtain ⟨hPcomm, hRnc, hPltR, hRM, hCRA, hZall⟩ :=
    FNI_nonabelian_ambient_plane_centralizer h₂ h₄ h₅ G hG03 p M A E P R hsetup
      ⟨Q, (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).1 hQ, hQnc⟩ hPsyl hAP
      R'.card_eq_multiplicity hPR
  set Z₀ : Subgroup G := subgroupCenterTorsionBy R p with hZ₀def
  obtain ⟨hZ₀A, hZ₀card, htrans⟩ := hZall Z₀ (by
    ext z
    simp only [hZ₀def, SetLike.mem_coe, mem_subgroupCenterTorsionBy, Set.mem_ofPred_eq,
      CFSG.FeitThompson.Prep03.cent, Subgroup.mem_inf, mem_centralizer_iff]
    tauto)
  have hRZ₀ : R ≤ centralizer ((Z₀ : Subgroup G) : Set G) :=
    le_centralizer_iff.1 fun z hz =>
      mem_centralizer_iff.2 fun x hx => ((mem_subgroupCenterTorsionBy.1 hz).2.1 x hx)
  have hRnotle : ¬ R ≤ M := fun h => hPltR.not_ge (hRM ▸ le_inf le_rfl h)
  obtain ⟨e, heA, he1, heC⟩ :=
    exists_ne_one_inf_centralizer_singleton_ne_bot hp hAcard hAexp hANS hSsolv hpS hSne
  set A₀ : Subgroup G := zpowers e with hA₀def
  have hA₀A : A₀ ≤ A := zpowers_le.2 heA
  have hA₀card : Nat.card A₀ = p := by
    rw [hA₀def, Nat.card_zpowers, orderOf_eq_prime (hAexp e heA) he1]
  have hcentA₀ : centralizer ((A₀ : Subgroup G) : Set G) = centralizer ({e} : Set G) := by
    rw [hA₀def]; exact centralizer_coe_zpowers e
  have hA₀C : sigmaCore M ⊓ centralizer ((A₀ : Subgroup G) : Set G) ≠ ⊥ := by
    rw [hcentA₀]; exact heC
  obtain ⟨hUniq, -⟩ :=
    FNI_nonregular_plane_line_unique_centralizer h₂ h₃ G hG p M A E A₀ hOSP hSC hAE
      (hA₀A.trans hAE) hA₀card hA₀C
  have hA₀Z : A₀ ≠ Z₀ := fun h =>
    hRnotle ((h ▸ hRZ₀ : R ≤ centralizer ((A₀ : Subgroup G) : Set G)).trans hUniq.le)
  have hout : ∀ X : Subgroup G, X ≤ E → Nat.card X = p → X ≠ A₀ →
      ¬ centralizer (X : Set G) ≤ M := by
    intro X hXE hXcard hXA₀
    have hXA : X ≤ A := hlines X hXE hXcard
    by_cases hXZ : X = Z₀
    ·
      exact fun h => hRnotle ((hXZ ▸ hRZ₀ : R ≤ centralizer (X : Set G)).trans h)
    obtain ⟨g, hgmem, hgeq⟩ := htrans A₀ X hA₀A hXA hA₀card hXcard hA₀Z hXZ
    obtain ⟨hgN, hgR⟩ := mem_inf.1 hgmem
    have hgX : MulAut.conj g⁻¹ • A₀ = X := hgeq
    have hgM : g ∉ M := by
      intro hgMmem
      have hgP : g ∈ P := hRM ▸ mem_inf.2 ⟨hgR, hgMmem⟩
      have hfix : MulAut.conj g⁻¹ • A₀ = A₀ :=
        map_conj_inv_eq_self_of_mem_centralizer
          (le_centralizer_of_isMulCommutative_of_le hPcomm (hA₀A.trans hAP) hgP)
      exact hXA₀ (by rw [← hgX, hfix])
    have hCX : centralizer (X : Set G)
        = MulAut.conj g⁻¹ • centralizer ((A₀ : Subgroup G) : Set G) := by
      rw [← hgX, ← centralizer_conj_smul]
    intro hle
    have hMg : MulAut.conj g • M = M :=
      hUniq.eq_of_isCoatom (isCoatom_conj_smul hM g)
        (le_conj_smul_of_conj_inv_smul_le (by rw [← hCX]; exact hle))
    exact hgM (by
      have hmem : g ∈ normalizer (M : Set G) := mem_normalizer_iff_conj_smul_eq.2 hMg
      rwa [normalizer_coe_eq_of_isCoatom hG.not_isMulCommutative hM] at hmem)
  have hfree : ∀ X : Subgroup G, X ≤ E → Nat.card X = p → X ≠ A₀ →
      sigmaCore M ⊓ centralizer (X : Set G) = ⊥ := by
    intro X hXE hXcard hXA₀
    by_contra hne
    exact hout X hXE hXcard hXA₀
      (FNI_nonregular_plane_line_unique_centralizer h₂ h₃ G hG p M A E X hOSP hSC hAE hXE
        hXcard hne).1.le
  have hSA₀ : sigmaCore M ≤ centralizer ((A₀ : Subgroup G) : Set G) := by
    refine le_of_forall_inf_centralizer_singleton_le hp hAcard hAexp hANS hSsolv hpS ?_
    intro a ha ha1
    have hXa : (zpowers a : Subgroup G) ≤ A := zpowers_le.2 ha
    have hXacard : Nat.card (zpowers a : Subgroup G) = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hAexp a ha) ha1]
    have hcent : centralizer ((zpowers a : Subgroup G) : Set G) = centralizer ({a} : Set G) :=
      centralizer_coe_zpowers a
    by_cases hXaA₀ : (zpowers a : Subgroup G) = A₀
    · rw [← hcent, hXaA₀]
      exact inf_le_right
    · rw [← hcent, hfree _ (hXa.trans hAE) hXacard hXaA₀]
      exact bot_le
  have hA₀eq : A₀ = A ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G) := by
    refine (eq_of_le_of_le_of_ne_of_natCard_eq_sq hp hAcard hA₀card
      (le_inf hA₀A (le_centralizer_iff.2 hSA₀)) inf_le_left ?_).symm
    intro hAeq
    have hAC : A ≤ centralizer ((sigmaCore M : Subgroup G) : Set G) := hAeq ▸ inf_le_right
    exact hSne (by
      rw [← hSCA]
      exact (inf_eq_left.2 (le_centralizer_iff.1 hAC)).symm)
  refine ⟨A₀, hA₀A, hA₀card, inf_eq_left.2 hSA₀, fun X hXE hXcard hXA₀ =>
    ⟨hfree X hXE hXcard hXA₀, hout X hXE hXcard hXA₀⟩, hA₀eq, hA₀A.trans hOSP.le, ?_⟩
  rw [← hsemi.sup_eq]
  refine sup_le (hSA₀.trans (centralizer_le_normalizer _)) fun x hx => ?_
  rw [hA₀eq]
  exact mem_normalizer_inf_of_mem_of_mem (hEnormA hx)
    (mem_normalizer_centralizer_of_mem_normalizer (hsemi.le_normalizer (hSC.le hx)))

end

end CFSG.FeitThompson.Proofs
