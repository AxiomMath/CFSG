module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.Tau13StrictFixedReflection
import CFSG.FeitThompson.Local.TauOnePrimeCentralizerInclusion
import CFSG.FeitThompson.Local.TauOneHallFixedCentralizer
import CFSG.FeitThompson.Local.SigmaPrimeNormalizerOutsideComplement
import CFSG.FeitThompson.Local.KappaNonemptyNoPrimeInOtherSigma
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05 (centralizerIn_eq)
open CFSG.FeitThompson.Prep09 (centIn_def)

universe u

theorem FNI_tau13_commuting_prime_fixed_equality
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_commuting_prime_fixed_equality.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ hsigma hfac p r P R hp hPE₁ hPcard hr hRcent hRcard
  have hsimple := hG.isSimpleGroup
  have hM : IsCoatom M := hsigma.isCoatom
  have hsd := hsigma.isInternalSemidirectProduct
  have hEM : E ≤ M := hsd.right_le
  have hamb02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb05 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hpp : p.Prime := prime_of_mem_tau1Primes hp
  have hPE : P ≤ E := hPE₁.trans hfac.le_E₁
  have hRE₃ : R ≤ E₃ := hRcent.trans inf_le_left
  have hRcentP : R ≤ centralizer (P : Set G) := hRcent.trans inf_le_right
  have hRE : R ≤ E := hRE₃.trans hfac.le_E₃
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hpp.ne_one hPcard.symm
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRcard
    exact hr.ne_one hRcard.symm
  have hle : (sigmaCore M ⊓ centralizer (P : Set G) : Subgroup G) ≤
      sigmaCore M ⊓ centralizer (R : Set G) := by
    have hincl := FTS_tau_one_prime_centralizer_inclusion h₅ G hamb09 M hM E hEM hsd p r hpp hr hp
      P hPE hPcard R (by rw [centIn_def]; exact le_inf hRE hRcentP) hRcard
    rwa [centIn_def, centIn_def] at hincl
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq
  exfalso
  have hfac05 :
      CFSG.FeitThompson.Prep05.IsTauFactorization M E E₁ E₂ E₃ :=
    { isSigmaComplement := ⟨hM, hsd⟩
      le_E₁ := hfac.le_E₁
      le_E₂ := hfac.le_E₂
      le_E₃ := hfac.le_E₃
      hall_E₁ := hfac.isHall_E₁
      hall_E₂ := hfac.isHall_E₂
      hall_E₃ := hfac.isHall_E₃
      semidirect_E := hfac.outer
      semidirect_E₂₁ := hfac.inner
      isCyclic_E₁ := hfac.isCyclic_E₁
      isCyclic_E₃ := hfac.isCyclic_E₃
      le_commutator_E₃ := hfac.le_commutator_E₃
      normalizes_E₂E₃ := hfac.normal_E₂_sup_E₃
      centralizer_E₃ := by rw [centralizerIn_eq]; exact hfac.centralizer_E₃ }
  obtain ⟨hE₂, T, hT, -, hET, hrσ, hE₁τ⟩ :=
    FNI_tau13_strict_fixed_reflection h₁ h₂ h₃ h₄ h₅ h₆ G hamb05 M E E₁ E₂ E₃ hfac05 p hp P hPE₁
      hPcard r hr R (by rw [centralizerIn_eq]; exact hRcent) hRcard
      (by rw [centralizerIn_eq, centralizerIn_eq]; exact hlt)
  have hTsolv : Group.IsSolvable ↥T := hG.isSolvable_of_ne_top T hT.1
  have hE₁T : E₁ ≤ T := hfac.le_E₁.trans hET
  have hE₁pi : IsPiSubgroup ((sigmaPrimes T)ᶜ) E₁ :=
    isPiSubgroup_iff.2 fun s hs => notMem_sigmaPrimes_of_mem_tau1Primes (hE₁τ s hs)
  obtain ⟨F, hE₁F, hFsd⟩ := exists_isInternalSemidirectProduct_sigmaCore_ge
    hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hT hE₁T hE₁pi
  have hFT : F ≤ T := hFsd.right_le
  have hFsolv : Group.IsSolvable ↥F := @isSolvable_of_le _ _ _ _ hFT hTsolv
  obtain ⟨F₁, hF₁Hall, hE₁F₁⟩ := exists_isHallPiSubgroupOf_ge (π := tau1Primes T) hFsolv hE₁F
    (isPiSubgroup_iff.2 hE₁τ)
  have hRT : R ≤ T := hRE.trans hET
  have hRpi : IsPiSubgroup (sigmaPrimes T) R := by
    refine isPiSubgroup_iff.2 fun s hs => ?_
    rw [hRcard, hr.primeFactors, Finset.mem_singleton] at hs
    exact hs ▸ hrσ
  have hRST : R ≤ sigmaCore T := by
    have _inst : Fintype G := Fintype.ofFinite G
    exact le_sigmaCore_of_isPiSubgroup (h₁ G hamb02 T hT).1 hRT hRpi
  have hkey := (FTS_tau_one_hall_fixed_centralizer h₁ h₅ h₆ G hamb09 T hT F hFT hFsd F₁
    hF₁Hall.1 hF₁Hall.2).2 P (hPE₁.trans hE₁F₁) hPne
  rw [centIn_def, centIn_def] at hkey
  have hRF₁ : R ≤ sigmaCore T ⊓ centralizer (F₁ : Set G) := by
    rw [← hkey]; exact le_inf hRST hRcentP
  have hRcentE₁ : R ≤ centralizer (E₁ : Set G) :=
    (hRF₁.trans inf_le_right).trans (centralizer_le (SetLike.coe_subset_coe.2 hE₁F₁))
  have hE₃comm : IsMulCommutative ↥E₃ := @IsCyclic.isMulCommutative _ _ hfac.isCyclic_E₃
  have hRcentE₃ : R ≤ centralizer (E₃ : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun g hg =>
      congrArg Subtype.val (hE₃comm.is_comm.comm (⟨g, hg⟩ : ↥E₃) ⟨x, hRE₃ hx⟩)
  have hEeq : E₃ ⊔ E₁ = E := by
    have h := hfac.outer.sup_eq
    rwa [hE₂, bot_sup_eq] at h
  have hREcent : R ≤ centralizer (E : Set G) := by
    rw [← hEeq, ← Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.1 hRcentE₃) (Subgroup.le_centralizer_iff.1 hRcentE₁)
  exact hRne (le_bot_iff.1 (hfac.centralizer_E₃ ▸ le_inf hRE₃ hREcent))

end

end CFSG.FeitThompson.Proofs
