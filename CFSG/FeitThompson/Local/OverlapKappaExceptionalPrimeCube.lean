module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.LowRankSylowCentralProduct
import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.Omega1CentralizerCommutatorBound
import CFSG.FeitThompson.Local.HighRankMaximalPlaneCommutatorPrimePower
import CFSG.FeitThompson.Local.CoprimeActionDetectedOnPrimeTorsion
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.ElementaryMaximalPLengthOneConstraint
import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer
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

open Subgroup

variable {G : Type*} [Group G]

theorem fittingIn_eq_mixedFitting [Finite G] (M : Subgroup G) :
    CFSG.FeitThompson.fittingIn M = mixedFitting M := (mixedFitting_eq M).symm

theorem conj_mem_centreIn_of_mem_normalizer {P : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (P : Set G)) {x : G}
    (hx : x ∈ P ⊓ Subgroup.centralizer (P : Set G)) :
    k * x * k⁻¹ ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
  obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hk x).mp hxP, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : k⁻¹ * y * k ∈ P := by
    have h2 : k * (k⁻¹ * y * k) * k⁻¹ = y := by group
    exact (Subgroup.mem_normalizer_iff.mp hk (k⁻¹ * y * k)).mpr (by rw [h2]; exact hy)
  have hcomm := (Subgroup.mem_centralizer_iff.mp hxc) (k⁻¹ * y * k) hy'
  calc y * (k * x * k⁻¹) = k * ((k⁻¹ * y * k) * x) * k⁻¹ := by group
    _ = k * (x * (k⁻¹ * y * k)) * k⁻¹ := by rw [hcomm]
    _ = (k * x * k⁻¹) * y := by group

theorem le_normalizer_centreIn_of_le_normalizer {P L : Subgroup G}
    (h : L ≤ Subgroup.normalizer (P : Set G)) :
    L ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_centreIn_of_mem_normalizer (h hk) hx, fun hx => ?_⟩
  have h3 := conj_mem_centreIn_of_mem_normalizer (inv_mem (h hk)) hx
  have h4 : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
  rw [h4] at h3
  exact h3

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson Pointwise

universe u

theorem FBG_overlap_kappa_exceptional_prime_cube
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nonabelian_fitting_overlap_maximal_plane.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_overlap_kappa_fixed_line_order_position.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_trivial_residual_prime_fixed_core.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_overlap_kappa_exceptional_prime_cube.{u} := by
  intro G _ _ hG M hM g hg X hX hXne H hH hHnab K hKne hKhall hHS hsemi p hp P hP Z₀ hZ₀ hCZ hKnd
  obtain ⟨hpp, hKcyc, hKstarCard, hKstarLeP, -⟩ :=
    h₂ G hG M hM g hg X hX hXne H hH hHnab K hKne hKhall hHS hsemi p hp P hP Z₀ hZ₀
      (H ⊓ Subgroup.centralizer (K : Set G)) rfl
  have hfactp : Fact p.Prime := ⟨hpp⟩
  have hpodd : Odd p := by
    refine Odd.of_dvd_nat hG.odd_natCard ?_
    rw [hp]
    exact Subgroup.card_subgroup_dvd_card X
  have hPP : P = pCoreIn p H := by rw [hP]
  have hPH : P ≤ H := by rw [hPP, pCoreIn_eq]; exact Subgroup.map_subtype_le _
  have hPp : IsPGroup p ↥P := by rw [hPP]; exact isPGroup_pCoreIn hpp H
  have hKM : K ≤ M := hKhall.1
  have hKnH : K ≤ Subgroup.normalizer (H : Set G) := fun k hk => hsemi.le_normalizer (hKM hk)
  have hKnP : K ≤ Subgroup.normalizer (P : Set G) := by
    rw [hPP]; exact le_normalizer_pCoreIn (G := G) p (X := H) (L := K) hKnH
  have hKnZc : K ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    le_normalizer_centreIn_of_le_normalizer hKnP
  have hZ₀sub : Z₀ ⊆ ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
    rw [hZ₀]; intro z hz; exact hz.1
  have hamb : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsetup : CFSG.FeitThompson.IsFittingOverlapSetup M X g := by
    refine ⟨hM, hg, ?_, hXne⟩
    rw [hX, CFSG.FeitThompson.fittingIn_eq_mixedFitting]
  have hpmem : p ∈ (Nat.card ↥X).primeFactors := by
    rw [← hp, Nat.mem_primeFactors]
    exact ⟨hpp, dvd_rfl, hpp.pos.ne'⟩
  have hPeq : pCoreIn p (CFSG.FeitThompson.hallCoreIn M) = P := by rw [hPP, hH]
  obtain ⟨hPnab0, ⟨Q, hQ⟩, ⟨Z₀', hZ₀'coe, hZ₀'char, hZ₀'card, A, hAdirect, hAea, hAcard, hAmax⟩,
      -, -⟩ :=
    h₁ G hamb M X g hsetup (by rw [← hH]; exact hHnab) p hpmem X le_rfl hp.symm
  rw [hPeq] at hPnab0 hQ hZ₀'coe
  have hPnab : ¬ IsMulCommutative ↥P := hPnab0
  have hZ₀'Z₀ : (Z₀' : Set G) = Z₀ := by
    rw [hZ₀'coe, hZ₀]
    ext z
    rw [mem_pTorsionSet, centreIn_eq]
    rfl
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h] at hPnab
    exact hPnab ⟨⟨fun a b => Subtype.ext (by
      simp [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩⟩
  have hKpi : ∀ r ∈ (Nat.card ↥K).primeFactors, r ∈ kappaPrimes M := by
    intro r hr
    have hcardeq : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    exact isPiSubgroup_iff.mp hKhall.2.isPiSubgroup r (by rw [hcardeq]; exact hr)
  have hcop : (Nat.card ↥K).Coprime p := by
    rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
    intro hdvd
    have hmem : p ∈ kappaPrimes M :=
      hKpi p (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩)
    exact notMem_sigmaPrimes_of_mem_kappaPrimes hmem
      (CFSG.FeitThompson.Proofs.mem_sigmaPrimes_of_isPGroup_le_sigmaCore hpp hPne hPp
        (by rw [← hHS]; exact hPH))
  have hZcAbel : ∀ a b : ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G), a * b = b * a := by
    intro a b
    have h6 := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp a.2).2) (b : G)
      (Subgroup.mem_inf.mp b.2).1
    exact Subtype.ext (by simpa using h6.symm)
  let _ : CommGroup ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
    { (inferInstance : Group ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) with
      mul_comm := hZcAbel }
  have hZcP : IsPGroup p ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
    hPp.to_le inf_le_left
  have hfix : ∀ (b : ↥K) (x : ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)),
      x ^ p = 1 → (conjOnNormalized _ hKnZc) b x = x := by
    intro b x hx
    have hxp : ((x : G)) ^ p = 1 := by
      have h7 := congrArg
        (fun y : ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) => (y : G)) hx
      simpa using h7
    have hxZ₀ : (x : G) ∈ Z₀ := by rw [hZ₀]; exact ⟨x.2, hxp⟩
    have hxmem : (x : G) ∈ H ⊓ Subgroup.centralizer (K : Set G) := by
      have h8 : (x : G) ∈ ((H ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
        rw [hCZ]; exact hxZ₀
      exact h8
    have hcomm := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxmem).2) (b : G) b.2
    apply Subtype.ext
    rw [conjOnNormalized_apply_coe, hcomm, mul_inv_cancel_right]
  have hact_one : ∀ b : ↥K, (conjOnNormalized _ hKnZc) b = 1 :=
    eq_one_of_forall_pow_eq_one hpp hZcP hcop _ hfix
  have hZcCK : (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ≤
      Subgroup.centralizer (K : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h3 : k * z * k⁻¹ = z := by
      have h8 := congrArg
        (fun (f : MulAut ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) =>
          ((f ⟨z, hz⟩ : ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) : G))
        (hact_one ⟨k, hk⟩)
      simpa [conjOnNormalized_apply_coe] using h8
    calc k * z = k * z * k⁻¹ * k := by group
      _ = z * k := by rw [h3]
  have hZcsub : ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) ⊆ Z₀ := by
    rw [← hCZ]
    intro z hz
    exact Subgroup.mem_inf.mpr ⟨hPH (Subgroup.mem_inf.mp hz).1, hZcCK hz⟩
  have hZcZ₀ : ((P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) = Z₀ :=
    Set.Subset.antisymm hZcsub hZ₀sub
  have hZccard : Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = p := by
    have heq : (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = Z₀' :=
      SetLike.coe_injective (by rw [hZcZ₀, hZ₀'Z₀])
    rw [heq]; exact hZ₀'card
  have hfaith : ∀ k ∈ K, (∀ x ∈ P, k⁻¹ * x * k = x) → k = 1 := by
    intro k hk hcent
    by_contra hk1
    have hkappane : (kappaPrimes M).Nonempty := by
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
        (fun h => hKne (Subgroup.card_eq_one.mp h))
      exact ⟨q, hKpi q (Nat.mem_primeFactors.mpr ⟨hq, hqd, Nat.card_pos.ne'⟩)⟩
    have hhall3 : CFSG.FeitThompson.Prep03.IsHallPiOf (kappaPrimes M) K M :=
      ⟨hKM, hKpi, fun r hr => hKhall.2.notMem_of_mem_primeFactors_index r hr⟩
    have hsemi3 : CFSG.FeitThompson.Prep03.IsSemidirect M (sigmaCore M) K := by
      refine ⟨?_, hKM, ?_, ?_, ?_⟩
      · rw [← hHS, ← hsemi.sup_eq]; exact le_sup_left
      · rw [← hHS]; exact hsemi.le_normalizer
      · rw [← hHS]; exact hsemi.sup_eq
      · rw [← hHS]; exact disjoint_iff.mp hsemi.disjoint
    have hsetup3 : CFSG.FeitThompson.Prep03.IsKappaSetup G M K
        (CFSG.FeitThompson.Prep03.cent (sigmaCore M) (K : Set G))
        (K ⊔ CFSG.FeitThompson.Prep03.cent (sigmaCore M) (K : Set G)) :=
      ⟨⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩,
        hM, hkappane, hhall3, rfl, rfl⟩
    obtain ⟨-, -, -, hcentX⟩ := h₃ G M K _ _ hsetup3 hsemi3
    have hzle : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hk
    have hzne : Subgroup.zpowers k ≠ ⊥ := fun h => hk1 (Subgroup.zpowers_eq_bot.mp h)
    have hcc := hcentX (Subgroup.zpowers k) hzle hzne
    have hPA : P ≤ CFSG.FeitThompson.Prep03.cent (sigmaCore M)
        ((Subgroup.zpowers k : Subgroup G) : Set G) := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨by rw [← hHS]; exact hPH hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : k * x = x * k := by
        have h9 := hcent x hx
        calc k * x = k * (k⁻¹ * x * k) := by rw [h9]
          _ = x * k := by group
      exact ((show Commute k x from hcomm).zpow_left n).eq
    rw [hcc] at hPA
    have hPZc : P ≤ (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
      intro x hx
      have h10 : x ∈ Z₀ := by
        rw [← hCZ, hHS]
        exact hPA hx
      exact hZ₀sub h10
    exact hPnab ⟨⟨fun a b => Subtype.ext
      (((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hPZc a.2)).2) (b : G) b.2).symm)⟩⟩
  have hKcyc' := hKcyc
  obtain ⟨k0, hk0⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥K)
  have hρinj : Function.Injective (conjOnNormalized P hKnP) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h11 : (b : G) = 1 := by
      refine hfaith (b : G) b.2 ?_
      intro x hx
      have h12 := congrArg (fun (f : MulAut ↥P) => ((f ⟨x, hx⟩ : ↥P) : G)) hb
      have h13 : (b : G) * x * (b : G)⁻¹ = x := by
        simpa [conjOnNormalized_apply_coe] using h12
      have hc : (b : G) * x = x * (b : G) := mul_inv_eq_iff_eq_mul.mp h13
      rw [mul_assoc, ← hc, inv_mul_cancel_left]
    exact Subtype.ext (by simpa using h11)
  have hord : orderOf (conjOnNormalized P hKnP k0) = Nat.card ↥K := by
    rw [orderOf_injective _ hρinj k0, hk0]
  have hrank : elementaryAbelianPRank p ↥P ≤ 2 := by
    by_contra hcon
    have h3le : 3 ≤ elementaryAbelianPRank p ↥P := by omega
    have hApg : IsPGroup p ↥A := by
      intro a
      exact ⟨1, Subtype.ext (by simpa using hAea.pow_eq_one a.2)⟩
    obtain ⟨Q', hAQ'⟩ := hApg.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G Q' Q
    have hA'P : Subgroup.map (MulAut.conj c).toMonoidHom A ≤ P := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      have hxQ' : x ∈ (Q' : Subgroup G) := hAQ' hx
      have h15 : c * x * c⁻¹ ∈ P := by
        rw [← hQ, ← hc, Sylow.coe_subgroup_smul]
        simpa using Subgroup.smul_mem_pointwise_smul x (MulAut.conj c) (Q' : Subgroup G) hxQ'
      rw [← hxy]
      simpa using h15
    have hA'max : Maximal (IsElementaryAbelian p) (Subgroup.map (MulAut.conj c).toMonoidHom A) :=
      maximal_isElementaryAbelian_map _ hAmax
    have hA'card : Nat.card ↥(Subgroup.map (MulAut.conj c).toMonoidHom A) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective]
      exact hAcard
    have hEmaxS : Maximal (IsElementaryAbelianSubgroup p)
        ((Subgroup.map (MulAut.conj c).toMonoidHom A).subgroupOf P) :=
      maximal_isElementaryAbelianSubgroup_subgroupOf
        (maximal_isElementaryAbelianSubgroup_iff.mpr
          (maximal_isElementaryAbelian_iff_maximal.mp hA'max)) hA'P
    have hEmax : Maximal (fun (B : Subgroup ↥P) => IsMulCommutative ↥B ∧ ∀ x ∈ B, x ^ p = 1)
        ((Subgroup.map (MulAut.conj c).toMonoidHom A).subgroupOf P) :=
      maximal_isElementaryAbelianSubgroup_iff.mp hEmaxS
    have hEcard :
        Nat.card ↥((Subgroup.map (MulAut.conj c).toMonoidHom A).subgroupOf P) = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'P).toEquiv]
      exact hA'card
    have hb := orderOf_dvd_sub_one_of_coprime_of_maximal_plane hpp hpodd hPp hEmax hEcard h3le
      (B := ⊤) (b := conjOnNormalized P hKnP k0) (Subgroup.mem_top _) (by rw [hord]; exact hcop)
    rw [hord] at hb
    exact hKnd hb
  have hMOS : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsyl : _root_.CFSG.FeitThompson.Prep06.IsSylowIn p P ⊤ := by
    refine ⟨le_top, ?_⟩
    rw [Subgroup.card_top, ← hQ]
    exact Q.card_eq_multiplicity
  obtain ⟨B, C, hBP, hCP, hBC, hBcard, hBnab, hBexp, hCne, hCcyc, hCZ', hBCinf, hBCcoe,
      hBCcard⟩ :=
    CFSG.FeitThompson.Proofs.FPL_low_rank_sylow_central_product h₄ G hMOS p hpp hpodd P hsyl hrank hPnab
  have hCcard : Nat.card ↥C = p := by
    have hdvd : Nat.card ↥C ∣ p := by
      rw [← hZccard]; exact Subgroup.card_dvd_of_le hCZ'
    rcases (Nat.Prime.eq_one_or_self_of_dvd hpp _ hdvd) with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hCne
    · exact h
  have hCB : C ≤ B := by
    have h16 : B ⊓ C = C := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hCcard, hBCcard])
    rw [← h16]; exact inf_le_left
  have hPB : P = B := le_antisymm (by rw [← hBC]; exact sup_le le_rfl hCB) hBP
  refine ⟨hpp, hpodd, hZcZ₀, hZccard, hrank, by rw [hPB]; exact hBcard, ?_, hfaith, hcop, ?_⟩
  · intro x hx
    exact hBexp x (by rw [← hPB]; exact hx)
  · intro k hk z hz
    have h17 := (Subgroup.mem_centralizer_iff.mp (hZcCK hz)) k hk
    rw [mul_assoc, ← h17, inv_mul_cancel_left]

end

end CFSG.FeitThompson.Proofs
