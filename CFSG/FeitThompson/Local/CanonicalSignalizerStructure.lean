module

public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SignalizerAuxiliaryBase
import CFSG.FeitThompson.Local.SignalizerRegularActionFromBase
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

section

variable {G : Type*} [Group G]

theorem conjBy_eq_conjSub (Y : Subgroup G) (g : G) : conjBy Y g = conjSub g Y := by
  ext y; simp [mem_conjBy, mem_conjSub]

theorem normalizer_coe_bot : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
  Subgroup.normalizer_eq_top_iff.2 inferInstance

theorem mem_normalizer_of_conjSub_eq_self {M : Subgroup G} {c : G} (h : conjSub c M = M) :
    c ∈ normalizer (M : Set G) := by
  have h' : conjSub c M = conjSub 1 M := by rw [conjSub_one, h]
  simpa using inv_mem (mem_normalizer_of_conjSub_eq h')

theorem sigmaSignalizer_eq_of_isNormalHall [Finite G] {x : G} {R : Subgroup G}
    (hle : R ≤ centralizer ({x} : Set G))
    (hnorm : (R.subgroupOf (centralizer ({x} : Set G))).Normal)
    (hcard : Nat.card ↥R = sigmaMultiplicity x)
    (hcop : (Nat.card ↥R).Coprime (R.relIndex (centralizer ({x} : Set G)))) :
    sigmaSignalizer x = R := by
  have := hnorm
  have hcardsub :
      Nat.card ↥(R.subgroupOf (centralizer ({x} : Set G))) = sigmaMultiplicity x := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
  have hHall : IsHallPiSubgroup (primeSupport (sigmaMultiplicity x))
      (R.subgroupOf (centralizer ({x} : Set G))) := by
    refine isHallPiSubgroup_iff.2 ⟨fun p hp => ?_, fun p hp hmem => ?_⟩
    · rw [hcardsub] at hp
      exact mem_primeSupport_iff.2
        ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩
    ·
      have hpR : p ∣ Nat.card ↥R := hcard ▸ (mem_primeSupport_iff.1 hmem).2
      have hpidx : p ∣ R.relIndex (centralizer ({x} : Set G)) :=
        Nat.dvd_of_mem_primeFactors hp
      have h1 : p ∣ 1 := by
        have hd := Nat.dvd_gcd hpR hpidx
        rwa [hcop] at hd
      exact (Nat.prime_of_mem_primeFactors hp).ne_one (Nat.dvd_one.1 h1)
  rw [sigmaSignalizer_eq, canonicalSignalizer_eq,
    show supportMultiplicity (maximalSubgroups G) sigmaCore x = sigmaMultiplicity x from rfl,
    ← hHall.eq_piCore, Subgroup.map_subgroupOf_eq_of_le hle]

theorem sigmaSignalizer_eq_bot_of_sigmaMultiplicity_eq_one [Finite G] {x : G}
    (h : sigmaMultiplicity x = 1) : sigmaSignalizer x = ⊥ := by
  rw [sigmaSignalizer_eq, canonicalSignalizer_eq,
    show supportMultiplicity (maximalSubgroups G) sigmaCore x = sigmaMultiplicity x from rfl, h,
    primeSupport_one, piCore_empty, Subgroup.map_bot]

theorem conjSub_mem_sigmaSupportingMaximals [Finite G] {x c : G} {M : Subgroup G}
    (hc : c ∈ centralizer ({x} : Set G)) (hM : M ∈ sigmaSupportingMaximals (G := G) x) :
    conjSub c M ∈ sigmaSupportingMaximals (G := G) x := by
  obtain ⟨hMco, hxM⟩ := mem_sigmaSupportingMaximals.1 hM
  refine mem_sigmaSupportingMaximals.2 ⟨isCoatom_conjSub hMco c, ?_⟩
  rw [sigmaCore_conjSub, mem_conjSub]
  have h : c * x = x * c := mem_centralizer_singleton_iff.1 hc
  have hcx : c * x * c⁻¹ = x := by rw [h, mul_inv_cancel_right]
  rw [hcx]
  exact hxM

end

section

variable {G : Type u} [Group G] [Finite G]

theorem exists_auxiliary_data
    (h₁ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₃ : Statements.FTS_sigma_prime_separation.{u})
    (hG : Prep09.IsMinimalSimpleOddOrder G) {x : G} (hx : x ∈ sigmaSupport G)
    (hk : 1 < sigmaMultiplicity x) (M : Subgroup G)
    (hM : M ∈ sigmaSupportingMaximals (G := G) x) :
    ∃ N : Subgroup G, IsCoatom N ∧
      centralizer ({x} : Set G) ≤ N ∧ x ∈ M ⊓ N ∧ sigmaPrimes N ∩ sigmaPrimes M = ∅ ∧
      sigmaSignalizer x = centIn (sigmaCore N) {x} ∧
      FreeCore.IsInternalSemidirectProduct N (sigmaCore N) (M ⊓ N) ∧
      ((sigmaSignalizer x).subgroupOf (centralizer ({x} : Set G))).Normal ∧
      (Nat.card ↥(sigmaSignalizer x)).Coprime
        ((sigmaSignalizer x).relIndex (centralizer ({x} : Set G))) ∧
      Nat.card ↥(sigmaSignalizer x) = sigmaMultiplicity x ∧
      (∀ N₁ ∈ sigmaSupportingMaximals (G := G) x, ∀ N₂ ∈ sigmaSupportingMaximals (G := G) x,
        ∃! r : G, r ∈ sigmaSignalizer x ∧ conjSub r N₁ = N₂) := by
  obtain ⟨q, hq, -, Q, hQx, hQcard, N, hNco, -, hNQ, hCN, hxMN, hsd, hsep⟩ :=
    FTS_signalizer_auxiliary_base h₁ h₂ h₃ G hG x hx hk M hM
  have hQp : (Nat.card ↥Q).Prime := by rw [hQcard]; exact hq
  have hCQ : centralizer (Q : Set G) ≤ N := (Subgroup.centralizer_le_normalizer _).trans hNQ
  obtain ⟨⟨hR₀C, hR₀norm, hR₀cop⟩, -, htrans, hR₀card⟩ :=
    FTS_signalizer_regular_action_from_base h₃ G hG x hx M hM N hNco hCN hxMN hsd
      ⟨Q, hQx, hQp, hCQ⟩
  have hRR : sigmaSignalizer x = centIn (sigmaCore N) {x} :=
    sigmaSignalizer_eq_of_isNormalHall hR₀C hR₀norm hR₀card hR₀cop
  exact ⟨N, hNco, hCN, hxMN, hsep, hRR, hsd, hRR ▸ hR₀norm, hRR ▸ hR₀cop, hRR ▸ hR₀card,
    hRR ▸ htrans⟩

end

theorem FTS_canonical_signalizer_structure
    (h₁ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₂ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₃ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_canonical_signalizer_structure.{u} := by
  intro G _ _ hamb x hx
  have hG : Prep09.IsMinimalSimpleOddOrder G :=
    { odd_natCard := hamb.odd_natCard
      isSimpleGroup := hamb.isSimpleGroup
      not_isMulCommutative := hamb.not_isMulCommutative
      isSolvable_of_ne_top := hamb.isSolvable }
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  obtain ⟨M₀, hM₀co, hxM₀, hx1⟩ := mem_sigmaSupport.1 hx
  have hM₀ : M₀ ∈ sigmaSupportingMaximals (G := G) x :=
    mem_sigmaSupportingMaximals.2 ⟨hM₀co, hxM₀⟩
  have hfin : (sigmaSupportingMaximals (G := G) x).Finite := Set.toFinite _
  have hk1 : 1 ≤ sigmaMultiplicity (G := G) x := by
    rw [sigmaMultiplicity_eq_ncard]
    exact (Set.ncard_pos hfin).2 ⟨M₀, hM₀⟩
  rcases eq_or_lt_of_le hk1 with hk | hk
  ·
    have hnc : (sigmaSupportingMaximals (G := G) x).ncard = 1 := by
      rw [← sigmaMultiplicity_eq_ncard, ← hk]
    have hsingle : sigmaSupportingMaximals (G := G) x = {M₀} := by
      obtain ⟨T, hT⟩ := Set.ncard_eq_one.1 hnc
      rw [hT] at hM₀ ⊢
      rw [Set.mem_singleton_iff] at hM₀
      rw [hM₀]
    have hRbot : sigmaSignalizer (G := G) x = ⊥ :=
      sigmaSignalizer_eq_bot_of_sigmaMultiplicity_eq_one hk.symm
    have hCM : centralizer ({x} : Set G) ≤ M₀ := by
      intro c hc
      have h := conjSub_mem_sigmaSupportingMaximals hc hM₀
      rw [hsingle, Set.mem_singleton_iff] at h
      rw [← normalizer_coe_eq_of_isCoatom hna hM₀co]
      exact mem_normalizer_of_conjSub_eq_self h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hRbot, Subgroup.bot_subgroupOf]; infer_instance
    · exact ⟨hRbot ▸ bot_le, by rw [hRbot]; simp⟩
    · rw [hRbot, ← hk]; simp
    · intro M hM N hN
      rw [hsingle, Set.mem_singleton_iff] at hM hN
      subst hM; subst hN
      refine ⟨⟨1, by rw [hRbot]; exact one_mem _⟩, ?_, ?_⟩
      · simp
      · intro r _
        ext
        have : (r : G) ∈ (⊥ : Subgroup G) := hRbot ▸ r.2
        simpa using this
    · intro M hM
      rw [hsingle, Set.mem_singleton_iff] at hM
      subst hM
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hRbot, bot_sup_eq, inf_eq_right.2 hCM]
      · rw [hRbot, normalizer_coe_bot]; exact le_top
      · rw [hRbot]; simp
      · rw [hRbot]; simp
    · intro hne
      exact absurd hRbot hne
  ·
    obtain ⟨-, -, -, -, -, -, -, hnorm, hcop, hcard, htrans⟩ :=
      exists_auxiliary_data h₁ h₂ h₃ hG hx hk M₀ hM₀
    refine ⟨hnorm, ⟨sigmaSignalizer_le_centralizer x, hcop⟩, hcard, ?_, ?_, ?_⟩
    ·
      intro M hM N hN
      obtain ⟨r, ⟨hrR, hrc⟩, huniq⟩ := htrans M hM N hN
      refine ⟨⟨r, hrR⟩, ?_, ?_⟩
      · change conjBy M (r : G) = N
        rw [conjBy_eq_conjSub]; exact hrc
      · intro s hs
        refine Subtype.ext (huniq (s : G) ⟨s.2, ?_⟩)
        rw [← conjBy_eq_conjSub]; exact hs
    ·
      intro M hM
      obtain ⟨hMco, hxM⟩ := mem_sigmaSupportingMaximals.1 hM
      obtain ⟨N, -, -, -, -, hRR, hsd, -, -, -, -⟩ :=
        exists_auxiliary_data h₁ h₂ h₃ hG hx hk M hM
      have hRS : sigmaSignalizer (G := G) x ≤ sigmaCore N := by
        rw [hRR]; exact centIn_le _ _
      have hSM : sigmaCore N ⊓ M = ⊥ := by
        refine le_bot_iff.1 ?_
        rw [← hsd.inf_eq_bot]
        exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (sigmaCore_le N)))
      have hRM : sigmaSignalizer (G := G) x ⊓ M = ⊥ := by
        refine le_bot_iff.1 ?_
        calc sigmaSignalizer (G := G) x ⊓ M ≤ sigmaCore N ⊓ M := inf_le_inf_right M hRS
          _ = ⊥ := hSM
      refine ⟨⟨?_, ?_, ?_⟩, hRM⟩
      ·
        refine le_antisymm (sup_le (sigmaSignalizer_le_centralizer x) inf_le_right) ?_
        intro c hc
        obtain ⟨r, ⟨hrR, hrc⟩, -⟩ :=
          htrans M hM (conjSub c M) (conjSub_mem_sigmaSupportingMaximals hc hM)
        have hcr : c * r⁻¹ ∈ normalizer (M : Set G) := mem_normalizer_of_conjSub_eq hrc
        have hcrM : c * r⁻¹ ∈ M := by
          rwa [normalizer_coe_eq_of_isCoatom hna hMco] at hcr
        have hcrC : c * r⁻¹ ∈ centralizer ({x} : Set G) :=
          mul_mem hc (inv_mem (sigmaSignalizer_le_centralizer x hrR))
        have hmem : c ∈ (M ⊓ centralizer ({x} : Set G)) ⊔ sigmaSignalizer (G := G) x := by
          have h := Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hcrM, hcrC⟩) hrR
          rwa [show c * r⁻¹ * r = c by group] at h
        rwa [sup_comm] at hmem
      · exact le_normalizer_of_normal_subgroupOf (sigmaSignalizer_le_centralizer x) hnorm
      · rw [disjoint_iff]
        refine le_bot_iff.1 ?_
        calc sigmaSignalizer (G := G) x ⊓ (M ⊓ centralizer ({x} : Set G))
            ≤ sigmaSignalizer (G := G) x ⊓ M := inf_le_inf_left _ inf_le_left
          _ = ⊥ := hRM
    ·
      intro _ M hM
      obtain ⟨N, hNco, hCN, -, hsep, hRR, -, -, -, -, -⟩ :=
        exists_auxiliary_data h₁ h₂ h₃ hG hx hk M hM
      obtain ⟨hMco, hxM⟩ := mem_sigmaSupportingMaximals.1 hM
      have hRS : sigmaSignalizer (G := G) x ≤ sigmaCore N := by
        rw [hRR]; exact centIn_le _ _
      have hxN : x ∈ N := hCN (mem_centralizer_iff.2 (by simp))
      exact ⟨N, hNco, hCN, hRS, Subgroup.mem_inf.2 ⟨sigmaCore_le M hxM, hxN⟩,
        by rw [Set.inter_comm]; exact hsep⟩

end

end CFSG.FeitThompson.Proofs
