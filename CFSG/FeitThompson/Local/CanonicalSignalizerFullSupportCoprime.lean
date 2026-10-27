module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaNonemptyNoPrimeInOtherSigma

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem coprime_natCard_of_le_sigmaCore [Finite G] {T R X : Subgroup G}
    (hR : R ≤ sigmaCore T)
    (h : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥X → r ∉ sigmaPrimes T) :
    Nat.Coprime (Nat.card ↥R) (Nat.card ↥X) := by
  by_contra hc
  obtain ⟨p, hp, hpR, hpX⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  exact h p hp hpX (isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) p
    (Nat.mem_primeFactors.2 ⟨hp, hpR.trans (Subgroup.card_dvd_of_le hR), Nat.card_pos.ne'⟩))

theorem FTS_canonical_signalizer_full_support_coprimality
    (h₁ : Statements.FBG_kappa_nontrivial_complement_structure.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_pair_hall_intersection.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₇ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₈ : Statements.FTS_kappa_free_auxiliary_cross_point_coprimality.{u})
    (h₉ : Statements.FTS_signalizer_unique_supporting_maximum.{u}) :
    Statements.FTS_canonical_signalizer_full_support_coprimality.{u} := by
  intro G _ _ hG M hM
  have hsimple := hG.isSimpleGroup
  have hodd := hG.odd_natCard
  have hna := hG.not_isMulCommutative
  have hsolv := hG.isSolvable
  have hMc : IsCoatom M := CFSG.FeitThompson.mem_maximalSubgroups.1 hM
  have key : ∀ a ∈ sigmaCore M, a ≠ 1 →
      ((kappaPrimes M).Nonempty →
          Nat.Coprime (Nat.card ↥(sigmaSignalizer a)) (Nat.card ↥M)) ∧
        (∀ b ∈ M, b ≠ 1 → sigmaCore M ⊓ centralizer ({b} : Set G) ≠ ⊥ →
          Nat.Coprime (Nat.card ↥(sigmaSignalizer a))
            (Nat.card ↥(M ⊓ centralizer ({b} : Set G)))) := by
    intro a ha ha1
    have ha' : a ∈ sigmaSupport G := CFSG.FeitThompson.mem_sigmaSupport.2 ⟨M, hMc, ha, ha1⟩
    have hMsupp : M ∈ sigmaSupportingMaximals a :=
      CFSG.FeitThompson.mem_sigmaSupportingMaximals.2 ⟨hMc, ha⟩
    have hcard : Nat.card ↥(sigmaSignalizer a) = sigmaMultiplicity a := (h₇ G hG a ha').2.2.1
    by_cases hk : 1 < sigmaMultiplicity a
    ·
      have h9 := h₉ G ⟨hodd, hsimple, hna, hsolv⟩ a ha' hk
      obtain ⟨T, ⟨hTc, hTle⟩, hTuniq⟩ := h9.1
      have hT := h9.2 T hTc hTle
      have hTu : IsUniqueMaximalOvergroup (centralizer ({a} : Set G)) T :=
        ⟨hTc, hTle, fun N hN hNle => hTuniq N ⟨hN, hNle⟩⟩
      have hRT : sigmaSignalizer a ≤ sigmaCore T := by
        rw [hT.1]; exact Prep09.centIn_le _ _
      have hTM := hT.2.2.2 M hMsupp
      have hcopM : (kappaPrimes M).Nonempty →
          Nat.Coprime (Nat.card ↥(sigmaSignalizer a)) (Nat.card ↥M) := by
        intro hκ
        refine coprime_natCard_of_le_sigmaCore hRT ?_
        intro r _ hrM
        exact FTS_kappa_positive_support_sigma_primes_disjoint h₁ h₂ h₃ h₄ h₅ h₆ h₉ G hG a ha' hk
          M hMsupp T (CFSG.FeitThompson.mem_maximalSubgroups.2 hTc) hTu hκ r hrM
      refine ⟨hcopM, fun b hb hb1 hbc => ?_⟩
      rcases Set.eq_empty_or_nonempty (kappaPrimes M) with hκ | hκ
      ·
        have h8 := h₈ G hG M hM T (CFSG.FeitThompson.mem_maximalSubgroups.2 hTc)
          hTM.2.2.2.2.1 (fun r hrM hrT => hTM.2.2.2.2.2 r hrT hrM) hκ
          (by rw [Set.inter_comm]; exact hTM.2.2.2.1) ⟨a, ha, ha1, hTle⟩ b hb hb1 hbc
        exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hRT) h8
      ·
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) (hcopM hκ)
    ·
      have hpos : 0 < Nat.card ↥(sigmaSignalizer a) := Nat.card_pos
      have h1 : Nat.card ↥(sigmaSignalizer a) = 1 := by omega
      exact ⟨fun _ => by simp [h1], fun _ _ _ _ => by simp [h1]⟩
  exact ⟨fun a ha ha1 b hb hb1 hbc => (key a ha ha1).2 b hb hb1 hbc,
    fun hκ a ha ha1 => (key a ha ha1).1 hκ⟩

end

end CFSG.FeitThompson.Proofs
