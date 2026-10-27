module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaCandidateMixedSupportCardinality
import CFSG.FeitThompson.Local.SignalizerPacketCardinality
import CFSG.FeitThompson.Local.KappaDerivedComplement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open _root_.CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem two_mul_natCard_le_natCard_of_lt [Finite G] {Y X : Subgroup G} (h : Y < X) :
    2 * Nat.card ↥Y ≤ Nat.card ↥X := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le h.le
  have hlt : Nat.card ↥Y < Nat.card ↥X :=
    Set.Finite.card_lt_card (Set.toFinite _) (by exact_mod_cast h)
  have hpos : 0 < Nat.card ↥Y := Nat.card_pos
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with hcl | hcl
    · interval_cases c <;> omega
    · exact hcl
  calc 2 * Nat.card ↥Y = Nat.card ↥Y * 2 := by ring
    _ ≤ Nat.card ↥Y * c := Nat.mul_le_mul_left _ hc2
    _ = Nat.card ↥X := hc.symm

theorem residual_measure_contradiction {α : Type*} {F : Finset α} {kf ff : α → ℚ} {g z c : ℚ}
    (hg : 0 < g) (hz : 0 < z) (hn : 2 ≤ (F.card : ℚ))
    (hf : ∀ V ∈ F, g / kf V - g / (2 * z) ≤ ff V)
    (hc : c = g * (1 + ((F.card : ℚ) - 1) / z - ∑ V ∈ F, 1 / kf V))
    (htot : c + ∑ V ∈ F, ff V ≤ g - 1) : False := by
  have h1 : ∑ V ∈ F, (g / kf V - g / (2 * z)) ≤ ∑ V ∈ F, ff V := Finset.sum_le_sum hf
  have h2 : ∑ V ∈ F, (g / kf V - g / (2 * z))
      = g * (∑ V ∈ F, 1 / kf V) - (F.card : ℚ) * (g / (2 * z)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun V _ => by rw [mul_one_div]
  have key : g * (1 + ((F.card : ℚ) - 1) / z - ∑ V ∈ F, 1 / kf V)
      + (g * (∑ V ∈ F, 1 / kf V) - (F.card : ℚ) * (g / (2 * z)))
      = g + g * ((F.card : ℚ) - 2) / (2 * z) := by
    field_simp
    ring
  have hnn : 0 ≤ g * ((F.card : ℚ) - 2) / (2 * z) := by
    apply div_nonneg
    · nlinarith
    · positivity
  rw [h2] at h1
  rw [hc] at htot
  linarith

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_candidate_has_nontrivial_residual
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_candidate_family_common_factors.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : Statements.FTS_sigma_prime_separation.{u})
    (h₇ : Statements.FTS_signalizer_unique_supporting_maximum.{u})
    (h₈ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_candidate_has_nontrivial_residual.{u} := by
  classical
  intro G _ _ M K A Z I KT hs
  have hamb : Prep03.IsAmbient G := hs.base.ambient
  have hmin08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.odd_natCard, hamb.forall_isSolvable⟩
  obtain ⟨-, hn2, hmain, -⟩ := h₂ G M K A Z I hs.base hs.I_eq
  obtain ⟨hknonempty, hb, -⟩ := hmain KT hs.KT_self hs.KT_hall
  have hcoatom : ∀ V ∈ I, IsCoatom V := by
    intro V hV
    rw [hs.I_eq] at hV
    rcases hV with h | h
    · rw [h]; exact hs.base.isCoatom
    · exact h.1
  have hhall : ∀ V ∈ I, IsHallPiOf (kappaPrimes V) (KT V) V := by
    intro V hV
    by_cases hVM : V = M
    · subst hVM; rw [hs.KT_self]; exact hs.base.isHall_K
    · exact (hs.KT_hall V hV hVM).1
  obtain ⟨hcard, -, -, hdisjTD, hdisjDD, h1TG, h1D⟩ :=
    FNI_kappa_candidate_mixed_support_cardinality h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ G M K A Z I KT hs
  by_contra hcon
  have hfac : ∀ V ∈ I, Nat.card ↥V = Nat.card ↥(sigmaCore V) * Nat.card ↥(KT V) := by
    intro V hV
    obtain ⟨-, U, E₁, -, -, hsd1, hsd2, -⟩ :=
      h₄ G hamb V (KT V) (hcoatom V hV) (hknonempty V hV) (hhall V hV)
    have hU : U = ⊥ := by
      by_contra hUb
      exact hcon ⟨V, hV, U, hUb, hsd1, hsd2⟩
    subst hU
    rw [bot_sup_eq] at hsd1
    exact natCard_of_isSemidirect hsd1
  have hpk : ∀ V ∈ I, (sigmaDelta V).ncard = (Nat.card ↥(sigmaCore V) - 1) * V.index := by
    intro V hV
    rw [sigmaDelta_eq_sigmaPacketSupport]
    exact (FTS_packet_cardinality h₁ h₅ h₆ G hmin08 V (hcoatom V hV)).1
  have hzpos : (0 : ℚ) < (Nat.card ↥Z : ℚ) := by exact_mod_cast Nat.card_pos (α := ↥Z)
  have hGpos : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos (α := G)
  have hbound : ∀ V ∈ I, (Nat.card G : ℚ) / (Nat.card ↥(KT V) : ℚ)
      - (Nat.card G : ℚ) / (2 * (Nat.card ↥Z : ℚ)) ≤ ((sigmaDelta V).ncard : ℚ) := by
    intro V hV
    have hZV : Z < V := (hb V hV).2.2.2.1
    have h2z : 2 * Nat.card ↥Z ≤ Nat.card ↥V := two_mul_natCard_le_natCard_of_lt hZV
    have hsk : Nat.card ↥V = Nat.card ↥(sigmaCore V) * Nat.card ↥(KT V) := hfac V hV
    have hidx : Nat.card ↥V * V.index = Nat.card G := Subgroup.card_mul_index V
    have hs1 : 1 ≤ Nat.card ↥(sigmaCore V) := Nat.card_pos
    have hkpos : (0 : ℚ) < (Nat.card ↥(KT V) : ℚ) := by
      exact_mod_cast Nat.card_pos (α := ↥(KT V))
    have hidxpos : (0 : ℚ) ≤ (V.index : ℚ) := by positivity
    have hGeq : (Nat.card G : ℚ)
        = (Nat.card ↥(sigmaCore V) : ℚ) * (Nat.card ↥(KT V) : ℚ) * (V.index : ℚ) := by
      rw [← hidx, hsk]; push_cast; ring
    have hGk : (Nat.card G : ℚ) / (Nat.card ↥(KT V) : ℚ)
        = (Nat.card ↥(sigmaCore V) : ℚ) * (V.index : ℚ) := by
      rw [hGeq]; field_simp
    have hidxle : (V.index : ℚ) ≤ (Nat.card G : ℚ) / (2 * (Nat.card ↥Z : ℚ)) := by
      rw [le_div_iff₀ (by linarith)]
      have h2zQ : (2 : ℚ) * (Nat.card ↥Z : ℚ) ≤ (Nat.card ↥V : ℚ) := by exact_mod_cast h2z
      have hmul : (V.index : ℚ) * (Nat.card ↥V : ℚ) = (Nat.card G : ℚ) := by
        rw [← hidx]; push_cast; ring
      nlinarith [hidxpos]
    rw [hpk V hV]
    have hcast : (((Nat.card ↥(sigmaCore V) - 1) * V.index : ℕ) : ℚ)
        = ((Nat.card ↥(sigmaCore V) : ℚ) - 1) * (V.index : ℚ) := by
      push_cast [Nat.cast_sub hs1]
      ring
    rw [hcast, hGk]
    have hexp : ((Nat.card ↥(sigmaCore V) : ℚ) - 1) * (V.index : ℚ)
        = (Nat.card ↥(sigmaCore V) : ℚ) * (V.index : ℚ) - (V.index : ℚ) := by ring
    rw [hexp]
    linarith
  have hI : I.Finite := Set.toFinite I
  have hpd : I.PairwiseDisjoint sigmaDelta := fun V hV V' hV' hne => hdisjDD V hV V' hV' hne
  have hDunion : (⋃ V ∈ I, sigmaDelta V).ncard = ∑ᶠ V ∈ I, (sigmaDelta V).ncard :=
    hI.ncard_biUnion (fun i _ => Set.toFinite _) hpd
  have hdisjTot : Disjoint (Prep03.sat (mixedTorusSet Z I KT)) (⋃ V ∈ I, sigmaDelta V) := by
    rw [Set.disjoint_iUnion₂_right]
    intro V hV
    exact hdisjTD V hV
  have hsub : (Prep03.sat (mixedTorusSet Z I KT)) ∪ (⋃ V ∈ I, sigmaDelta V) ⊆ ({1} : Set G)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    rcases hx with hx | hx
    · exact h1TG hx
    · obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.1 hx
      exact h1D V hV hxV
  have hcompl : (({1} : Set G)ᶜ).ncard = Nat.card G - 1 := by
    have h := Set.ncard_add_ncard_compl ({1} : Set G)
    rw [Set.ncard_singleton] at h
    omega
  have hle : (Prep03.sat (mixedTorusSet Z I KT)).ncard + (⋃ V ∈ I, sigmaDelta V).ncard
      ≤ Nat.card G - 1 := by
    rw [← Set.ncard_union_eq hdisjTot (Set.toFinite _) (Set.toFinite _), ← hcompl]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hFcard : (hI.toFinset.card : ℚ) = (I.ncard : ℚ) := by
    rw [Set.ncard_eq_toFinset_card _ hI]
  refine residual_measure_contradiction (F := hI.toFinset)
    (kf := fun V => (Nat.card ↥(KT V) : ℚ)) (ff := fun V => ((sigmaDelta V).ncard : ℚ))
    (g := (Nat.card G : ℚ)) (z := (Nat.card ↥Z : ℚ))
    (c := ((Prep03.sat (mixedTorusSet Z I KT)).ncard : ℚ)) hGpos hzpos ?_ ?_ ?_ ?_
  · rw [hFcard]; exact_mod_cast hn2
  · intro V hV; exact hbound V (hI.mem_toFinset.1 hV)
  · rw [hFcard, hcard, finsum_mem_eq_finite_toFinset_sum _ hI]
  · have hsum : ∑ V ∈ hI.toFinset, ((sigmaDelta V).ncard : ℚ)
        = ((⋃ V ∈ I, sigmaDelta V).ncard : ℚ) := by
      rw [hDunion, finsum_mem_eq_finite_toFinset_sum _ hI]
      push_cast
      rfl
    rw [hsum]
    have hN1 : 1 ≤ Nat.card G := Nat.card_pos
    have hnat : (Prep03.sat (mixedTorusSet Z I KT)).ncard + (⋃ V ∈ I, sigmaDelta V).ncard + 1
        ≤ Nat.card G := by omega
    have hQ := (Nat.cast_le (α := ℚ)).2 hnat
    push_cast at hQ
    linarith

end

end CFSG.FeitThompson.Proofs
