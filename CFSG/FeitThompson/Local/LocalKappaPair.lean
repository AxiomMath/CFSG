module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaCandidateCyclicTorus
import CFSG.FeitThompson.Local.MixedElementsKappaCandidateTorus
import CFSG.FeitThompson.Local.KappaCandidateMixedSetTi
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep03

universe u

variable {G : Type u} [Group G] [Finite G]

theorem mixedTorusSet_eq_sdiff_union {M Mstar K A Z : Subgroup G}
    {KT : Subgroup G → Subgroup G} (hAM : kappaA KT M = A) (hKS : kappaA KT Mstar = K) :
    mixedTorusSet Z {M, Mstar} KT = (Z : Set G) \ ((K : Set G) ∪ (A : Set G)) := by
  rw [mixedTorusSet, Set.biUnion_pair, hAM, hKS]
  ext x
  constructor
  · rintro ⟨⟨hxZ, hx1⟩, hx⟩
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, not_or, not_and,
      SetLike.mem_coe] at hx ⊢
    exact ⟨hxZ, fun hK => hx.2 hK (by simpa using hx1), fun hA => hx.1 hA (by simpa using hx1)⟩
  · rintro ⟨hxZ, hx⟩
    simp only [Set.mem_union, SetLike.mem_coe, not_or] at hx
    refine ⟨⟨hxZ, ?_⟩, ?_⟩
    · simp only [Set.mem_singleton_iff]
      exact fun h => hx.2 (h ▸ one_mem A)
    · simp only [Set.mem_union, Set.mem_sdiff, SetLike.mem_coe, not_or]
      exact ⟨fun h => hx.2 h.1, fun h => hx.1 h.1⟩

theorem FNI_kappa_local_pair
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_candidate_family_common_factors.{u})
    (h₃ : Statements.FNI_kappa_candidate_has_nontrivial_residual.{u})
    (h₄ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₅ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₆ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₇ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₈ : Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₉ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_local_pair.{u} := by
  intro G _ _ M K A Z hs
  obtain ⟨⟨KT, hKTM, hKThall⟩, hIcard, hfam, hprimefam⟩ :=
    h₂ G M K A Z (kappaFamily M K) hs rfl
  have hfs : IsKappaFamilySetup G M K A Z (kappaFamily M K) KT := ⟨hs, rfl, hKTM, hKThall⟩
  obtain ⟨hknone, hpack, hdist⟩ := hfam KT hKTM hKThall
  obtain ⟨hZcyc, -, -, ⟨Mstar, hIeq, hAeq, hKeq, hres⟩, -⟩ :=
    FNI_kappa_candidate_cyclic_torus h₁ h₂ h₃ h₅ h₆ h₇ h₈ G M K A Z (kappaFamily M K) KT hfs
  obtain ⟨-, -, hnorm⟩ := h₄ G M K A Z hs
  have hMI : M ∈ kappaFamily M K := Set.mem_union_left _ rfl
  have hMstarI : Mstar ∈ kappaFamily M K := by rw [hIeq]; exact Set.mem_insert_of_mem _ rfl
  have hMne : M ≠ Mstar := by
    intro h
    rw [hIeq, h, Set.pair_eq_singleton, Set.ncard_singleton] at hIcard
    omega
  have hAM : kappaA KT M = A := by rw [kappaA, hKTM, hs.A_eq]
  have hMpack := hpack M hMI
  have hSpack := hpack Mstar hMstarI
  obtain ⟨hMstarHall, -⟩ := hKThall Mstar hMstarI (Ne.symm hMne)
  have hMstarCoatom : IsCoatom Mstar := by
    rcases hMstarI with h | h
    · exact absurd (h.symm : M = Mstar) hMne
    · exact h.1
  have hwit : ∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
      Subgroup.normalizer (X : Set G) ≤ Mstar := by
    rcases hMstarI with h | h
    · exact absurd (h.symm : M = Mstar) hMne
    · exact h.2
  have huniq : ∀ T : Subgroup G, IsCoatom T →
      (∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
        Subgroup.normalizer (X : Set G) ≤ T) → T = Mstar := by
    intro T hT hex
    obtain ⟨X, hXK, hXp, hXT⟩ := hex
    have hTI : T ∈ kappaFamily M K := Set.mem_union_right _ ⟨hT, X, hXK, hXp, hXT⟩
    rw [hIeq] at hTI
    rcases hTI with h | h
    · have hXS : X ≤ sigmaCore T := (hnorm X hXK hXp).2.2 T hT hXT
      rw [h] at hXS
      exact absurd hXK (not_le_kappaHall_of_le_sigmaCore hs.isHall_K hXp hXS)
    · exact h
  have hAne : A ≠ ⊥ := hAM ▸ hMpack.1
  have hAhall : IsHallPiOf (kappaPrimes Mstar) A Mstar := hAeq ▸ hMstarHall
  have hcentA : cent (sigmaCore Mstar) (A : Set G) = K := by
    rw [hAeq]; rw [kappaA] at hKeq; exact hKeq
  have hsstar : IsKappaSetup G Mstar A K Z :=
    ⟨hs.ambient, hMstarCoatom, hknone Mstar hMstarI, hAhall, hcentA.symm, by
      rw [hs.Z_eq, sup_comm]⟩
  obtain ⟨-, hcentK, -⟩ :=
    FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₅ h₉ G Mstar A K Z hsstar
  obtain ⟨-, hcentAY, -⟩ :=
    FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₅ h₉ G M K A Z hs
  have hmix : mixedTorusSet Z (kappaFamily M K) KT
      = (Z : Set G) \ ((K : Set G) ∪ (A : Set G)) := by
    rw [hIeq]; exact mixedTorusSet_eq_sdiff_union hAM hKeq
  obtain ⟨-, hmixne, -⟩ :=
    FNI_kappa_candidate_mixed_set_description h₂ G M K A Z (kappaFamily M K) KT hfs
  obtain ⟨hmixnorm, hmixti⟩ :=
    FNI_kappa_candidate_mixed_set_ti h₁ h₂ h₄ h₅ h₉ G M K A Z (kappaFamily M K) KT hfs
  rw [hmix] at hmixne hmixnorm hmixti
  refine ⟨Mstar, ⟨hMstarCoatom, hwit⟩, huniq, (hdist M hMI Mstar hMstarI hMne).2.2,
    hAne, hAhall, hcentA, hKTM ▸ hAM ▸ hMpack.2.1, hZcyc,
    (hKTM ▸ hMpack.2.2.1).symm, (hAeq ▸ hSpack.2.2.1).symm, ?_, ?_,
    ⟨hmixne, hmixnorm, hmixti⟩, ?_⟩
  ·
    intro X hXK hXp
    obtain ⟨T, hTI, hTM, hTnorm, -⟩ := hprimefam X hXK hXp
    have hTstar : T = Mstar := by
      rw [hIeq] at hTI
      rcases hTI with h | h
      · exact absurd h hTM
      · exact h
    subst hTstar
    exact ⟨hTnorm, (hcentK (Nat.card ↥X) X hXp hXK rfl).1,
      fun T hT hXT => huniq T hT ⟨X, hXK, hXp, hXT⟩,
      (hcentK (Nat.card ↥X) X hXp hXK rfl).2⟩
  ·
    intro Y hYA hYp
    exact hcentAY (Nat.card ↥Y) Y hYp hYA rfl
  ·
    rcases hres with ⟨U, hU, h1, h2⟩ | ⟨V, hV, h1, h2⟩
    · exact Or.inl ⟨U, hU, h1, h2⟩
    · exact Or.inr ⟨V, hV, hAeq ▸ h1, hAeq ▸ h2⟩

end

end CFSG.FeitThompson.Proofs
