module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaNormalizerReflection
import CFSG.FeitThompson.Local.KappaReflectedCommonNormalizer
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.KappaHallThirdFactorSupportedComplement
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.NormalBetaSylowControlsFittingPrimes
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.Local.KappaGlobalPairExhaustion

namespace CFSG.FeitThompson.Prep03

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {X Y W : Subgroup G}

theorem IsDirect.symm (h : IsDirect X Y W) : IsDirect X W Y := by
  refine ⟨h.2.1, h.1, ?_, ?_, ?_⟩
  · rw [sup_comm]; exact h.2.2.1
  · rw [inf_comm]; exact h.2.2.2.1
  · rw [Subgroup.commutator_comm]; exact h.2.2.2.2

theorem IsDirect.relIndex_left [Finite G] (h : IsDirect X Y W) :
    Y.relIndex (Y ⊔ W) = Nat.card ↥W := by
  have h' := h.symm.relIndex_right
  rwa [sup_comm] at h'

theorem IsDirect.le_normalizer_left (h : IsDirect X Y W) :
    Y ⊔ W ≤ Subgroup.normalizer (Y : Set G) := by
  have h' := h.symm.le_normalizer_right
  rwa [sup_comm] at h'

end

end CFSG.FeitThompson.Prep03

namespace CFSG.FeitThompson

public section

open Subgroup CFSG.FeitThompson.Prep03

variable {G : Type*} [Group G]

theorem isHallPiOf_of_isDirect [Finite G] {T L B Z : Subgroup G}
    (hdir : IsDirect Z L B) (hL : ∀ r ∈ (Nat.card ↥L).primeFactors, r ∈ kappaPrimes T)
    (hB : B ≤ sigmaCore T) :
    IsHallPiOf (sigmaPrimes T)ᶜ L Z ∧ Z ≤ Subgroup.normalizer (L : Set G) ∧
      IsHallPiOf (sigmaPrimes T) B Z ∧ Z ≤ Subgroup.normalizer (B : Set G) := by
  have hBσ : ∀ r ∈ (Nat.card ↥B).primeFactors, r ∈ sigmaPrimes T := fun r hr =>
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) r
      (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hr,
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hB), Nat.card_pos.ne'⟩)
  have hsup : L ⊔ B = Z := hdir.2.2.1
  refine ⟨⟨hdir.1, fun r hr => notMem_sigmaPrimes_of_mem_kappaPrimes (hL r hr), fun r hr => ?_⟩,
    ?_, ⟨hdir.2.1, hBσ, fun r hr => ?_⟩, ?_⟩
  · rw [← hsup, hdir.relIndex_left] at hr
    exact not_not.2 (hBσ r hr)
  · rw [← hsup]; exact hdir.le_normalizer_left
  · rw [← hsup, hdir.relIndex_right] at hr
    exact notMem_sigmaPrimes_of_mem_kappaPrimes (hL r hr)
  · rw [← hsup]; exact hdir.le_normalizer_right

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_candidate_family_common_factors
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₆ : Statements.FTS_sigma_prime_separation.{u})
    (h₇ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_candidate_family_common_factors.{u} := by
  classical
  intro G _ _ M K A Z I hsetup hI
  have hamb := hsetup.ambient
  have hM := hsetup.isCoatom
  have hsimple := hamb.isSimpleGroup
  have hna := hamb.not_isMulCommutative
  have hrefl := FNI_kappa_normalizer_reflection h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hcomm := FNI_kappa_reflected_common_normalizer h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hfixed := FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₄ h₇
  obtain ⟨hdirM, -, hprimeM⟩ := h₃ G M K A Z hsetup
  have hmemI : ∀ T ∈ I, T = M ∨ (IsCoatom T ∧ ∃ X : Subgroup G, X ≤ K ∧ (Nat.card ↥X).Prime ∧
      Subgroup.normalizer (X : Set G) ≤ T) := by
    intro T hT
    rw [hI] at hT
    exact hT
  have hMI : M ∈ I := by rw [hI]; exact Or.inl rfl
  have hIcoatom : ∀ T ∈ I, IsCoatom T := by
    intro T hT
    rcases hmemI T hT with h | ⟨hTc, -⟩
    · exact h ▸ hM
    · exact hTc
  have hlast : ∀ X : Subgroup G, X ≤ K → (Nat.card ↥X).Prime →
      ∃ T ∈ I, T ≠ M ∧ Subgroup.normalizer (X : Set G) ≤ T ∧ X ≤ sigmaCore T := by
    intro X hXK hXp
    obtain ⟨T, hT, hle⟩ := exists_isCoatom_ge_of_ne_top
      (normalizer_ne_top_of_natCard_eq_prime hna hXp rfl)
    have hTI : T ∈ I := by rw [hI]; exact Or.inr ⟨hT, X, hXK, hXp, hle⟩
    obtain ⟨hnc, -, -, -, -⟩ := hrefl G M K A Z hsetup X T hXK hXp hT hle
    have hTM : T ≠ M := fun h => hnc ⟨1, by rw [conjSub_one]; exact h⟩
    exact ⟨T, hTI, hTM, hle, ((hprimeM X hXK hXp).2.2 T hT hle)⟩
  have hKbot : K ≠ ⊥ :=
    (h₄ G hamb M K hM hsetup.kappa_nonempty hsetup.isHall_K).1
  obtain ⟨q₀, hq₀, hq₀K⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
    (fun h => hKbot (Subgroup.card_eq_one.1 h))
  obtain ⟨x₀, hx₀, hx₀ord⟩ := exists_mem_orderOf_eq_of_dvd hq₀ hq₀K
  have hX₀K : zpowers x₀ ≤ K := zpowers_le.2 hx₀
  have hX₀card : Nat.card ↥(zpowers x₀) = q₀ := by rw [Nat.card_zpowers, hx₀ord]
  obtain ⟨T₀, hT₀I, hT₀M, -, -⟩ := hlast (zpowers x₀) hX₀K (hX₀card ▸ hq₀)
  have hZle : ∀ T ∈ I, Z ≤ T := by
    intro T hT
    rcases hmemI T hT with h | ⟨hTc, X, hXK, hXp, hNX⟩
    · subst h
      rw [hsetup.Z_eq]
      refine sup_le hsetup.isHall_K.1 ?_
      rw [hsetup.A_eq]
      exact le_trans inf_le_left (sigmaCore_le T)
    · exact (hrefl G M K A Z hsetup X T hXK hXp hTc hNX).2.1
  have hZlt : ∀ T ∈ I, Z < T := by
    intro T hT
    refine lt_of_le_of_ne (hZle T hT) ?_
    intro hZT
    have hTT₀ : T ≤ T₀ := by rw [← hZT]; exact hZle T₀ hT₀I
    have hTM : T ≤ M := by rw [← hZT]; exact hZle M hMI
    by_cases hc : T = M
    · exact hT₀M (((hIcoatom T hT).le_iff_eq (hIcoatom T₀ hT₀I).ne_top).1 hTT₀ ▸ hc)
    · exact hc ((((hIcoatom T hT).le_iff_eq hM.ne_top).1 hTM).symm)
  have key : ∀ KT : Subgroup G → Subgroup G, KT M = K →
      (∀ T ∈ I, T ≠ M → IsHallPiOf (kappaPrimes T) (KT T) T ∧ A ≤ KT T) →
      ∀ T ∈ I, IsKappaSetup G T (KT T) (kappaA KT T) Z ∧
        IsDirect Z (KT T) (kappaA KT T) ∧
        Z = Subgroup.normalizer ((KT T : Subgroup G) : Set G) ⊓ T := by
    intro KT hKTM hKT T hTI
    by_cases hTM : T = M
    · rw [hTM]
      have hAM : kappaA KT M = A := by simp only [kappaA, hKTM, hsetup.A_eq]
      have hZN : Z = Subgroup.normalizer (K : Set G) ⊓ M := by
        rw [hsetup.Z_eq, hdirM.2.2.1]
      refine ⟨?_, ?_, ?_⟩
      · exact
          { ambient := hamb
            isCoatom := hM
            kappa_nonempty := hsetup.kappa_nonempty
            isHall_K := by rw [hKTM]; exact hsetup.isHall_K
            A_eq := by rw [hAM, hsetup.A_eq, hKTM]
            Z_eq := by rw [hKTM, hAM]; exact hsetup.Z_eq }
      · rw [hKTM, hAM, hZN]; exact hdirM
      · rw [hKTM]; exact hZN
    · obtain ⟨hTc, X, hXK, hXp, hNX⟩ := (hmemI T hTI).resolve_left hTM
      obtain ⟨hHall, hAL⟩ := hKT T hTI hTM
      obtain ⟨-, -, hκT, -, -⟩ := hrefl G M K A Z hsetup X T hXK hXp hTc hNX
      obtain ⟨hdir, hZeq⟩ := hcomm G M K A Z hsetup X T (KT T) (kappaA KT T)
        hXK hXp hTc hNX hHall hAL rfl
      refine ⟨?_, hdir, hZeq⟩
      exact
        { ambient := hamb
          isCoatom := hTc
          kappa_nonempty := hκT
          isHall_K := hHall
          A_eq := rfl
          Z_eq := hdir.2.2.1.symm }
  refine ⟨?_, ?_, ?_, hlast⟩
  ·
    refine ⟨fun T => if T = M then K else
      if h : ∃ L : Subgroup G, IsHallPiOf (kappaPrimes T) L T ∧ A ≤ L then h.choose else K,
      by simp, ?_⟩
    intro T hTI hTM
    obtain ⟨hTc, X, hXK, hXp, hNX⟩ := (hmemI T hTI).resolve_left hTM
    obtain ⟨-, -, -, hex, -⟩ := hrefl G M K A Z hsetup X T hXK hXp hTc hNX
    simp only [if_neg hTM, dif_pos hex]
    exact hex.choose_spec
  ·
    have h : (1 : ℕ) < I.ncard :=
      (Set.one_lt_ncard (Set.toFinite I)).2 ⟨M, hMI, T₀, hT₀I, fun h => hT₀M h.symm⟩
    omega
  · intro KT hKTM hKT
    refine ⟨fun T hT => ((key KT hKTM hKT T hT).1).kappa_nonempty, ?_, ?_⟩
    · intro T hT
      obtain ⟨hsetupT, hdir, hZeq⟩ := key KT hKTM hKT T hT
      have hAT : kappaA KT T ≤ sigmaCore T := inf_le_left
      obtain ⟨hh1, hh2, hh3, hh4⟩ := isHallPiOf_of_isDirect hdir hsetupT.isHall_K.2.1 hAT
      exact ⟨(hfixed G T (KT T) (kappaA KT T) Z hsetupT).1, hdir, hZeq, hZlt T hT,
        hh1, hh2, hh3, hh4⟩
    · intro T hT V hV hTV
      obtain ⟨hsetupT, hdirT, hZeqT⟩ := key KT hKTM hKT T hT
      obtain ⟨hsetupV, hdirV, hZeqV⟩ := key KT hKTM hKT V hV
      have hATS : kappaA KT T ≤ sigmaCore T := inf_le_left
      have hAVS : kappaA KT V ≤ sigmaCore V := inf_le_left
      obtain ⟨hhT1, hhT2, hhT3, hhT4⟩ :=
        isHallPiOf_of_isDirect hdirT hsetupT.isHall_K.2.1 hATS
      obtain ⟨hhV1, hhV2, hhV3, hhV4⟩ :=
        isHallPiOf_of_isDirect hdirV hsetupV.isHall_K.2.1 hAVS
      obtain ⟨hATbot, hcentT, -⟩ := hfixed G T (KT T) (kappaA KT T) Z hsetupT
      obtain ⟨hAVbot, hcentV, -⟩ := hfixed G V (KT V) (kappaA KT V) Z hsetupV
      have hinf : kappaA KT T ⊓ kappaA KT V = ⊥ := by
        by_contra hne
        obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd
          (n := Nat.card ↥(kappaA KT T ⊓ kappaA KT V)) (fun h => hne (Subgroup.card_eq_one.1 h))
        obtain ⟨y, hy, hyord⟩ := exists_mem_orderOf_eq_of_dvd hr hrdvd
        have hQ : zpowers y ≤ kappaA KT T ⊓ kappaA KT V := zpowers_le.2 hy
        have hQcard : Nat.card ↥(zpowers y) = r := by rw [Nat.card_zpowers, hyord]
        have h1 := (hcentV r (zpowers y) hr (hQ.trans inf_le_right) hQcard).1
        exact hTV ((hcentT r (zpowers y) hr (hQ.trans inf_le_left) hQcard).2 V
          (hIcoatom V hV) h1).symm
      have hout : ∀ r ∈ (Nat.card ↥(kappaA KT T)).primeFactors, r ∈ (sigmaPrimes V)ᶜ := by
        intro r hr hrσ
        obtain ⟨y, hy, hyord⟩ := exists_mem_orderOf_eq_of_dvd
          (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
        have hQ : zpowers y ≤ kappaA KT T := zpowers_le.2 hy
        have hQcard : Nat.card ↥(zpowers y) = r := by rw [Nat.card_zpowers, hyord]
        have hQπ : ∀ s ∈ (Nat.card ↥(zpowers y)).primeFactors, s ∈ sigmaPrimes V := by
          intro s hs
          rw [hQcard, (Nat.prime_of_mem_primeFactors hr).primeFactors,
            Finset.mem_singleton] at hs
          exact hs ▸ hrσ
        have hQV : zpowers y ≤ kappaA KT V :=
          le_of_isHallPiOf_of_le_normalizer hhV3 hhV4 (hQ.trans hdirT.2.1) hQπ
        have hbot : zpowers y ≤ ⊥ := hinf ▸ le_inf hQ hQV
        have hone : Nat.card ↥(zpowers y) = 1 := Subgroup.card_eq_one.2 (le_bot_iff.1 hbot)
        rw [hQcard] at hone
        exact (Nat.prime_of_mem_primeFactors hr).ne_one hone
      refine ⟨hinf, le_of_isHallPiOf_of_le_normalizer hhV1 hhV2 hdirT.2.1 hout, ?_⟩
      rintro ⟨g, hg⟩
      obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥(kappaA KT T))
        (fun h => hATbot (Subgroup.card_eq_one.1 h))
      have hrmem : r ∈ (Nat.card ↥(kappaA KT T)).primeFactors :=
        Nat.mem_primeFactors.2 ⟨hr, hrdvd, Nat.card_pos.ne'⟩
      have hrT : r ∈ sigmaPrimes T :=
        isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) r
          (Nat.mem_primeFactors.2 ⟨hr, hrdvd.trans (Subgroup.card_dvd_of_le hATS),
            Nat.card_pos.ne'⟩)
      exact hout r hrmem (by rw [← hg, sigmaPrimes_prep03_conjSub]; exact hrT)

end

end CFSG.FeitThompson.Proofs
