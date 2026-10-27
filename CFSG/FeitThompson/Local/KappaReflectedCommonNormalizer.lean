module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaNormalizerReflection
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.KappaHallThirdFactorSupportedComplement
import CFSG.FeitThompson.Local.KappaDerivedComplement
import CFSG.FeitThompson.Local.FrattiniCommutingProductPrimePower
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.NormalBetaSylowControlsFittingPrimes
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence

namespace CFSG.FeitThompson.Prep03

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {X Y W : Subgroup G}

theorem IsDirect.commute (h : IsDirect X Y W) {a b : G} (ha : a ∈ Y) (hb : b ∈ W) :
    Commute a b :=
  ((mem_centralizer_iff).1 (commutator_eq_bot_iff_le_centralizer.1 h.2.2.2.2 ha) b hb).symm

theorem IsDirect.natCard_sup (h : IsDirect X Y W) :
    Nat.card ↥(Y ⊔ W) = Nat.card ↥Y * Nat.card ↥W := by
  have h' := natCard_sup_mul_natCard_inf_of_commute
    (U := Y) (V := W) fun a ha b hb => h.commute ha hb
  rw [h.2.2.2.1] at h'
  simpa using h'

theorem IsDirect.relIndex_right (h : IsDirect X Y W) [Finite G] :
    W.relIndex (Y ⊔ W) = Nat.card ↥Y :=
  Nat.eq_of_mul_eq_mul_left Nat.card_pos
    ((natCard_mul_relIndex_of_le le_sup_right).trans (h.natCard_sup.trans (mul_comm _ _)))

theorem IsDirect.le_normalizer_right (h : IsDirect X Y W) :
    Y ⊔ W ≤ Subgroup.normalizer (W : Set G) :=
  sup_le ((commutator_eq_bot_iff_le_centralizer.1 h.2.2.2.2).trans
    (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer

end

end CFSG.FeitThompson.Prep03

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_reflected_common_normalizer
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₆ : Statements.FTS_sigma_prime_separation.{u})
    (h₇ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_reflected_common_normalizer.{u} := by
  intro G _ _ M K A Z hsetup X T L B hXK hXp hT hNXT hL hAL hBeq
  have hamb := hsetup.ambient
  have hM := hsetup.isCoatom
  have hsimple := hamb.isSimpleGroup
  have hna := hamb.not_isMulCommutative
  have hrefl := FNI_kappa_normalizer_reflection h₁ h₂ h₃ h₄ h₅ h₆ h₇
  obtain ⟨-, -, hκT, -, hZN⟩ := hrefl G M K A Z hsetup X T hXK hXp hT hNXT
  obtain ⟨hdirM, -, hprimeM⟩ := h₃ G M K A Z hsetup
  obtain ⟨-, hNeqM, hXS⟩ := hprimeM X hXK hXp
  have hXT : X ≤ sigmaCore T := hXS T hT hNXT
  have hZM : Z = Subgroup.normalizer (X : Set G) ⊓ M := by
    rw [hNeqM, hsetup.Z_eq, hdirM.2.2.1]
  have hsetupT : IsKappaSetup G T L B (L ⊔ B) :=
    { ambient := hamb, isCoatom := hT, kappa_nonempty := hκT, isHall_K := hL,
      A_eq := hBeq, Z_eq := rfl }
  obtain ⟨hdirT, -, hprimeT⟩ := h₃ G T L B (L ⊔ B) hsetupT
  have hZTeq : L ⊔ B = Subgroup.normalizer (L : Set G) ⊓ T := hdirT.2.2.1
  obtain ⟨hAbot, hcentA, -⟩ :=
    FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₄ h₇ G M K A Z hsetup
  obtain ⟨q₀, hq₀, hq₀A⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥A)
    (fun h => hAbot (Subgroup.card_eq_one.1 h))
  obtain ⟨y, hyA, hyord⟩ := exists_mem_orderOf_eq_of_dvd hq₀ hq₀A
  have hYA : zpowers y ≤ A := zpowers_le.2 hyA
  have hYcard : Nat.card ↥(zpowers y) = q₀ := by rw [Nat.card_zpowers, hyord]
  have hYp : (Nat.card ↥(zpowers y)).Prime := hYcard ▸ hq₀
  have hYL : zpowers y ≤ L := hYA.trans hAL
  have hZle : Z ≤ L ⊔ B := by
    have h := hZN (zpowers y) hYA hYp
    rw [(hprimeT (zpowers y) hYL hYp).2.1, ← hZTeq] at h
    exact h
  have hBS : B ≤ sigmaCore T := by rw [hBeq]; exact inf_le_left
  have hBhall : IsHallPiOf (sigmaPrimes T) B (L ⊔ B) := by
    refine ⟨le_sup_right, fun r hr => ?_, fun r hr => ?_⟩
    · exact isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) r
        (Nat.mem_primeFactors.2 ⟨Nat.prime_of_mem_primeFactors hr,
          (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hBS),
          Nat.card_pos.ne'⟩)
    · rw [hdirT.relIndex_right] at hr
      exact notMem_sigmaPrimes_of_mem_kappaPrimes (hL.2.1 r hr)
  have hXB : X ≤ B := by
    refine le_of_isHallPiOf_of_le_normalizer hBhall hdirT.le_normalizer_right
      (hXK.trans (le_sup_left.trans (hsetup.Z_eq ▸ hZle))) fun r hr => ?_
    have hrX : r = Nat.card ↥X := by
      rw [hXp.primeFactors, Finset.mem_singleton] at hr; exact hr
    subst hrX
    exact isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore T) _
      (Nat.mem_primeFactors.2 ⟨hXp, Subgroup.card_dvd_of_le hXT, Nat.card_pos.ne'⟩)
  have hNYM : Subgroup.normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := by
    obtain ⟨T', hT', hle⟩ :=
      exists_isCoatom_ge_of_ne_top (normalizer_ne_top_of_natCard_eq_prime hna hq₀ hYcard)
    have hT'M : T' = M := (hcentA q₀ (zpowers y) hq₀ hYA hYcard).2 T' hT'
      ((Subgroup.centralizer_le_normalizer _).trans hle)
    exact hT'M ▸ hle
  obtain ⟨-, -, -, -, hZTN⟩ := hrefl G T L B (L ⊔ B) hsetupT (zpowers y) M hYL hYp hM hNYM
  have hZTle : L ⊔ B ≤ Z := by
    have h := hZTN X hXB hXp
    rw [← hZM] at h
    exact h
  have hZeq : Z = Subgroup.normalizer (L : Set G) ⊓ T := by
    rw [← hZTeq]; exact le_antisymm hZle hZTle
  exact ⟨hZeq ▸ hZTeq ▸ hdirT, hZeq⟩

end

end CFSG.FeitThompson.Proofs
