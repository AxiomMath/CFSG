module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalLift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic

variable {G : Type} [Group G] [Finite G] {A T : Subgroup G} {g : G}

omit [Finite G] in
theorem eq_one_of_mem_rightConjugate (hZ : Odd (Nat.card (center A))) {t : G}
    (htA : t ∈ rightConjugate A g) (htK : t ∈ rightConjugate (centralizer (A : Set G)) g)
    (ht2 : t ^ 2 = 1) : t = 1 := by
  rw [mem_rightConjugate_iff] at htA htK
  have hZ' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have h2 : (g * t * g⁻¹) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * t ^ 2 * g⁻¹ by rw [sq]; group, ht2,
      mul_one, mul_inv_cancel]
  have h1 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZ' (mem_inf.2 ⟨htA, htK⟩)) h2
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [h1, mul_one, inv_mul_cancel]

variable {W : Type*} [Group W] {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}

theorem leviLift_le_rightConjugate (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hA : Hyp31 A) (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    {t : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hψ : IsActionHom A X ψ) (htN : t ∈ normalizer (A : Set G)) {P : Subgroup W} (hPX : P ≤ X)
    (hP : ⁅P, P⁆ = P) (htP : ∀ s ∈ P, ψ ⟨t, htN⟩ * s = s * ψ ⟨t, htN⟩) :
    leviLift ψ P ≤ rightConjugate A g := by
  have hLC : leviLift ψ P ≤ A ⊓ centralizer ({t} : Set G) :=
    le_inf leviLift_le (leviLift_le_centralizer hψ htN htP)
  have hperf := commutator_leviLift hψ hPX hP
  have h1 : leviLift ψ P ≤ admResidual (oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
      ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆) := by
    refine RankTwoClassical.le_admResidual_of_perfect ?_ hperf
    calc leviLift ψ P = ⁅leviLift ψ P, leviLift ψ P⁆ := hperf.symm
      _ ≤ ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆ :=
        commutator_mono hLC hLC
      _ ≤ _ := le_sup_right
  exact h1.trans (Lemma39.lemma39_one h4 h32 h34 hA hT ht ht1 hOut).1

theorem psi_commute_of_perfect (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hA : Hyp31 A) (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    {t : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hψ : IsActionHom A X ψ) (htN : t ∈ normalizer (A : Set G)) {P : Subgroup W} (hPX : P ≤ X)
    (hP : ⁅P, P⁆ = P) (htP : ∀ s ∈ P, ψ ⟨t, htN⟩ * s = s * ψ ⟨t, htN⟩) {u : G} (hu : u ∈ T)
    (huN : u ∈ normalizer (A : Set G)) {s : W} (hs : s ∈ P) :
    ψ ⟨u, huN⟩ * s = s * ψ ⟨u, huN⟩ := by
  obtain ⟨l, hl, rfl⟩ := exists_mem_leviLift hψ hPX hP hs
  have hlg := leviLift_le_rightConjugate h4 h32 h34 hA hT ht ht1 hOut hψ htN hPX hP htP hl
  have hlT : u * l = l * u :=
    mem_centralizer_iff.mp ((Lemma39.lemma39_one h4 h32 h34 hA hT ht ht1 hOut).2 hlg) u hu
  have hlN := le_normalizer (leviLift_le hl)
  have h := congrArg ψ (Subtype.ext hlT :
    (⟨u * l, mul_mem huN hlN⟩ : normalizer (A : Set G)) = ⟨l * u, mul_mem hlN huN⟩)
  rwa [psi_mul huN hlN, psi_mul hlN huN] at h

theorem eq_one_of_psi_mem_perfect (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hA : Hyp31 A) (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZ : Odd (Nat.card (center A))) (hψ : IsActionHom A X ψ) {t : G} (ht : t ∈ T)
    (htA : t ∈ A) {P : Subgroup W} (hPX : P ≤ X) (hP : ⁅P, P⁆ = P)
    (htP : ∀ s ∈ P, ψ ⟨t, le_normalizer htA⟩ * s = s * ψ ⟨t, le_normalizer htA⟩)
    (htP' : ψ ⟨t, le_normalizer htA⟩ ∈ P) : t = 1 := by
  by_contra ht1
  have hTe := isElemAbelian_of_isSylowOf_rightConjugate h32 hA hT
  have ht2 : t ^ 2 = 1 := hTe.2 t ht
  have hZ' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have htS : t ∈ liftIn ψ P := mem_liftIn.2 ⟨htA, htP'⟩
  have htL : t ∈ leviLift ψ P :=
    mem_leviLift_of_pow hψ hPX hP hZ' htS (k := 1) (by rw [pow_one]; exact ht2)
  have htg := leviLift_le_rightConjugate h4 h32 h34 hA hT ht ht1 hOut hψ
    (le_normalizer htA) hPX hP htP htL
  exact ht1 (eq_one_of_mem_rightConjugate hZ htg (hT.le ht) ht2)

end CFSG.ComponentClassification.RankTwoExceptional
