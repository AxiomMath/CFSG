module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveOrbit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem exists_sylow_normalizer {K T : Subgroup G} (hTK : T ≤ K) (hT2 : IsPGroup 2 T) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ T ≤ S ∧
      IsSylowOf 2 (S ⊓ Subgroup.normalizer (T : Set G)) (K ⊓ Subgroup.normalizer (T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hTR⟩ :=
    AschbacherTheorem3.exists_isSylowOf_le hT2 (le_inf hTK Subgroup.le_normalizer)
  obtain ⟨S, hS, hRS⟩ :=
    AschbacherTheorem3.exists_isSylowOf_le hR.isPGroup (hR.le.trans inf_le_left)
  refine ⟨S, hS, hTR.trans hRS, ?_⟩
  have heq : S ⊓ Subgroup.normalizer (T : Set G) = R :=
    hR.eq_of_le (le_inf hRS (hR.le.trans inf_le_right)) (inf_le_inf_right _ hS.le)
      hS.isPGroup.to_inf_left
  rw [heq]
  exact hR

theorem part_one_of_isSylowOf (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G)) {T S : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (hS : IsSylowOf 2 S (Q ⊔ T)) (hTS : T ≤ S) (hT1 : T ≠ ⊥) :
    T ⊓ Q = ⊥ ∧
      Nat.card (S ⊓ Subgroup.normalizer (T : Set G) ⊓ Q : Subgroup G) = Nat.card T ∧
      Nat.card (S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) = Nat.card T * Nat.card T := by
  obtain ⟨T', rfl⟩ := hT
  obtain ⟨S', rfl⟩ := hS
  obtain ⟨-, hbot, -, -, factor, square, -, -⟩ :=
    theorem_2_part_one Q htight g hg T' S' hTS hT1
  refine ⟨hbot, ?_, ?_⟩
  · have h1 := (Nat.card_congr factor.toEquiv).symm
    rw [relativeNormalizer] at h1
    rw [inf_comm (Subgroup.map _ _) (Subgroup.normalizer _)]
    exact h1
  · have h1 := (Nat.card_congr square.toEquiv).symm
    rw [Nat.card_prod, relativeNormalizer] at h1
    rw [inf_comm (Subgroup.map _ _) (Subgroup.normalizer _)]
    exact h1

theorem exists_thm3_of_overlap (hC : Counterexample G D r Abar)
    (h3 : AschbacherTheorem3.Theorem3Statement) {Q : Subgroup G} {k j : Fin r}
    (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q) (hQj : Q ≤ centralizing D (Abar j))
    (hHQ : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G)) {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (D : Set G))) (hT1 : T ≠ ⊥) :
    ∃ S : Subgroup G, IsSylowOf 2 S (Q ⊔ T) ∧ T ≤ S ∧ T ⊓ Q = ⊥ ∧
      Nat.card (S ⊓ Subgroup.normalizer (T : Set G) ⊓ Q : Subgroup G) = Nat.card T ∧
      S ⊓ Subgroup.normalizer (T : Set G) ⊓ Q ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g ∧
      AschbacherTheorem3.Thm3Conclusion (bar D Q) (bar D T) (bar D S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hN, htight⟩ := tightlyEmbedded_of_le_centralizing hC hkQ hQj hHQ
  have hQD : Q ≤ D := hQj.trans (centralizing_le _)
  have hQH : Q ≤ Subgroup.normalizer (D : Set G) := hQD.trans Subgroup.le_normalizer
  have hTH : T ≤ Subgroup.normalizer (D : Set G) := hT.le.trans inf_le_right
  have hTQg : T ≤ rightConjugate Q g := hT.le.trans inf_le_left
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hKH : Q ⊔ T ≤ Subgroup.normalizer (D : Set G) := sup_le hQH hTH
  obtain ⟨S, hS, hTS, hSN⟩ := exists_sylow_normalizer (le_sup_right : T ≤ Q ⊔ T) hT2
  have hg' : g ∉ Subgroup.normalizer (Q : Set G) := hN ▸ hg
  have hTQ' : IsSylowOf 2 T (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) := hN ▸ hT
  obtain ⟨hbot, hcardNQ, hcardN⟩ := part_one_of_isSylowOf Q htight g hg' hTQ' hS hTS hT1
  have hTSN : T ≤ S ⊓ Subgroup.normalizer (T : Set G) := le_inf hTS Subgroup.le_normalizer
  have hidx : T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card T (S ⊓ Subgroup.normalizer (T : Set G))
    rw [inf_eq_left.mpr hTSN, hcardN] at h1
    rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos h1]
  set P := rightConjugate Q g ⊓ (Q ⊔ T) with hP
  have hTP : IsSylowOf 2 T P :=
    hT.of_le (le_inf hTQg le_sup_right) (inf_le_inf_left _ hKH)
  have heven : Even (Nat.card P) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hT2)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    have h2T : 2 ∣ Nat.card T := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2T.trans (Subgroup.card_dvd_of_le hTP.le))
  have htightP : ∀ y ∈ Q ⊔ T, y ∉ Subgroup.normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)) := by
    intro y hy hyN
    have hQgt := rightConjugate_tightlyEmbedded Q htight g
    have hyQg : y ∉ Subgroup.normalizer (rightConjugate Q g : Set G) := by
      intro hyn
      apply hyN
      rw [← rightConjugate_eq_self_iff] at hyn ⊢
      rw [hP, AschbacherTheorem3.rightConjugate_inf, hyn,
        (rightConjugate_eq_self_iff _ y).mpr (Subgroup.le_normalizer hy)]
    exact (hQgt.2 y hyQg).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left)))
  have hOQ : aschbacherThm5Core D ≤ Q := (core_le_preimage D (Abar k)).trans hkQ
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer.trans hHQ
  have hconc := thm3_bar h3 hQD hOQ hDQ hTH (hTH.trans hHQ) hT2 hT1 hbot (inf_le_right : P ≤ _)
    hTP heven htightP hS hTS hSN hidx
  refine ⟨S, hS, hTS, hbot, hcardNQ, ?_, hconc⟩
  have hNT : Subgroup.normalizer (T : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g := by
    have h := normalizer_two_subgroup_le (rightConjugate Q g) T
      (rightConjugate_tightlyEmbedded Q htight g) hT2 hTQg hT1
    rwa [← AschbacherTheorem3.rightConjugate_normalizer, hN] at h
  exact inf_le_left.trans (inf_le_right.trans hNT)

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
