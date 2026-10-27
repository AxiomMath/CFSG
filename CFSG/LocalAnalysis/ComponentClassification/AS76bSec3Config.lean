module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec3
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExist
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

theorem mem_normalizer_rightConjugate_iff (Q : Subgroup G) (g x : G) :
    x ∈ normalizer (rightConjugate Q g : Set G) ↔ g * x * g⁻¹ ∈ normalizer (Q : Set G) := by
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_eq_self_iff, rightConjugate_mul]
  constructor
  · intro h
    rw [← rightConjugate_mul, h, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  · intro h
    rw [show g * x = g * x * g⁻¹ * g by group, ← rightConjugate_mul, h]

theorem isElemAbelian_rightConjugate {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) (g : G) :
    IsElemAbelian p (rightConjugate E g) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    rw [mem_rightConjugate_iff] at ha hb
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    simp only [coe_mul] at h ⊢
    have : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
        _ = g * (b * a) * g⁻¹ := by group
    simpa using this
  · rw [mem_rightConjugate_iff] at hx
    have h := hE.2 _ hx
    rw [conj_pow] at h
    simpa using h

theorem tightlyEmbedded_rightConjugate {K : Subgroup G} (hK : TightlyEmbedded K) (g : G) :
    TightlyEmbedded (rightConjugate K g) :=
  StandardSubgroupAPI.tightlyEmbedded_rightConjugate hK g

variable [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_le {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup G, IsSylowOf 2 S H ∧ P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype : IsPGroup 2 (P.subgroupOf H)).exists_le_sylow
  exact ⟨(Q : Subgroup H).map H.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPH hx⟩, hQ hx, rfl⟩⟩

omit [Finite G] in
theorem tightlyEmbedded_inf_subgroupOf_of_tightlyEmbedded {Q M : Subgroup G}
    (hQ : TightlyEmbedded Q) (heven : Even (Nat.card (Q ⊓ M : Subgroup G))) :
    TightlyEmbedded ((Q ⊓ M).subgroupOf M) :=
  StandardSubgroupAPI.tightlyEmbedded_inf_subgroupOf hQ heven

theorem sylowInTightTwoNilpotent_of_tightlyEmbedded {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hK : Even (Nat.card K)) (htight : TightlyEmbedded (oddCoreIn K ⊔ R)) (B : Subgroup G) :
    SylowInTightTwoNilpotent R B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRQ : R ≤ oddCoreIn K ⊔ R := le_sup_right
  have hQK : oddCoreIn K ⊔ R ≤ K := sup_le (oddCoreIn_le K) hR.le
  have hRX : R ≤ (oddCoreIn K ⊔ R) ⊓ (R ⊔ B) := le_inf hRQ le_sup_left
  refine ⟨(oddCoreIn K ⊔ R) ⊓ (R ⊔ B), inf_le_right, hR.of_le hRX (inf_le_left.trans hQK), ?_,
    tightlyEmbedded_inf_subgroupOf_of_tightlyEmbedded htight (even_iff_two_dvd.mpr
      ((two_dvd_card_of_isSylowOf hR hK).trans (card_dvd_of_le hRX)))⟩
  refine IsTwoNilpotent.mono ⟨oddCoreIn K, le_sup_left, ?_, odd_card_oddCoreIn K, ?_⟩ inf_le_left
  · exact (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (hQK.trans (le_normalizer_oddCoreIn K))
  · have hidx : (oddCoreIn K).relIndex (oddCoreIn K ⊔ R) = (oddCoreIn K).relIndex R :=
      AschbacherTheorem3.relIndex_sup_of_le_normalizer (hR.le.trans (le_normalizer_oddCoreIn K))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR.isPGroup
    have hdvd : (oddCoreIn K).relIndex (oddCoreIn K ⊔ R) ∣ 2 ^ m := by
      rw [hidx, ← hm]
      exact relIndex_dvd_card _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩

theorem not_normal_rightConjugate_centralizer {A : Subgroup G} (hA : Hyp31 A) (g : G) :
    ¬ (rightConjugate (centralizer (A : Set G)) g).Normal := by
  intro h
  apply hA.not_normal
  rw [← normalizer_eq_top_iff, ← normalizer_centralizer_eq hA.standard, eq_top_iff]
  intro y _
  have hy : g⁻¹ * y * g ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) := by
    rw [normalizer_eq_top_iff.mpr h]
    exact mem_top _
  rw [mem_normalizer_rightConjugate_iff] at hy
  simpa [mul_assoc] using hy

theorem isElemAbelian_of_isSylowOf_rightConjugate (h32 : Lemma32) {A : Subgroup G}
    (hA : Hyp31 A) {g : G} {T : Subgroup G}
    (hTK : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) : IsElemAbelian 2 T := by
  have hT' : IsSylowOf 2 (rightConjugate T g⁻¹) (centralizer (A : Set G)) := by
    have := AschbacherTheorem3.isSylowOf_rightConjugate hTK g⁻¹
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
  have h := isElemAbelian_rightConjugate (h32 G A hA _ hT') g
  rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h

theorem sylowInTightTwoNilpotent_of_hyp31 (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) {A : Subgroup G} (hA : Hyp31 A) {g : G} {T : Subgroup G}
    (hTK : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) (B : Subgroup G) :
    SylowInTightTwoNilpotent T B := by
  have htight := tightlyEmbedded_rightConjugate (tightlyEmbedded_centralizer hA.standard) g
  exact sylowInTightTwoNilpotent_of_tightlyEmbedded hTK htight.1
    (lemma21 h4 htight hTK (isElemAbelian_of_isSylowOf_rightConjugate h32 hA hTK)
      (h34 G A hA).2 (not_normal_rightConjugate_centralizer hA g)).1 B

theorem section3Config_of (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) : Section3Config := by
  intro G _ _ A hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htight := tightlyEmbedded_centralizer hA.standard
  have hNK := normalizer_centralizer_eq hA.standard
  obtain ⟨g, hg, T, hTN, hTK⟩ := h33 G A hA
  have hTNA : T ≤ normalizer (A : Set G) := hTN.le.trans inf_le_right
  have hTKN : T ≤ normalizer (centralizer (A : Set G) : Set G) := by rw [hNK]; exact hTNA
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_le (le_sup_right : T ≤ centralizer (A : Set G) ⊔ T)
    hTK.isPGroup
  have hR : IsSylowOf 2 (S ⊓ centralizer (A : Set G)) (centralizer (A : Set G)) :=
    hS.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTKN)
  have hTR : T ≤ normalizer ((S ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
    intro t ht
    have h1 := mem_normalizer_iff.mp (le_normalizer (hTS ht) : t ∈ normalizer (S : Set G))
    have h2 := mem_normalizer_iff.mp (hTKN ht)
    rw [mem_normalizer_iff]
    intro x
    rw [mem_inf, mem_inf, h1 x, h2 x]
  set R := S ⊓ centralizer (A : Set G) with hRdef
  have hKgeven : Even (Nat.card (rightConjugate (centralizer (A : Set G)) g)) := by
    rw [rightConjugate_card]
    exact htight.1
  have hT1 : T ≠ ⊥ := isSylowOf_ne_bot_of_even hTK hKgeven
  obtain ⟨e⟩ := lemma33Four G A hA R hR g hg T hTN hT1 hTR
  have hcardTR : Nat.card T = Nat.card R := by
    rw [hTK.card_eq, hR.card_eq, rightConjugate_card]
  have hRC : R ≤ centralizer (T : Set G) := by
    have h1 : Nat.card R ≤ Nat.card (R ⊓ centralizer (T : Set G) : Subgroup G) := by
      rw [Nat.card_congr e.toEquiv, hcardTR]
    exact inf_eq_left.mp (eq_of_le_of_card_ge inf_le_left h1)
  have hcomm : ⁅T, R⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hRC
  have hKgt := tightlyEmbedded_rightConjugate htight g
  have hRN : R ≤ normalizer (rightConjugate A g : Set G) := by
    intro x hx
    have hxT := mem_centralizer_iff.mp (hRC hx)
    have hxKg : x ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) := by
      by_contra hxN
      have hle : T ≤ rightConjugate (centralizer (A : Set G)) g ⊓
          rightConjugate (rightConjugate (centralizer (A : Set G)) g) x := by
        refine le_inf hTK.le fun t ht => ?_
        rw [mem_rightConjugate_iff]
        have : x * t * x⁻¹ = t := by rw [← hxT t ht, mul_inv_cancel_right]
        rw [this]
        exact hTK.le ht
      exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr
        ((two_dvd_card_of_isSylowOf hTK hKgeven).trans (card_dvd_of_le hle)))) (hKgt.2 x hxN)
    rw [mem_normalizer_rightConjugate_iff] at hxKg ⊢
    rwa [hNK] at hxKg
  have hKn : ¬ (centralizer (A : Set G)).Normal := by
    have h := not_normal_rightConjugate_centralizer hA 1
    rwa [rightConjugate_one] at h
  refine ⟨g, hg, R, T, hR, hTK, hTNA, hRN, hcomm,
    sylowInTightTwoNilpotent_of_hyp31 h32 h4 h34 hA hTK A, ?_⟩
  exact sylowInTightTwoNilpotent_of_tightlyEmbedded hR htight.1
    (lemma21 h4 htight hR (h32 G A hA R hR) (h34 G A hA).2 hKn).1 _

theorem lemma33Two_of (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) : Lemma33Two := by
  intro G _ _ A hA R hR g hg T hTN hT1 hTR hTK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htight := tightlyEmbedded_centralizer hA.standard
  have hNK := normalizer_centralizer_eq hA.standard
  refine hA.hypII G A T ⟨MulEquiv.refl _⟩ ⟨isElemAbelian_of_isSylowOf_rightConjugate h32 hA hTK,
    ?_, hTN.le.trans inf_le_right, ?_⟩ (sylowInTightTwoNilpotent_of_hyp31 h32 h4 h34 hA hTK A)
  ·
    obtain ⟨E, hEK, -, hE4⟩ := exists_elemAbelian_four hA.rank
    have h4K : 2 ^ 2 ∣ Nat.card (rightConjugate (centralizer (A : Set G)) g) := by
      rw [rightConjugate_card, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hE4]
      exact card_dvd_of_le hEK
    exact Nat.le_of_dvd Nat.card_pos (by simpa using pow_dvd_card_of_isSylowOf hTK h4K)
  ·
    rw [← hNK] at hg
    refine eq_bot_of_isPGroup_of_odd (hTK.isPGroup.to_le inf_le_left) ?_
    exact (htight.2 g hg).of_dvd_nat (card_dvd_of_le (le_inf inf_le_right
      (inf_le_left.trans hTK.le)))

theorem section3Config_of_asc76Theorem2 (hT2 : Asc76Theorem2) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) : Section3Config :=
  section3Config_of (lemma32_of_asc76Theorem2 hT2) (lemma33Three_of_asc76Theorem2 hT2) h4 h34

theorem lemma33Two_of_asc76Theorem2 (hT2 : Asc76Theorem2) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) : Lemma33Two :=
  lemma33Two_of (lemma32_of_asc76Theorem2 hT2) h4 h34

end CFSG.ComponentClassification.AS76b
