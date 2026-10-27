module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1a

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_not_mem_sq_mem {C U : Subgroup G} (hCU : C < U) (hU : IsPGroup 2 U)
    (hn : U ≤ normalizer (C : Set G)) : ∃ r ∈ U, r ∉ C ∧ r ^ 2 ∈ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCn : (C.subgroupOf U).Normal := (normal_subgroupOf_iff_le_normalizer hCU.le).mpr hn
  set Q := U ⧸ C.subgroupOf U
  have hQp : IsPGroup 2 Q := hU.to_quotient _
  have hQ1 : Nontrivial Q := by
    rw [QuotientGroup.nontrivial_iff]
    intro h
    apply hCU.ne
    apply le_antisymm hCU.le
    intro x hx
    have : (⟨x, hx⟩ : U) ∈ C.subgroupOf U := h ▸ mem_top _
    exact this
  obtain ⟨n, hn'⟩ := IsPGroup.iff_card.mp hQp
  have h2 : 2 ∣ Nat.card Q := by
    rcases n with _ | n
    · have h1 : 1 < Nat.card Q := Finite.one_lt_card
      rw [hn'] at h1
      norm_num at h1
    · rw [hn', pow_succ]
      exact dvd_mul_left _ _
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 h2
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨r, r.2, fun hr => ?_, ?_⟩
  · have : (r : Q) = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [this, orderOf_one] at hq
    norm_num at hq
  · have h1 : ((r ^ 2 : U) : Q) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    have := mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    simpa using this

namespace Overlap

variable {A R T : Subgroup G} {g : G}

variable (h22 : Asc76Lemma22)

include h22 in
theorem inv_of_sq_mem (h : Overlap A R g T) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTe : ¬ IsElemAbelian 2 T) :
    ∀ r ∈ R, r ∉ R ⊓ centralizer (T : Set G) → r ^ 2 ∈ R ⊓ centralizer (T : Set G) →
      ∀ x ∈ R ⊓ centralizer (T : Set G), r * x * r⁻¹ = x⁻¹ := by
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨-, -, -, -, -, h6, -⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  have h6' := (h6 hTe (h.ne_weakClosure h22 hm hnot)).2.2
  rw [h.inf_normalizer_eq] at h6'
  exact h6'

include h22 in
theorem relIndex_le_two (h : Overlap A R g T) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTe : ¬ IsElemAbelian 2 T) :
    ∀ E : Subgroup G, R ⊓ centralizer (T : Set G) ≤ E → E ≤ R →
      (∀ x ∈ E, x ^ 2 ∈ R ⊓ centralizer (T : Set G)) →
      (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ R ⊓ centralizer (T : Set G)) →
      (R ⊓ centralizer (T : Set G)).relIndex E ≤ 2 := by
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨-, -, -, -, -, h6, -⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  have h6' := (h6 hTe (h.ne_weakClosure h22 hm hnot)).2.1
  rw [h.inf_normalizer_eq] at h6'
  exact h6'

include h22 in
theorem normal_inf_centralizer (h : Overlap A R g T)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G))) :
    ((R ⊓ centralizer (T : Set G)).subgroupOf R).Normal := by
  obtain ⟨hK, hKg, hodd, hfac, hmg⟩ := h.lemma22_hyps hm
  obtain ⟨-, -, -, -, -, -, h7⟩ :=
    h22 G _ _ T R hK hKg hodd hfac h.sylowK h.ne_bot h.sylowR h.normalizesR hm hmg
  rw [← h.inf_normalizer_eq]
  exact h7

omit h22 in
theorem tightlyEmbedded_sup (h : Overlap A R g T) : TightlyEmbedded (T.subgroupOf (R ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  have hTRT : T ≤ R ⊔ T := le_sup_right
  have hKgT : TightlyEmbedded (rightConjugate K g) := tightlyEmbedded_rightConjugate h.tight g
  have hTKg : T ≤ rightConjugate K g := h.sylow.le.trans inf_le_left
  have hTeven : Even (Nat.card T) := even_card_of_isPGroup h.sylow.isPGroup h.ne_bot
  have hNR : R ⊓ normalizer (rightConjugate K g : Set G) ≤ normalizer (T : Set G) := by
    obtain ⟨P, hP⟩ := exists_isSylowOf 2 (K ⊓ normalizer (rightConjugate K g : Set G))
    have hcard := card_eq_card_of_overlap h.tight h.not_mem_K h.sylowK h.ne_bot hP
    have hle : R ⊓ normalizer (T : Set G) ≤ R ⊓ normalizer (rightConjugate K g : Set G) :=
      inf_le_inf_left R (normalizer_le_normalizer_of_tightlyEmbedded hKgT hTKg hTeven)
    have h1 : Nat.card (R ⊓ normalizer (rightConjugate K g : Set G) : Subgroup G) ≤
        Nat.card P :=
      Sec5.card_le_of_isSylowOf hP (inf_le_inf_right _ h.sylowR.le) (h.sylowR.isPGroup.to_le
        inf_le_left)
    have h2 : Nat.card (R ⊓ normalizer (T : Set G) : Subgroup G) = Nat.card T := by
      rw [h.inf_normalizer_eq, h.card_inf_centralizer]
    have heq := eq_of_le_of_card_ge hle (by omega)
    rw [← heq]
    exact inf_le_right
  refine ⟨by rw [card_subgroupOf hTRT]; exact hTeven, fun y hy => ?_⟩
  have hy' : (y : G) ∉ normalizer (T : Set G) := fun h' =>
    hy ((mem_normalizer_subgroupOf_iff hTRT y).mpr h')
  have hTyle : rightConjugate T y ≤ R ⊔ T :=
    AschbacherTheorem3.rightConjugate_le_of_mem hTRT y.2
  rw [rightConjugate_subgroupOf, subgroupOf_inf_subgroupOf,
    card_subgroupOf (inf_le_left.trans hTRT)]
  by_cases hyN : (y : G) ∈ normalizer (rightConjugate K g : Set G)
  · exfalso
    have hymem : (y : G) ∈ ((R : Set G) * (T : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left R T h.normalizesR]
      exact y.2
    obtain ⟨r, hr, t, ht, hrt⟩ := hymem
    have hrt' : r * t = (y : G) := hrt
    have htN : t ∈ normalizer (rightConjugate K g : Set G) := Subgroup.le_normalizer (hTKg ht)
    have hrN : r ∈ normalizer (rightConjugate K g : Set G) := by
      have : r = (y : G) * t⁻¹ := by rw [← hrt']; group
      rw [this]
      exact mul_mem hyN (inv_mem htN)
    have hrT := hNR ⟨hr, hrN⟩
    apply hy'
    rw [← hrt']
    exact mul_mem hrT (Subgroup.le_normalizer ht)
  · have hle : T ⊓ rightConjugate T y ≤
        rightConjugate K g ⊓ rightConjugate (rightConjugate K g) y :=
      inf_le_inf hTKg (rightConjugate_le_rightConjugate hTKg y)
    exact (hKgT.2 y hyN).of_dvd_nat (card_dvd_of_le hle)

end Overlap

end CFSG.ComponentClassification.Asc76.Sec5
