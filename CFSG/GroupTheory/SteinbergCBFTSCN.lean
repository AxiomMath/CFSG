module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.GroupTheory.FT63ChII

open Subgroup

@[expose] def SCN (P : Type*) [Group P] : Set (Subgroup P) :=
  {A | A.Normal ∧ IsMulCommutative A ∧ centralizer (A : Set P) = A}

@[expose] def SCN₃ (p : ℕ) (P : Type*) [Group P] : Set (Subgroup P) :=
  {A | A ∈ SCN P ∧ 3 ≤ CFSG.pRank p A}

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem le_of_isPGroup_of_not_dvd_relIndex {A C Q : Subgroup X} (hA : IsPGroup p A)
    (hAC : A ≤ C) (hidx : ¬ p ∣ A.relIndex C) (hQ : IsPGroup p Q) (hQC : Q ≤ C)
    (hQA : Q ≤ normalizer (A : Set X)) : Q ≤ A := by
  have hR : IsPGroup p ↥(Q ⊔ A) := hQ.to_sup_of_normal_right' hA hQA
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : A.relIndex (Q ⊔ A) ∣ p ^ k := hk ▸ (A.subgroupOf (Q ⊔ A)).index_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  have hmul := relIndex_mul_relIndex A (Q ⊔ A) C le_sup_right (sup_le hQC hAC)
  have hj0 : j = 0 := by
    by_contra hj0
    refine hidx ((dvd_pow_self p hj0).trans ?_)
    rw [← hj, ← hmul]
    exact dvd_mul_right _ _
  rw [hj0, pow_zero, relIndex_eq_one] at hj
  exact le_sup_left.trans hj

omit [Finite X] in
theorem le_normalizer_centralizer {A K : Subgroup X} (hK : K ≤ normalizer (A : Set X)) :
    K ≤ normalizer (centralizer (A : Set X) : Set X) := by
  intro g hg
  have hgA := mem_normalizer_iff.1 (hK hg)
  rw [mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hc a ha
    have ha' : g⁻¹ * a * g ∈ A := by
      refine (hgA (g⁻¹ * a * g)).2 ?_
      simpa [mul_assoc] using ha
    have h := hc _ ha'
    calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * a := by group
  · intro hc a ha
    have h := hc _ ((hgA a).1 ha)
    calc a * c = g⁻¹ * ((g * a * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
      _ = c * a := by group

theorem le_of_isPGroup_le_centralizer (P : Sylow p X) {A : Subgroup X}
    (hnorm : (P : Subgroup X) ≤ normalizer (A : Set X))
    (hcen : (P : Subgroup X) ⊓ centralizer (A : Set X) = A) {Q : Subgroup X}
    (hQ : IsPGroup p Q) (hQA : Q ≤ centralizer (A : Set X)) : Q ≤ A := by
  set C := centralizer (A : Set X)
  have hAP : A ≤ P := hcen ▸ inf_le_left
  have hAC : A ≤ C := hcen ▸ inf_le_right
  have hAp : IsPGroup p A := P.isPGroup'.to_le hAP
  have hPC := le_normalizer_centralizer hnorm
  have hidx : ¬ p ∣ A.relIndex C := by
    have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hPC
    have h2 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex
      (inf_le_right : (P : Subgroup X) ⊓ C ≤ C)
    have h3 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex
      (le_sup_left : (P : Subgroup X) ≤ (P : Subgroup X) ⊔ C)
    have heq : ((P : Subgroup X) ⊓ C).relIndex C =
        (P : Subgroup X).relIndex ((P : Subgroup X) ⊔ C) := by
      rw [h2, h3] at h1
      have hpos : 0 < Nat.card (P : Subgroup X) * Nat.card ↥((P : Subgroup X) ⊓ C) :=
        Nat.mul_pos Nat.card_pos Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_left hpos
      linarith
    rw [← hcen, heq]
    exact fun h => P.not_dvd_index (h.trans (relIndex_dvd_index_of_le le_sup_left))
  exact le_of_isPGroup_of_not_dvd_relIndex hAp hAC hidx hQ hQA
    (hQA.trans (centralizer_le_normalizer _))

omit [Finite X] in
theorem SCN.map_props {P : Subgroup X} {A : Subgroup P} (hA : A ∈ SCN P) :
    P ≤ normalizer (A.map P.subtype : Set X) ∧
      P ⊓ centralizer (A.map P.subtype : Set X) = A.map P.subtype := by
  obtain ⟨hAn, -, hAc⟩ := hA
  constructor
  · intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, hAn.conj_mem a ha _, rfl⟩
    · rintro ⟨b, hb, hbx⟩
      refine ⟨⟨g, hg⟩⁻¹ * b * ⟨g, hg⟩, ?_, ?_⟩
      · simpa using hAn.conj_mem b hb ⟨g, hg⟩⁻¹
      · change g⁻¹ * (b : X) * g = x
        rw [show (b : X) = g * x * g⁻¹ from hbx]
        group
  · apply le_antisymm
    · rintro x ⟨hxP, hxC⟩
      have hmem : (⟨x, hxP⟩ : P) ∈ centralizer (A : Set P) := by
        rw [mem_centralizer_iff]
        intro a ha
        exact Subtype.ext (mem_centralizer_iff.1 hxC _ ⟨a, ha, rfl⟩)
      rw [hAc] at hmem
      exact ⟨_, hmem, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨a.2, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have ha' : a ∈ centralizer (A : Set P) := by rw [hAc]; exact ha
      exact congrArg Subtype.val (mem_centralizer_iff.1 ha' b hb)

theorem ft_lemma_7_4_a (P : Sylow p X) {A : Subgroup (P : Subgroup X)} (hA : A ∈ SCN P)
    {H : Subgroup X} (hnorm : A.map (P : Subgroup X).subtype ≤ normalizer (H : Set X))
    (hAH : A.map (P : Subgroup X).subtype ⊓ H = ⊥) : Nat.Coprime p (Nat.card H) := by
  set A' := A.map (P : Subgroup X).subtype
  obtain ⟨hPA, hcen⟩ := SCN.map_props hA
  have hA'p : IsPGroup p A' := P.isPGroup'.to_le (map_subtype_le A)
  refine CFSG.SignalizerFunctor.Helpers.coprime_of_centralizer_coprime p Fact.out A' H hA'p
    hnorm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hdvd => ?_)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ centralizer (A' : Set X))) p hdvd
  have hQ : IsPGroup p (zpowers (g : X)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, Subgroup.orderOf_coe, hg]
    exact ⟨1, (pow_one p).symm⟩
  have hle : zpowers (g : X) ≤ A' :=
    le_of_isPGroup_le_centralizer P hPA hcen hQ
      ((zpowers_le (G := X)).2 (inf_le_right (a := H) g.2))
  have hg1 : (g : X) = 1 := by
    have : (g : X) ∈ A' ⊓ H := ⟨hle (mem_zpowers _), (inf_le_left (b := centralizer _) g.2)⟩
    rwa [hAH, mem_bot] at this
  have : orderOf g = 1 := by
    rw [← Subgroup.orderOf_coe, hg1, orderOf_one]
  rw [this] at hg
  exact (Fact.out : p.Prime).one_lt.ne' hg.symm

end CFSG.GroupTheory.FT63ChII
