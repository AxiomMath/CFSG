module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75L47Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22PartSeven

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure)

variable {G : Type} [Group G] [Finite G]

theorem eq_of_bar_eq {K A B S : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ normalizer (K : Set G)) (h : bar K A = bar K B) : A = B := by
  have hAB2 : IsPGroup 2 (A ⊓ B : Subgroup G) := hS2.to_le (inf_le_left.trans hAS)
  have hABN : A ⊓ B ≤ normalizer (K : Set G) := inf_le_left.trans (hAS.trans hSN)
  have hinf : bar K (A ⊓ B) = bar K A := by
    rw [← bar_inf_of_le_isPGroup hAS hBS hS2, h, inf_idem]
  have hcA : Nat.card (A ⊓ B : Subgroup G) = Nat.card A := by
    rw [← card_bar_of_isPGroup hAB2 hABN, hinf,
      card_bar_of_isPGroup (hS2.to_le hAS) (hAS.trans hSN)]
  have hcB : Nat.card (A ⊓ B : Subgroup G) = Nat.card B := by
    rw [← card_bar_of_isPGroup hAB2 hABN, hinf, h,
      card_bar_of_isPGroup (hS2.to_le hBS) (hBS.trans hSN)]
  exact (Subgroup.eq_of_le_of_card_ge inf_le_left hcA.ge).symm.trans
    (Subgroup.eq_of_le_of_card_ge inf_le_right hcB.ge)

theorem mem_of_toBar_mem_bar {K A S : Subgroup G} (hAS : A ≤ S) (hS2 : IsPGroup 2 S)
    {x : normalizer (K : Set G)} (hxS : (x : G) ∈ S) (h : toBar K x ∈ bar K A) :
    (x : G) ∈ A := by
  obtain ⟨a, ha, hax⟩ := (mem_bar_iff K A _).mp h
  rw [← toBar_injOn_of_isPGroup hS2 (hAS ha) hxS hax]
  exact ha

theorem isElemAbelian_of_mulEquiv {Y Z : Type*} [Group Y] [Group Z] {A : Subgroup Y}
    {B : Subgroup Z} (e : A ≃* B) (hB : CFSG.Open.IsElemAbelian 2 B) :
    CFSG.Open.IsElemAbelian 2 A := by
  refine ⟨⟨⟨fun a b => e.injective ?_⟩⟩, fun x hx => ?_⟩
  · rw [map_mul, map_mul]
    exact hB.1.is_comm.comm _ _
  · have h1 : e ⟨x, hx⟩ ^ 2 = 1 := Subtype.ext (by simpa using hB.2 _ (e ⟨x, hx⟩).2)
    have h2 : (⟨x, hx⟩ : A) ^ 2 = 1 := e.injective (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val h2

theorem hyp3 {K J T R : Subgroup G} (hK : TightlyEmbedded K) (hJ : TightlyEmbedded J)
    (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) :
    AschbacherTheorem3.Hyp3 (bar K K) (bar K T) (bar K (J ⊓ (K ⊔ T))) (bar K (R ⊔ T)) := by
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTKb := inf_eq_bot_of_le hKJ hT2 hTJ
  have hKTN : K ⊔ T ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  set P := J ⊓ (K ⊔ T) with hP
  have hTP : IsSylowOf 2 T P := hT.of_le (le_inf hTJ le_sup_right) (inf_le_inf_left _ hKTN)
  have heven : Even (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    have h2T : 2 ∣ Nat.card T := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2T.trans (Subgroup.card_dvd_of_le hTP.le))
  have htight : ∀ y ∈ K ⊔ T, y ∉ normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)) := by
    intro y hy hyN
    have hyJ : y ∉ normalizer (J : Set G) := by
      intro hyn
      apply hyN
      rw [← rightConjugate_eq_self_iff] at hyn ⊢
      rw [hP, AschbacherTheorem3.rightConjugate_inf, hyn,
        (rightConjugate_eq_self_iff _ y).mpr (Subgroup.le_normalizer hy)]
    exact (hJ.2 y hyJ).of_dvd_nat
      (Subgroup.card_dvd_of_le (inf_le_inf inf_le_left (Subgroup.map_mono inf_le_left)))
  exact hyp3_bar le_rfl (core_le K) Subgroup.le_normalizer hTK hTK hT2 hT1 hTKb inf_le_right
    hTP heven htight (isSylowOf_sup hR hT2 hTK hTR hTKb) le_sup_right
    (isSylowOf_sup_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR)
    (relIndex_sup_inf_normalizer_le hK hJ hKJ hfac hT hT1 hR hTR)

theorem relativeWeakClosure_ne {K T R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hT2 : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G)) (hTR : T ≤ normalizer (R : Set G))
    (hW : T ≠ weakClosure K T (R ⊔ T)) :
    relativeWeakClosure (bar K K) (bar K T) (bar K (R ⊔ T)) ≠ bar K T := by
  have hSN : R ⊔ T ≤ normalizer (K : Set G) := sup_le (hR.le.trans Subgroup.le_normalizer) hTK
  rw [← bar_weakClosure hSN hTK hT2]
  intro h
  exact hW (eq_of_bar_eq le_sup_right (weakClosure_le K T (R ⊔ T))
    (hR.isPGroup.to_sup_of_normal_left' hT2 hTR) hSN h.symm)

theorem isDihedral_bar_of_shape {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hmK : 1 < CFSG.Open.pRank 2 K)
    (h : IsCyclic (bar K R) ∨ AschbacherTheorem3.IsQuaternionTwoGroup (bar K R) ∨
      AschbacherTheorem3.IsDihedralTwoGroup (bar K R)) :
    AschbacherTheorem3.IsDihedralTwoGroup (bar K R) := by
  have hRN : R ≤ normalizer (K : Set G) := hR.le.trans le_normalizer
  obtain ⟨E, hER, hE, hE4⟩ := exists_isElemAbelian_le hR hmK
  have hE2 : IsPGroup 2 E := hR.isPGroup.to_le hER
  have hEb : ∀ y ∈ bar K E, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (mem_bar_iff K E y).mp hy
    have hu2 : u ^ 2 = 1 := Subtype.ext (by simpa using hE.2 _ hu)
    rw [← map_pow, hu2, map_one]
  have hEcard : Nat.card (bar K E) = Nat.card E := card_bar_of_isPGroup hE2 (hER.trans hRN)
  rcases h with hc | ⟨k, hk, ⟨eQ⟩⟩ | hd
  · exfalso
    have := card_le_two_of_isCyclic (bar_mono K hER) hc hEb
    omega
  · exfalso
    have : NeZero (2 ^ (k - 2)) := ⟨by positivity⟩
    have := card_le_two_of_quaternion eQ (bar_mono K hER) hEb
    omega
  · exact hd

theorem isDihedral_and_of_isCyclic {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hmK : 1 < CFSG.Open.pRank 2 K)
    (hW : T ≠ weakClosure K T (R ⊔ T)) (hcyc : IsCyclic T) :
    AschbacherTheorem3.IsDihedralTwoGroup R ∧
      (AschbacherTheorem3.IsDihedralTwoGroup (R ⊔ T) ∨
        AschbacherTheorem3.IsWreathedTwoGroup (R ⊔ T)) := by
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTKb := inf_eq_bot_of_le hKJ hT2 hTJ
  have hRN : R ≤ normalizer (K : Set G) := hR.le.trans le_normalizer
  have hS2 : IsPGroup 2 (R ⊔ T : Subgroup G) := hR.isPGroup.to_sup_of_normal_left' hT2 hTR
  have hSN : R ⊔ T ≤ normalizer (K : Set G) := sup_le hRN hTK
  have h3 := hyp3 hK hJ hKJ hfac hT hT1 hR hTR
  have hWne := relativeWeakClosure_ne hR hT2 hTK hTR hW
  have hRbar : bar K (R ⊔ T) ⊓ bar K K = bar K R := by
    rw [← bar_inf_of_core_le (core_le K), sup_inf_eq hR.le hTR hTKb]
  obtain ⟨eT⟩ := nonempty_mulEquiv_bar hTK hT2
  have hcycb : IsCyclic (bar K T) := isCyclic_of_surjective eT.toMonoidHom eT.surjective
  have hRd : AschbacherTheorem3.IsDihedralTwoGroup (bar K R) := by
    have hshape := (Asc75L47.lemma47_cyclic h3 hWne hcycb).1
    rw [hRbar] at hshape
    exact isDihedral_bar_of_shape hR hmK hshape
  have hSd := Asc75L47.lemma47_cyclic_of_isDihedral h3 hWne hcycb (by rw [hRbar]; exact hRd)
  obtain ⟨eR⟩ := nonempty_mulEquiv_bar hRN hR.isPGroup
  obtain ⟨eS⟩ := nonempty_mulEquiv_bar hSN hS2
  obtain ⟨k, hk, ⟨eD⟩⟩ := hRd
  refine ⟨⟨k, hk, ⟨eR.trans eD⟩⟩, ?_⟩
  rcases hSd with ⟨k', hk', ⟨e'⟩⟩ | ⟨k', hk', ⟨e'⟩⟩
  · exact Or.inl ⟨k', hk', ⟨eS.trans e'⟩⟩
  · exact Or.inr ⟨k', hk', ⟨eS.trans e'⟩⟩

end CFSG.ComponentClassification.Asc76.Lemma22
