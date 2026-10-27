module

public import CFSG.CGT.PushingUpLit.SolKNA.Thm3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.Open (IsElemAbelian)
open CFSG.CGT.PushingUpLit.SolKAb (IsCommSubgroup)
open CFSG.ComponentClassification.AschbacherTheorem3 (Thm3Conclusion Theorem3Statement centerOf
  frattiniOf omegaOne oTwoPrime)
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure subgroup_le_relative_weak_closure
  relative_weak_closure_le)
open CFSG.ComponentClassification.Asc76.Lemma22 (card_relativeNormalizer relativeNormalizer_sup_inf)
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix (tightlyEmbedded_subgroupOf_iff)
open scoped MatrixGroups

variable {G : Type} [Group G]

private theorem isSylowOf_self_two [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) :
    IsSylowOf 2 P P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  refine isSylowOf_of_card le_rfl ?_
  rw [hk, Nat.Prime.factorization_pow Nat.prime_two]
  simp

private theorem nontrivial_psl2 {K : Type*} [Field K] [CharP K 2] : Nontrivial PSL(2, K) := by
  let e := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)
  refine e.toEquiv.nontrivial_congr.mpr ?_
  refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun h => ?_⟩⟩
  have := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp at this



section Abstract

variable [Finite G] {R T : Subgroup G}

omit [Finite G] in
theorem card_sup_inf_normalizer_abstract (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hTRb : T ⊓ R = ⊥) :
    Nat.card ↥((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) =
      Nat.card ↥T * Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) := by
  rw [card_relativeNormalizer hTR hTRb le_sup_right le_rfl,
    relativeNormalizer_sup_inf le_rfl hTR hTRb]

theorem thm3_abstract (h3 : Theorem3Statement) (hR : IsPGroup 2 R) (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hTRb : T ⊓ R = ⊥)
    (hTI : ∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T)
    (hγ : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card ↥T) :
    Thm3Conclusion R T (R ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 (R ⊔ T : Subgroup G) := hR.to_sup_of_normal_left' hT hTR
  have hSN2 : IsPGroup 2 ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :=
    hS2.to_inf_left
  have hcardN := card_sup_inf_normalizer_abstract hTR hTRb
  have hidx : T.relIndex ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card ↥T := by
    have h1 := Subgroup.relIndex_mul_card T ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G))
    rw [inf_eq_left.mpr (le_inf le_sup_right Subgroup.le_normalizer), hcardN] at h1
    have h2 : T.relIndex ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) =
        Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1, mul_comm])
    rw [h2]
    exact hγ
  have heven : Even (Nat.card ↥T) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    rw [hn]
    exact (Nat.even_pow.mpr ⟨even_two, hn0⟩)
  have htight : TightlyEmbedded (T.subgroupOf (R ⊔ T)) := by
    refine (tightlyEmbedded_subgroupOf_iff le_sup_right).mpr ⟨heven, fun g hg hgN => ?_⟩
    have hbot : T ⊓ rightConjugate T g = ⊥ := by
      by_contra hne
      exact hgN ((rightConjugate_eq_self_iff T g).mp (hTI g hg hne))
    rw [hbot, Subgroup.card_bot]
    exact odd_one
  have hodd : CFSG.oddCore ↥R = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun N hN => ?_)
    obtain ⟨-, hNodd⟩ := hN
    have hN2 : IsPGroup 2 N := (hR.of_equiv (Subgroup.topEquiv (G := R)).symm).to_le le_top
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    have hk0 : k = 0 := by
      by_contra hk0
      rw [hk] at hNodd
      exact (Nat.not_even_iff_odd.mpr hNodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk
    exact (Subgroup.eq_bot_of_card_eq N hk).le
  exact h3 G R T T (R ⊔ T) ⟨hT1, ⟨⟨hTR, hTRb, hT⟩, isSylowOf_self_two hS2,
    isSylowOf_self_two hSN2⟩, isSylowOf_self_two hT, le_sup_right, htight, hidx, hodd⟩

end Abstract


section Main

variable [Finite G] {R T : Subgroup G}

theorem lemma14_of (h3 : Theorem3Statement) (hR : IsPGroup 2 R) (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hTRb : T ⊓ R = ⊥)
    (hcomm : IsCommSubgroup T) (hnc : ¬ IsCyclic T)
    (hTI : ∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T)
    (hγ : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card ↥T) :
    R ≤ Subgroup.normalizer (T : Set G) ∨
      BData R T ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) ∨ ∃ W, AData R T W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : TIPair R T := ⟨hR, hT, hT1, hTR, hTRb, hcomm, hTI⟩
  rcases thm3_abstract h3 hR hT hT1 hTR hTRb hTI hγ with h1 | h2 | h3' | h4 | h5
  · exact absurd h1.1 hnc
  · exact Or.inl (le_sup_left.trans h2)
  · exfalso
    obtain ⟨n, -, -, hinf, -, -, -, ⟨e⟩⟩ := h3'
    have hS2 := hP.two_S
    have hpc : CFSG.Open.pCoreOf 2 (R ⊔ T) = R ⊔ T := by
      refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 le_rfl ?_ hS2
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    have hle : oTwoPrime R ≤ R ⊔ T :=
      (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_sup_left hx.1
    rw [hpc, inf_eq_right.mpr hle] at hinf
    have hsub : Subsingleton ↥(oTwoPrime R) := by
      rw [hinf]
      infer_instance
    have hsub' : Subsingleton PSL(2, GaloisField 2 n) := e.symm.injective.subsingleton
    have hnt := nontrivial_psl2 (K := GaloisField 2 n)
    exact not_subsingleton _ hsub'
  · right
    left
    obtain ⟨x, hx, hW1, hTT, hcT, hW2, hnorm, -, -⟩ := h4
    have hTx : rightConjugate T x ≤ Subgroup.normalizer (T : Set G) := by
      have h6 : ⁅rightConjugate T x, T⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcT
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h6).trans
        (Subgroup.centralizer_le_normalizer _)
    have hcardN : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T := by
      have e1 := card_sup_inf_normalizer_abstract hTR hTRb
      have e2 : Nat.card ↥((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) =
          Nat.card ↥T * Nat.card ↥T := by
        rw [← hW2, hW1, CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer
          hTx hTT, rightConjugate_card]
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (e1.symm.trans e2)
    rw [hW2] at hnorm
    exact { toTIPair := hP, hW := rfl, normal := hnorm, card_N := hcardN }
  · right
    right
    exact ⟨relativeWeakClosure R T (R ⊔ T), aData_of_alt5 hP
      (subgroup_le_relative_weak_closure _ _ _ le_sup_right) (relative_weak_closure_le _ _ _)
      h5.1 h5.2.1 h5.2.2.1 h5.2.2.2.1 h5.2.2.2.2.1 h5.2.2.2.2.2.1 h5.2.2.2.2.2.2 hγ⟩

end Main

section Certified


variable [Finite G] {R T : Subgroup G}

theorem lemma14 (hR : IsPGroup 2 R) (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) (hTR : T ≤ Subgroup.normalizer (R : Set G)) (hTRb : T ⊓ R = ⊥)
    (hcomm : IsCommSubgroup T) (hnc : ¬ IsCyclic T)
    (hTI : ∀ x ∈ R ⊔ T, T ⊓ rightConjugate T x ≠ ⊥ → rightConjugate T x = T)
    (hγ : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card ↥T) :
    R ≤ Subgroup.normalizer (T : Set G) ∨
      BData R T ((R ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) ∨ ∃ W, AData R T W :=
  lemma14_of CFSG.ComponentClassification.AschbacherTheorem3.theorem_3_holds hR hT hT1 hTR hTRb
    hcomm hnc hTI hγ

end Certified

end CFSG.CGT.PushingUpLit.SolKNA
