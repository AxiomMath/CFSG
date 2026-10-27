module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1h
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Thm4
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1d

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

@[expose] def UniqueOfInverts : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {R C C' : Subgroup G}, IsPGroup 2 R → C ≤ R →
    (C.subgroupOf R).Normal → IsMulCommutative C →
    (∀ r ∈ R, r ∉ C → r ^ 2 ∈ C → ∀ x ∈ C, r * x * r⁻¹ = x⁻¹) →
    (∀ E : Subgroup G, C ≤ E → E ≤ R → (∀ x ∈ E, x ^ 2 ∈ C) →
      (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ C) → C.relIndex E ≤ 2) →
    (∀ x ∈ C, x ^ 2 = 1 → ∃ y ∈ C, x = y ^ 2) → ¬ IsCyclic C → C' ≤ R → (C' ≃* C) → C' = C

variable {G : Type} [Group G] [Finite G]

theorem Overlap.false_of_minimal (h22 : Asc76Lemma22) (h75 : Asc75Theorem4)
    (h4' : Asc76Theorem4) (hU : UniqueOfInverts) {A R T : Subgroup G} {g : G}
    (hO : standardComponentOddCore G = ⊥) (hII : Asc76HypII A) (h : Overlap A R g T)
    (hm : 1 < Open.pRank 2 (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R)
    (hnot : ¬ IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hmin : ∀ (x : G) (V : Subgroup G), Overlap A R x V →
      ¬ IsSylowOf 2 V (rightConjugate (centralizer (A : Set G)) x) → Nat.card T ≤ Nat.card V) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  set C := R ⊓ centralizer (T : Set G) with hCdef
  have hTc := h.isMulCommutative h22 hm hnot
  have hTe := h.not_isElemAbelian h22 h75 hII hm hRd hnot
  have hTnc := h.not_isCyclic h22 hm hRd hnot
  have hUAK := omegaOne_le_sup_centralizer h75 h.standard hII h.not_mem h.sylow h.ne_bot hTc
    (h.four_le_card_omegaOne h22 hm hRd hnot)
  obtain ⟨e⟩ := h.mulEquiv
  have hCc : IsMulCommutative C := isMulCommutative_of_mulEquiv' e hTc
  have hCR : C ≤ R := inf_le_left
  have hCn := h.normal_inf_centralizer h22 hm
  have hRC : R ≤ normalizer (C : Set G) := (normal_subgroupOf_iff_le_normalizer hCR).mp hCn
  have hClt : C < R := by
    refine lt_of_le_of_ne hCR fun heq => ?_
    have h1 := h.card_inf_centralizer
    rw [← hCdef, heq] at h1
    exact (h.card_lt hnot).ne h1.symm
  obtain ⟨r, hr, hrC, hr2⟩ := exists_not_mem_sq_mem hClt h.sylowR.isPGroup hRC
  have hinv := h.inv_of_sq_mem h22 hm hnot hTe
  have hsq := h.exists_sq hTc hUAK hr hrC (hinv r hr hrC hr2)
  have hCnc : ¬ IsCyclic C := fun hc => hTnc (isCyclic_of_surjective e.toMonoidHom e.surjective)
  have hCu : ∀ C' : Subgroup G, C' ≤ R → Nonempty (C' ≃* C) → C' = C := fun C' hC'R ⟨e'⟩ =>
    hU h.sylowR.isPGroup hCR hCn hCc hinv (h.relIndex_le_two h22 hm hnot hTe) hsq hCnc hC'R e'
  have H : ∀ (x : G) (V : Subgroup G), Overlap A R x V →
      IsSylowOf 2 V (rightConjugate K x) ∨ R ⊓ centralizer (V : Set G) = C :=
    fun x V hV => h.inf_centralizer_eq_or_isSylowOf h22 hm hnot hTe hCu hV (hmin x V hV)
  have hCN := h.le_normalizer_inf_centralizer hnot H
  have hJK := h.le_normalizer_sup_oddCoreIn h22 hm hRd hnot hTe
  have hJN := h.normalizer_le_normalizer_sup_oddCoreIn hJK hCN
  set J₀ := oUpperTwoPrime (C ⊔ oddCoreIn K) with hJ₀def
  have hJ₀N : normalizer (K : Set G) ≤ normalizer (J₀ : Set G) :=
    hJN.trans (normalizer_le_normalizer_oUpperTwoPrime _)
  have hstar := h.star H hJ₀N
  have hCK : C ≤ K := hCR.trans h.sylowR.le
  have hCp : IsPGroup 2 C := h.sylowR.isPGroup.to_le hCR
  obtain ⟨hCsyl, -⟩ := isSylowOf_oUpperTwoPrime_sup hCK hCp
  have hmC : 1 < Open.pRank 2 C := by
    by_contra hr1
    exact hCnc (isCyclic_of_pRank_le_one hCp hCc hr1)
  have hJ₀K : J₀ ≤ K := (oUpperTwoPrime_le _).trans (sup_le hCK (oddCoreIn_le K))
  have hCe := isElemAbelian_of_theorem4 h4' h.standard hO h.not_mem hJ₀K hJ₀N
    (oUpperTwoPrime_oUpperTwoPrime _) hstar hCsyl hmC
  exact hTe (Asc76X.isElemAbelian_of_mulEquiv e hCe)

theorem isSylowOf_of_overlap (h22 : Asc76Lemma22) (h75 : Asc75Theorem4) (h4' : Asc76Theorem4)
    (hU : UniqueOfInverts) {A R : Subgroup G} (hO : standardComponentOddCore G = ⊥)
    (hII : Asc76HypII A) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hRd : ¬ IsDihedralTwoGroup R) :
    ∀ (n : ℕ) (x : G) (V : Subgroup G), Overlap A R x V → Nat.card V = n →
      IsSylowOf 2 V (rightConjugate (centralizer (A : Set G)) x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x V hV hcard
    by_contra hnot
    refine hV.false_of_minimal h22 h75 h4' hU hO hII hm hRd hnot fun x' V' hV' hnot' => ?_
    by_contra hlt
    push Not at hlt
    exact hnot' (ih _ (hcard ▸ hlt) x' V' hV' rfl)

omit [Finite G] in
theorem isDihedralTwoGroup_of_mulEquiv {P P' : Subgroup G} (e : P ≃* P')
    (h : IsDihedralTwoGroup P') : IsDihedralTwoGroup P := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  exact ⟨n, hn, ⟨e.trans f⟩⟩

theorem isSylowOf_of_not_isDihedralTwoGroup (h22 : Asc76Lemma22) (h75 : Asc75Theorem4)
    (h4' : Asc76Theorem4) (hU : UniqueOfInverts) {A R : Subgroup G}
    (hA : standardComponentIsStandard A) (hO : standardComponentOddCore G = ⊥)
    (hII : Asc76HypII A) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R) {g : G}
    (hg : g ∉ normalizer (A : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)))
    (hT1 : T ≠ ⊥) : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  have hTN : T ≤ normalizer (K : Set G) := by
    rw [normalizer_centralizer_eq hA]
    exact hT.le.trans inf_le_right
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_le (le_sup_right : T ≤ K ⊔ T) hT.isPGroup
  have hR' : IsSylowOf 2 (S ⊓ K) K := hS.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTN)
  have hTR' : T ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (le_normalizer (hTS ht)) (hTN ht)
  obtain ⟨c, -, hcR⟩ := exists_rightConjugate_eq_of_isSylowOf hR' hR
  have hR'd : ¬ IsDihedralTwoGroup (S ⊓ K) := fun hd => hRd (isDihedralTwoGroup_of_mulEquiv
    (by rw [← hcR]; exact R.equivMapOfInjective _ (MulAut.conj c⁻¹).injective) hd)
  exact isSylowOf_of_overlap h22 h75 h4' hU hO hII hm hR'd _ g T ⟨hA, hg, hT, hT1, hR', hTR'⟩ rfl

end CFSG.ComponentClassification.Asc76.Sec5
