module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

theorem one_lt_pRank_of_isSylowOf {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hm : 1 < Open.pRank 2 K) : 1 < Open.pRank 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEK, hE, hE4⟩ := Asc76X.exists_fourGroup_le hm
  have hEp : IsPGroup 2 E := by
    have h4 : Nat.card E = 2 ^ 2 := by rw [hE4]; norm_num
    exact IsPGroup.of_card h4
  obtain ⟨c, -, hc⟩ := exists_rightConjugate_le_of_isSylowOf hR hEp hEK
  exact Asc76X.one_lt_pRank_of_fourGroup hc (Asc76X.isElemAbelian_rightConjugate hE c)
    (by rw [rightConjugate_card, hE4])

omit [Finite G] in
theorem le_oUpperTwoPrime_of_isPGroup {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 P) :
    P ≤ oUpperTwoPrime K := fun x hx => by
  obtain ⟨m, hm⟩ := hP ⟨x, hx⟩
  exact mem_oUpperTwoPrime (hPK hx) (n := m) (by simpa using congrArg Subtype.val hm)

theorem isElemAbelian_of_not_isDihedralTwoGroup (h22 : Asc76Lemma22) (h75 : Asc75Theorem4)
    (h4' : Asc76Theorem4) (hU : UniqueOfInverts) {A R : Subgroup G}
    (hA : standardComponentIsStandard A) (hO : standardComponentOddCore G = ⊥)
    (hII : Asc76HypII A) (hm : 1 < Open.pRank 2 (centralizer (A : Set G)))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRd : ¬ IsDihedralTwoGroup R) {g : G}
    (hg : g ∉ normalizer (A : Set G)) : IsElemAbelian 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  set K₀ := oUpperTwoPrime K with hK₀def
  have hNA : normalizer (K : Set G) = normalizer (A : Set G) := normalizer_centralizer_eq hA
  have hRK₀ : R ≤ K₀ := le_oUpperTwoPrime_of_isPGroup hR.le hR.isPGroup
  have hK₀K : K₀ ≤ K := oUpperTwoPrime_le K
  have hRK₀s : IsSylowOf 2 R K₀ := hR.of_le hRK₀ hK₀K
  have hNK : normalizer (K : Set G) ≤ normalizer (K₀ : Set G) :=
    normalizer_le_normalizer_oUpperTwoPrime K
  have hReven : Even (Nat.card R) :=
    even_iff_two_dvd.mpr (two_dvd_card_of_isSylowOf hR (tightlyEmbedded_centralizer hA).1)
  have hK₀even : Even (Nat.card K₀) :=
    even_iff_two_dvd.mpr (hReven.two_dvd.trans (card_dvd_of_le hRK₀))
  have hNeq : normalizer (K₀ : Set G) = normalizer (K : Set G) :=
    le_antisymm (normalizer_le_normalizer_of_tightlyEmbedded (tightlyEmbedded_centralizer hA) hK₀K
      hK₀even) hNK
  refine isElemAbelian_of_theorem4 h4' hA hO hg hK₀K hNK (oUpperTwoPrime_oUpperTwoPrime K)
    (fun y heven => ?_) hRK₀s (one_lt_pRank_of_isSylowOf hR hm)
  by_cases hy : y ∈ normalizer (K : Set G)
  · have hKy : rightConjugate K₀ y = K₀ := (rightConjugate_eq_self_iff K₀ y).mpr (hNK hy)
    exact ⟨R, by rw [hKy]; exact hRK₀s, hRK₀.trans le_normalizer⟩
  have hyA : y ∉ normalizer (A : Set G) := by rwa [← hNA]
  have hle : rightConjugate K₀ y ⊓ normalizer (K₀ : Set G) ≤
      rightConjugate K y ⊓ normalizer (A : Set G) := by
    rw [hNeq, hNA]
    exact inf_le_inf_right _ (rightConjugate_le_rightConjugate hK₀K y)
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (rightConjugate K y ⊓ normalizer (A : Set G))
  have hT1 : T ≠ ⊥ := isSylowOf_ne_bot_of_even hT
    (even_iff_two_dvd.mpr (heven.two_dvd.trans (card_dvd_of_le hle)))
  have hTs := isSylowOf_of_not_isDihedralTwoGroup h22 h75 h4' hU hA hO hII hm hR hRd hyA hT hT1
  have hTK₀ : T ≤ rightConjugate K₀ y := by
    rw [hK₀def, ← Asc76X.oUpperTwoPrime_rightConjugate]
    exact le_oUpperTwoPrime_of_isPGroup hTs.le hT.isPGroup
  refine ⟨T, hTs.of_le hTK₀ (rightConjugate_le_rightConjugate hK₀K y), ?_⟩
  rw [hNeq, hNA]
  exact hT.le.trans inf_le_right

theorem commutator_inf_normalizer_eq_bot {A R T : Subgroup G}
    (hA : standardComponentIsStandard A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hRe : IsElemAbelian 2 R) {g : G} (hg : g ∉ normalizer (A : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)))
    (hT1 : T ≠ ⊥) (hTs : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    ⁅T ⊓ normalizer (R : Set G), R⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  have hTN : T ≤ normalizer (K : Set G) := by
    rw [normalizer_centralizer_eq hA]
    exact hT.le.trans inf_le_right
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_le (le_sup_right : T ≤ K ⊔ T) hT.isPGroup
  have hR' : IsSylowOf 2 (S ⊓ K) K := hS.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTN)
  have hTR' : T ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_inf (le_normalizer (hTS ht)) (hTN ht)
  have hO : Overlap A (S ⊓ K) g T := ⟨hA, hg, hT, hT1, hR', hTR'⟩
  have hcardT : Nat.card T = Nat.card (S ⊓ K : Subgroup G) := by
    rw [hTs.card_eq, hR'.card_eq, rightConjugate_card]
  have hCR' : S ⊓ K ⊓ centralizer (T : Set G) = S ⊓ K :=
    eq_of_le_of_card_ge inf_le_left (by rw [hO.card_inf_centralizer, hcardT])
  have hR'T : S ⊓ K ≤ centralizer (T : Set G) := by
    rw [← hCR']
    exact inf_le_right
  obtain ⟨c, -, hcR⟩ := exists_rightConjugate_eq_of_isSylowOf hR' hR
  have hR'e : IsElemAbelian 2 (S ⊓ K) := by
    rw [← hcR]
    exact Asc76X.isElemAbelian_rightConjugate hRe c
  obtain ⟨e⟩ := hO.mulEquiv
  rw [hCR'] at e
  have hTe : IsElemAbelian 2 T := Asc76X.isElemAbelian_of_mulEquiv e hR'e
  set X := T ⊓ normalizer (R : Set G) with hXdef
  have hXT : X ≤ T := inf_le_left
  have hXc : IsMulCommutative X := isMulCommutative_of_le hXT hTe.1
  have hXK : X ≤ normalizer (K : Set G) := hXT.trans hTN
  have hKX : K ⊓ X = ⊥ := le_bot_iff.mp ((inf_le_inf_left K hXT).trans hO.inf_eq_bot_K.le)
  have hR'X : S ⊓ K ⊓ X = ⊥ := le_bot_iff.mp ((inf_le_inf inf_le_right le_rfl).trans hKX.le)
  have hRX : R ⊓ X = ⊥ := le_bot_iff.mp ((inf_le_inf hR.le le_rfl).trans hKX.le)
  have hXR' : X ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := hXT.trans hTR'
  have hXR : X ≤ normalizer (R : Set G) := inf_le_right
  have hXp : IsPGroup 2 X := hT.isPGroup.to_le hXT
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hXp
  have hcardKX : Nat.card (K ⊔ X : Subgroup G) = Nat.card K * Nat.card X :=
    card_sup_of_le_normalizer hXK hKX
  have hfac : 2 ^ (Nat.card (K ⊔ X : Subgroup G)).factorization 2 =
      Nat.card R * Nat.card X := by
    rw [hcardKX, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hm,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      smul_eq_mul, mul_one, pow_add, ← hR.card_eq]
  have hsylR' : IsSylowOf 2 (S ⊓ K ⊔ X) (K ⊔ X) := by
    refine isSylowOf_of_card (sup_le_sup_right inf_le_right X) ?_
    rw [hfac, card_sup_of_le_normalizer hXR' hR'X, ← hcardT, hTs.card_eq, rightConjugate_card,
      ← hR.card_eq]
  have hsylR : IsSylowOf 2 (R ⊔ X) (K ⊔ X) := by
    refine isSylowOf_of_card (sup_le_sup_right hR.le X) ?_
    rw [hfac, card_sup_of_le_normalizer hXR hRX]
  have hab' : IsMulCommutative (S ⊓ K ⊔ X : Subgroup G) :=
    isMulCommutative_sup hR'e.1 hXc ((le_centralizer_iff.mp (hXT.trans
      (le_centralizer_iff.mp hR'T))))
  obtain ⟨d, -, hdR⟩ := exists_rightConjugate_eq_of_isSylowOf hsylR hsylR'
  have hab : IsMulCommutative (R ⊔ X : Subgroup G) := by
    rw [← hdR]
    exact isMulCommutative_rightConjugate hab' d
  rw [eq_bot_iff, commutator_le]
  intro x hx r hr
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hab.is_comm.comm ⟨x, mem_sup_right hx⟩ ⟨r, mem_sup_left hr⟩)

end CFSG.ComponentClassification.Asc76.Sec5
