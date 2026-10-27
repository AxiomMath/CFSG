module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocalBetween
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C9

open CFSG Subgroup C311
open scoped commutatorElement

theorem eq_bot_of_le_center_of_coprime {J : Type*} [Group J] [Finite J] [Group.IsPerfect J]
    {Z : Subgroup J} (hZ : Z ≤ center J) (hcop : Nat.Coprime (Nat.card Z) Z.index) : Z = ⊥ := by
  have hZn : Z.Normal := ⟨fun n hn g => by
    have h := mem_center_iff.mp (hZ hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hsup : H ⊔ Z = ⊤ := by rw [sup_comm]; exact hH.sup_eq_top
  have hcomm : commutator J ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨h₁, hh₁, z₁, hz₁, rfl⟩ := mem_sup_of_normal_right.mp (hsup ▸ mem_top x : x ∈ H ⊔ Z)
    obtain ⟨h₂, hh₂, z₂, hz₂, rfl⟩ := mem_sup_of_normal_right.mp (hsup ▸ mem_top y : y ∈ H ⊔ Z)
    have c1 := mem_center_iff.mp (hZ hz₁)
    have c2 := mem_center_iff.mp (hZ hz₂)
    have c1' := mem_center_iff.mp (hZ (inv_mem hz₁))
    have c2' := mem_center_iff.mp (hZ (inv_mem hz₂))
    have e : ⁅h₁ * z₁, h₂ * z₂⁆ = ⁅h₁, h₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc h₁ * z₁ * (h₂ * z₂) * (h₁ * z₁)⁻¹ * (h₂ * z₂)⁻¹
          = h₁ * (z₁ * h₂) * z₂ * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * (z₁ * z₂) * z₁⁻¹ * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by rw [← c1 h₂]; group
        _ = h₁ * h₂ * z₂ * (z₁ * z₁⁻¹) * h₁⁻¹ * z₂⁻¹ * h₂⁻¹ := by
          rw [show z₁ * z₂ = z₂ * z₁ from c2 z₁]; group
        _ = h₁ * h₂ * (z₂ * h₁⁻¹) * z₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by rw [← c2 h₁⁻¹]; group
    rw [e, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
  have hJH : Z ≤ H := by
    intro z _
    have : z ∈ commutator J := by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top z
    exact hcomm this
  have hdis := hH.disjoint
  rw [disjoint_iff] at hdis
  rw [← hdis, inf_eq_left.mpr hJH]

theorem card_eq_and_equiv_of_lieModel_nine {X : Type} [Group X] {p f : ℕ}
    (hm : Blueprint.LieModel X .PSL 2 p f) (h9 : p ^ f = 9) :
    Nat.card X = 360 ∧ Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel hm
  have := Fintype.ofFinite F
  have hF9 : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hF, h9]
  obtain ⟨eA⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      F hF9
  refine ⟨?_, ⟨e.trans eA⟩⟩
  rw [Nat.card_congr (e.trans eA).toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

variable {J : Type} [Group J]

theorem pPrimeCore_eq_bot_of_isSimpleGroup [IsSimpleGroup J] (hJ : IsTwoQuasisimple J) :
    pPrimeCore 2 J = ⊥ := by
  rcases (inferInstance : (pPrimeCore 2 J).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨x, hx⟩ := exists_not_mem_pPrimeCore hJ
    exact absurd (h ▸ mem_top x) hx

theorem center_eq_pPrimeCore (hle : pPrimeCore 2 J ≤ center J)
    [IsSimpleGroup (J ⧸ pPrimeCore 2 J)] (hna : ∃ a b : J ⧸ pPrimeCore 2 J, a * b ≠ b * a) :
    center J = pPrimeCore 2 J := by
  refine le_antisymm (fun z hz => ?_) hle
  have hz' : (QuotientGroup.mk z : J ⧸ pPrimeCore 2 J) ∈ center (J ⧸ pPrimeCore 2 J) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.mp hz) y]
  rw [FooteLit.center_eq_bot_of_isSimpleGroup hna, mem_bot, QuotientGroup.eq_one_iff] at hz'
  exact hz'

theorem card_eq_mul [Finite J] {p f : ℕ} (hm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (h9 : p ^ f = 9) : Nat.card J = 360 * Nat.card (pPrimeCore 2 J) := by
  rw [← (card_eq_and_equiv_of_lieModel_nine hm h9).1]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 J))

theorem pPrimeCore_eq_bot_of_card_dvd [Finite J] (hJ : IsTwoQuasisimple J) {p f : ℕ}
    (hm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) (h9 : p ^ f = 9)
    (hle : pPrimeCore 2 J ≤ center J) (hdvd : Nat.card J ∣ 20160) : pPrimeCore 2 J = ⊥ := by
  have : Group.IsPerfect J := hJ.1
  have hc := card_eq_mul hm h9
  have hodd : Odd (Nat.card (pPrimeCore 2 J)) := by
    have h' := (pPrimeCore_coprime_card (p := 2) (G := J))
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h'
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h')
  have h56 : Nat.card (pPrimeCore 2 J) ∣ 56 := by
    rw [hc, show (20160 : ℕ) = 360 * 56 by norm_num] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hidx : (pPrimeCore 2 J).index = 360 := by
    rw [← (card_eq_and_equiv_of_lieModel_nine hm h9).1]
    exact (Subgroup.index_eq_card _)
  apply eq_bot_of_le_center_of_coprime hle
  rw [hidx]
  have h7 : Nat.card (pPrimeCore 2 J) ∣ 7 := by
    have hcop : Nat.Coprime (Nat.card (pPrimeCore 2 J)) 8 :=
      Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
    exact hcop.dvd_of_dvd_mul_left (by rw [show (8 : ℕ) * 7 = 56 by norm_num]; exact h56)
  rcases (Nat.dvd_prime (by norm_num)).mp h7 with h | h <;> rw [h] <;> norm_num

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_eq_bot_of_alternating [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) {n : ℕ} (hn : n = 5 ∨ 7 ≤ n)
    (θ : GeneralizedFitting.subgroup G ≃* alternatingGroup (Fin n)) {a : G} (ha : orderOf a = 2)
    {J : Subgroup G} (hJ : IsTwoComponentIn J (centralizer {a})) : pPrimeCore 2 ↥J = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK, e, -⟩ :=
    CatalogueBAlternating.generalizedFitting_between_alternating_symmetric hnab hn θ
  have hNC := normalizer_zpowers_eq_centralizer ha
  have hJN : J ≤ normalizer (zpowers a : Set G) := hNC ▸ hJ.1
  have hJ' : IsTwoComponentIn J (normalizer (zpowers a : Set G)) := hNC ▸ hJ
  have hP : IsPComponent 2 (J.subgroupOf (normalizer (zpowers a : Set G))) :=
    (isTwoComponentIn_iff hJN).mp hJ'
  have hT : IsPGroup 2 ((zpowers a).map e.toMonoidHom) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])).map _
  let f := CatalogueBAlternating.normalizerEquiv e (zpowers a)
  set L := (J.subgroupOf (normalizer (zpowers a : Set G))).map f.toMonoidHom with hL
  have hLp : IsPComponent 2 L := isPComponent_map_mulEquiv f hP
  obtain ⟨h5, heq, -⟩ := CatalogueBAlternating.between_normalizer_pComponent K hK 2
    ((zpowers a).map e.toMonoidHom) hT L hLp
  have : IsSimpleGroup (alternatingGroup (MulAction.fixedPoints
      ((zpowers a).map e.toMonoidHom) (Fin n))) := alternatingGroup.isSimpleGroup h5
  let g := K.subtype.comp
    (normalizer (((zpowers a).map e.toMonoidHom : Subgroup K) : Set K)).subtype
  have hg : Function.Injective g := K.subtype_injective.comp (Subgroup.subtype_injective _)
  let eL : ↥L ≃* ↥(alternatingGroup (MulAction.fixedPoints
      ((zpowers a).map e.toMonoidHom) (Fin n))) :=
    ((L.equivMapOfInjective g hg).trans (MulEquiv.subgroupCongr heq)).trans
      ((alternatingGroup _).equivMapOfInjective _ Equiv.Perm.ofSubtype_injective).symm
  let eJ : ↥J ≃* ↥L := (subgroupOfEquivOfLe hJN).symm.trans
    ((J.subgroupOf (normalizer (zpowers a : Set G))).equivMapOfInjective _ f.injective)
  have : IsSimpleGroup ↥J := (eJ.trans eL).isSimpleGroup
  exact pPrimeCore_eq_bot_of_isSimpleGroup hJ.2.2

end CFSG.ComponentClassification.HarrisLit.C9
