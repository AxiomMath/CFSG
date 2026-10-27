module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract

public section

namespace CFSG.AGLEmbedding

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_eq_mul_index (B Z : Subgroup G) (h : B ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card ↥(B ⊔ Z) = Nat.card Z * (Z.subgroupOf B).index := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e : ↥B ⧸ Z.subgroupOf B ≃* ↥(B ⊔ Z) ⧸ Z.subgroupOf (B ⊔ Z) :=
    QuotientGroup.quotientInfEquivProdNormalizerQuotient B Z h
  have h1 : (Z.subgroupOf (B ⊔ Z)).index = (Z.subgroupOf B).index :=
    (Nat.card_congr e.toEquiv).symm
  have h2 : Nat.card (Z.subgroupOf (B ⊔ Z)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h3 := Subgroup.card_mul_index (Z.subgroupOf (B ⊔ Z))
  rw [h1, h2] at h3
  exact h3.symm

theorem exists_conj_mem_of_card_dvd_two_pow {J H : Subgroup G} (hHJ : H ≤ J) {a : ℕ}
    (hdvd : Nat.card J ∣ 2 ^ a * Nat.card H) {U : Subgroup G} (hUJ : U ≤ J)
    (hU : IsPGroup 3 U) : ∃ g ∈ J, ∀ u ∈ U, g⁻¹ * u * g ∈ H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨PH⟩ : Nonempty (Sylow 3 H) := inferInstance
  set P : Subgroup G := (PH : Subgroup H).map H.subtype with hP
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hPJ : P ≤ J := hPH.trans hHJ
  have hcardP : Nat.card P = Nat.card (PH : Subgroup H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hP3 : IsPGroup 3 P := PH.isPGroup'.map _
  obtain ⟨b, hb⟩ := hP3.exists_card_eq
  have hidx : ¬ 3 ∣ (PH : Subgroup H).index := PH.not_dvd_index
  have hHcard : Nat.card H = 3 ^ b * (PH : Subgroup H).index := by
    rw [← hb, hcardP, Subgroup.card_mul_index]
  set P' : Subgroup J := P.subgroupOf J with hP'
  have hcardP' : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ).toEquiv
  have hJpos : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have hfac : Nat.card P' = 3 ^ (Nat.card J).factorization 3 := by
    rw [hcardP', hb]
    congr 1
    apply le_antisymm
    · rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hJpos, ← hb, ← hcardP']
      exact Subgroup.card_subgroup_dvd_card P'
    · have h1 : 3 ^ (Nat.card J).factorization 3 ∣ 2 ^ a * (PH : Subgroup H).index * 3 ^ b := by
        refine (Nat.ordProj_dvd _ _).trans (hdvd.trans ?_)
        rw [hHcard]
        exact dvd_of_eq (by ring)
      have h2 : Nat.Coprime (3 ^ (Nat.card J).factorization 3)
          (2 ^ a * (PH : Subgroup H).index) :=
        Nat.Coprime.pow_left _ (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hidx))
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (h2.dvd_of_dvd_mul_left h1)
  let Q : Sylow 3 J := Sylow.ofCard P' hfac
  have hU' : IsPGroup 3 (U.subgroupOf J) :=
    hU.of_injective (Subgroup.subgroupOfEquivOfLe hUJ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUJ).injective
  obtain ⟨Q', hQ'⟩ := hU'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J Q Q'
  refine ⟨g, g.2, fun u hu => hPH ?_⟩
  have hmem : (⟨u, hUJ hu⟩ : J) ∈ (Q' : Subgroup J) := hQ' hu
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  have h2 : ((MulAut.conj g)⁻¹ • (⟨u, hUJ hu⟩ : J) : J) = g⁻¹ * ⟨u, hUJ hu⟩ * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  have h3 : ((Q : Sylow 3 J) : Subgroup J) = P' := rfl
  rw [h2, h3, hP', Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

theorem le_of_isPGroup_three_of_normal {L R U : Subgroup G} (hRL : R ≤ L)
    (hR : L ≤ Subgroup.normalizer (R : Set G)) (hR3 : IsPGroup 3 R) {m : ℕ}
    (hm : Nat.Coprime 3 m) (hLR : Nat.card L = Nat.card R * m) (hUL : U ≤ L)
    (hU : IsPGroup 3 U) : U ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUR : U ⊔ R ≤ L := sup_le hUL hRL
  have hdvd := ParabPrime.card_sup_dvd_mul U R (hUL.trans hR)
  obtain ⟨i, hi⟩ := hU.exists_card_eq
  obtain ⟨j, hj⟩ := hR3.exists_card_eq
  rw [hi, hj, ← pow_add] at hdvd
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hl' : 3 ^ l ∣ 3 ^ j * m := by
    rw [← hl, ← hj, ← hLR]
    exact Subgroup.card_dvd_of_le hUR
  have hlj : l ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
    ((Nat.Coprime.pow_left l hm).dvd_of_dvd_mul_right hl')
  have heq : U ⊔ R = R := by
    refine (Subgroup.eq_of_le_of_card_ge le_sup_right ?_).symm
    rw [hl, hj]
    exact Nat.pow_le_pow_right (by norm_num) hlj
  exact le_sup_left.trans heq.le

end CFSG.AGLEmbedding
