module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyDefs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.Bridge.J1

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem hasDihedralSylowTwo_of_isLThreeTwo {X : Type} [Group X] [Finite X]
    (hX : IsLThreeTwo X) : CFSG.GorensteinWalter.HasDihedralSylowTwo X := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hX
  obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (CFSG.AGLEmbeddingD2.McLaughlin.isLinTwoIndex_seven_one hd)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField 7 1)) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, GaloisField.card 7 1 one_ne_zero⟩
  exact CFSG.ComponentClassification.OutcomeLocal.hasDihedralSylowTwo_of_mulEquiv (e.trans e2)
    (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (GaloisField 7 1) hodd)

section Main

set_option linter.unusedSectionVars false


theorem overgroupL32Odd_of_card (K : Type) [Group K] [Finite K] (hK : Nat.card K = 175560) :
    OvergroupL32Odd K := by
  intro hsimp hnab _ _ A W Y _ _ _ _ hY
  exfalso
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N2 : Subgroup ↥Y := CFSG.pCore 2 ↥Y with hN2def
  have hcard168 : Nat.card (↥Y ⧸ N2) = 168 := isLThreeTwo_card_eq hY
  have hdvd : Nat.card Y ∣ 175560 := hK ▸ Subgroup.card_subgroup_dvd_card Y
  have hmul : Nat.card Y = Nat.card (↥Y ⧸ N2) * Nat.card N2 :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N2
  have hN2card : Nat.card N2 = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [hN2def, hk, h0]; rfl
    · exfalso
      have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 hpos.ne'
      have : 168 * 2 ∣ 175560 := by
        rw [hmul, hcard168, show Nat.card N2 = 2 ^ k from hk] at hdvd
        exact (Nat.mul_dvd_mul_left 168 h2k).trans hdvd
      omega
  have hbot : N2 = ⊥ := Subgroup.eq_bot_of_card_eq N2 hN2card
  have hinj : Function.Injective (QuotientGroup.mk' N2) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]
  let e : ↥Y ≃* (↥Y ⧸ N2) :=
    MulEquiv.ofBijective (QuotientGroup.mk' N2) ⟨hinj, QuotientGroup.mk'_surjective N2⟩
  let S₀ : Sylow 2 (↥Y ⧸ N2) := default
  obtain ⟨m, -, ⟨φ⟩⟩ := hasDihedralSylowTwo_of_isLThreeTwo hY S₀
  have hfac : (168 : ℕ).factorization 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]; decide +kernel
  have hS₀ : Nat.card (S₀ : Subgroup (↥Y ⧸ N2)) = 8 := by
    rw [Sylow.card_eq_multiplicity, hcard168, hfac]; norm_num
  let T : Subgroup K := ((S₀ : Subgroup (↥Y ⧸ N2)).map e.symm.toMonoidHom).map Y.subtype
  let eT : (S₀ : Subgroup (↥Y ⧸ N2)) ≃* T :=
    ((S₀ : Subgroup (↥Y ⧸ N2)).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((S₀ : Subgroup (↥Y ⧸ N2)).map e.symm.toMonoidHom).equivMapOfInjective Y.subtype
        Y.subtype_injective)
  have hT : Nat.card T = 8 := by rw [← Nat.card_congr eT.toEquiv]; exact hS₀
  have hfacK : (175560 : ℕ).factorization 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]; decide +kernel
  have hTsyl : Nat.card T = 2 ^ (Nat.card K).factorization 2 := by
    rw [hT, hK, hfacK]; norm_num
  let P : Sylow 2 K := Sylow.ofCard T hTsyl
  have hP : (P : Subgroup K) = T := Sylow.coe_ofCard T hTsyl
  let eP : (P : Subgroup K) ≃* DihedralGroup (2 ^ m) :=
    ((MulEquiv.subgroupCongr hP).trans eT.symm).trans φ
  have := hsimp
  rcases CFSG.GorensteinWalter.gorenstein_walter K hnab P ⟨2 ^ m, ⟨eP⟩⟩ with
    ⟨⟨eA⟩⟩ | ⟨p, k, hpf, hpodd, h5, ⟨ePSL⟩⟩
  · have : Nat.card K = 2520 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    omega
  · have := hpf
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at h5
    have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
    have hoddF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p k)) :=
      ⟨p, k, hpf.out, hpodd, Nat.one_le_iff_ne_zero.mpr hk0, hcardF⟩
    have hform := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p k) hoddF
    have hK' : Nat.card K = p ^ k * ((p ^ k) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr ePSL.toEquiv, hform, hcardF]
    rw [hK] at hK'
    generalize p ^ k = q at h5 hK'
    by_cases hq72 : 72 ≤ q
    · have hle : 72 * (72 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hq72 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq72 2) 1)
      have := Nat.div_le_div_right (c := 2) hle
      omega
    · push Not at hq72
      interval_cases q <;> omega


theorem overgroupL32J1_proved : OvergroupL32J1 := by
  intro K _ _ ⟨e⟩
  refine overgroupL32Odd_of_card K ?_
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  rw [Nat.card_congr e.toEquiv]
  show Nat.card TauCeti.SporadicName.J1.Group = 175560
  rw [← Nat.card_congr f.toEquiv]
  exact CFSG.Sporadic.J1.card_J1

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
