module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3EvenModel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem f1For_of_A5 (K : Type) [Group K] [Finite K]
    (e : Nonempty (K ≃* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group)) : F1For K := by
  intro _ _ _ _ A W Y _ _ _ _ hY _ S _ _
  exfalso
  obtain ⟨e⟩ := e
  have hK : Nat.card K = 60 := by
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (alternatingGroup (Fin 5)) = 60
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have h168 : 168 ∣ Nat.card Y := by
    rw [← isLThreeTwo_card_eq hY]
    exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y))
  have hYK : Nat.card Y ∣ Nat.card K := Subgroup.card_subgroup_dvd_card Y
  rw [hK] at hYK
  have := Nat.le_of_dvd (by norm_num) (h168.trans hYK)
  omega

section J1Proof

set_option linter.unusedSectionVars false


theorem f1For_of_card_175560 (K : Type) [Group K] [Finite K] (hK : Nat.card K = 175560) :
    F1For K := by
  intro hsimp hnab _ _ A W Y _ _ _ _ hY _ S _ _
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


theorem f1J1_proved :
    ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) → F1For K := by
  intro K _ _ ⟨e⟩
  refine f1For_of_card_175560 K ?_
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  rw [Nat.card_congr e.toEquiv]
  show Nat.card TauCeti.SporadicName.J1.Group = 175560
  rw [← Nat.card_congr f.toEquiv]
  exact CFSG.Sporadic.J1.card_J1

end J1Proof

section L2Proof

set_option linter.unusedSectionVars false

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer
  CFSG.BenderSuzuki.MatrixGroups CFSG.Models CFSG.Assembly.LowTwoRank


theorem f1L2_proved :
    ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      q.p ≠ 3 → d.1 = .A 1 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → F1For K := by
  intro K _ _ d q hq hd ⟨e2⟩ _ _ _ hcyc A W Y hA hNW hYW hAY hY hWtop S _ _
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hmodel :=
    ThreeRankCls.statedClassical_of_lieModel (by omega) (lieModel_A 1 q hv e2)
  obtain ⟨-, F, instF, instFin, hF, ⟨eF⟩⟩ := hmodel
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e3 : K ≃* PSL2MatrixGroup F :=
    eF.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W := by
    intro hW
    exact not_isPSolvable_of_isLThreeTwo hY
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hW hYW)
  have htop := overgroupEqTop_of_mulEquiv e3
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.overgroupEqTop_psl2 hF hq) hcyc A W hA hNW
    hWns
  exact absurd htop hWtop

end L2Proof

section U3EvenProof

open CFSG.Assembly.LowTwoRank CFSG.Models TauCeti

theorem f1For_of_twistedA_even (K : Type) [Group K] [Finite K]
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hq2 : q.p = 2)
    (hq3 : q.card % 3 = 1) (hd : d.1 = .twistedA 2 q)
    (e : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) : F1For K := by
  intro _ _ _ _ A W Y _ _ _ _ hY _ S _ _
  exfalso
  obtain ⟨e⟩ := e
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 q.p q.exponent := by
    have := statedClassicalModel_of_lieModel' (by omega) (lieModel_twistedA 2 q hv e)
    rwa [hc, hf] at this
  rw [hq2] at hmodel
  have hcard : q.card = 2 ^ q.exponent := by
    have := TauCeti.PrimePower.card_def q
    rwa [hq2] at this
  have hm : 2 ≤ q.exponent := by
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [h1, pow_one] at hcard
    omega
  obtain ⟨e'⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hm hmodel
  have : Finite (PSU3 2 q.exponent) := Finite.of_equiv K e'.toEquiv
  have hB := (bender_psu3_borel_full q.exponent hm).map_mulEquiv e'.symm
  exact not_isLThreeTwo_of_stronglyEmbedded (fun Q => (hB Q).1) Y hY

theorem f1U3Even_proved :
    ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      q.p = 2 → q.card % 3 = 1 → d.1 = .twistedA 2 q →
        Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → F1For K := by
  intro K _ _ d q hq2 hq3 hd e
  exact f1For_of_twistedA_even K d q hq2 hq3 hd e

end U3EvenProof

section L3EvenProof

set_option linter.unusedSectionVars false

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

variable {F : Type} [Field F] [Finite F]

theorem f1Core_SL3_even (hq : Nat.card F % 3 = 2) (hF : 2 ∣ Nat.card F) : F1Core (SL3 F) := by
  refine f1Core_of_A0 card_A0 ?_
  intro W Y hNW hYW hAY hY hWtop S hS hSW
  exfalso
  apply hWtop
  have hroot := sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
        lev X ∈ W :=
    fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | htr
  · exact (false_of_le_P1_of_isLThreeTwo hF (hYW.trans h) hY).elim
  · exact (false_of_le_P2_of_isLThreeTwo hF (hYW.trans h) hY).elim
  · have hlevY : ∀ X : GL (Fin 2) F,
        (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
          lev X ∈ W ⊓ P1 :=
      fun X hX => ⟨hlev X hX, lev_mem_P1 X⟩
    rcases inf_Q1_eq_bot_or_le hroot hcube hlevY with hb | hle
    · exact (false_of_transitive_of_isLThreeTwo hF hYW htr hb hY).elim
    · exact eq_top_of_Q1_le_of_transitive htr (hle.trans inf_le_left)

end L3EvenProof

section L3EvenFamily

set_option linter.unusedSectionVars false

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

theorem f1L3Even_proved :
    ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      q.p = 2 → q.card % 3 = 2 → d.1 = .A 2 q →
        Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → F1For K := by
  intro K _ _ d q hq2 hq hd ⟨e⟩
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set F := GaloisField q.p q.exponent
  have hF : Nat.card F = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def]
  have hqF : Nat.card F % 3 = 2 := by rw [hF]; exact hq
  have hFeven : 2 ∣ Nat.card F := by
    rw [hF, TauCeti.PrimePower.card_def, hq2]
    exact dvd_pow_self 2 q.exponent_pos.ne'
  exact f1For_of_core
    ((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans (pslEquivSL3 hqF))
    (f1Core_SL3_even hqF hFeven)

end L3EvenFamily

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
