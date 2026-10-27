module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517ChevGenQEng
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSU
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverModels
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInvFam
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517ChevGenQ

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabHub.ParabThreeInv CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

theorem hasQModel_of_sl2 {K Y : Type} [Group K] [Finite K] [Group Y] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}
    (h : BorelQuotient D n H π M) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : ∀ i, HasSL2Node D i F) : HasQModel Y (Nat.card F ^ 2 - 1) :=
  ⟨K, inferInstance, inferInstance, D, n, H, π, M, h, fun i => (hn i).hasInvolThree,
    fun i p hp hp2 hpd => oddNode_of_hasSL2Node (hn i) hp hp2 hpd⟩

section Models

open CFSG.LieType.Universal.Symplectic TauCeti.GLSymplecticFin
open CFSG.Assembly.LowTwoRank

theorem hasQModel_of_model_psp {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : HasQModel Y ((2 ^ f) ^ 2 - 1) := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have := hasQModel_of_sl2 (borelQuotient_sp e) (fun i => hasSL2Node_sp i)
  rwa [hcard] at this

open CFSG.LieType.Universal.Spin in
theorem hasQModel_of_model_pomegaPlus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : HasQModel Y ((2 ^ f) ^ 2 - 1) := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have := hasQModel_of_sl2 (borelQuotient_spinPlus hn3 e) (fun i => hasSL2Node_spinPlus hn3 i)
  rwa [hcard] at this

end Models

theorem card_eq_two_pow {q : TauCeti.PrimePower} (h : q.p = 2) : q.card = 2 ^ q.exponent := by
  rw [TauCeti.PrimePower.card_def, h]

theorem hasQModel_A (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (hq : q.p = 2) {Y : Type} [Group Y] (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    HasQModel Y (q.card ^ 2 - 1) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  have := hasQModel_of_sl2
    (borelQuotient_sl ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans
      e.symm)) (fun i => hasSL2Node_sl i)
  rwa [hK] at this

theorem hasQModel_B (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hq : q.p = 2) (hr : 2 ≤ r) {Y : Type} [Group Y]
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B r q, hv⟩) : HasQModel Y (q.card ^ 2 - 1) := by
  by_cases h2 : r = 2
  · subst h2
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    rw [hq] at h
    have := hasQModel_of_model_psp h
    rwa [← card_eq_two_pow hq] at this
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq
      (by omega) e
    rw [hq] at h
    have := hasQModel_of_model_psp h
    rwa [← card_eq_two_pow hq] at this

theorem hasQModel_D (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (hq : q.p = 2) {Y : Type} [Group Y]
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D r q, hv⟩) : HasQModel Y (q.card ^ 2 - 1) := by
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq e
  rw [hq] at h
  have := hasQModel_of_model_pomegaPlus h
  rwa [← card_eq_two_pow hq] at this

theorem sub_one_dvd_sq_sub_one (a : ℕ) : a - 1 ∣ a ^ 2 - 1 :=
  Nat.sub_one_dvd_pow_sub_one a 2

@[expose] def IsUntwistedIdx : TauCeti.LieTypeIndex → Prop
  | .A _ _ | .B _ _ | .D _ _ | .G2 _ => True
  | _ => False

@[expose] def IsTwistedIdx : TauCeti.LieTypeIndex → Prop
  | .twistedA _ _ | .twistedD _ _ => True
  | _ => False

theorem isUntwisted_or_isTwisted {d : TauCeti.LieTypeIndex} (h : IsRankTwoPlus d) :
    IsUntwistedIdx d ∨ IsTwistedIdx d := by
  cases d <;> first | exact Or.inl trivial | exact Or.inr trivial | exact h.elim

section TwistedA

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)

theorem oddNode_su_sq {n : ℕ} (hn : 3 ≤ n) (i : Fin (n / 2)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ∣ (2 ^ f) ^ 2 - 1) :
    OddNode (rankOne (rootDatum hF n).rootGroup i) p := by
  by_cases hk : i.val + 1 < n / 2
  · refine oddNode_of_hasSL2Node (hasSL2Node_su_short hF hk) hp hp2 ?_
    rw [hF]
    exact hpd.trans (sub_one_dvd_sq_sub_one _)
  · obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
    have hcard : Nat.card (fixedSubfield F 2 f) = 2 ^ f := card_fixedSubfield hF
    have hpd' : p ∣ Nat.card (fixedSubfield F 2 f) ^ 2 - 1 := by
      rw [hcard]
      exact hpd
    obtain ⟨w, m, hw, hw1, hm⟩ := exists_order_inverted_sl2 (F := fixedSubfield F 2 f) hp hp2 hpd'
    by_cases he : Even n
    · obtain ⟨e⟩ := nonempty_rankOne_last_even_mulEquiv hF he (by omega) hk
      exact oddNode_of_mulEquiv (e.trans (hypEquiv hζ0 hζ).symm) ⟨w, m, hw, hw1, hm⟩
    · obtain ⟨e⟩ := nonempty_rankOne_last_odd_mulEquiv hF he hn hk
      have hk' : ∀ c ∈ fixedSubfield F 2 f, unitaryInvolution F 2 f c = c := fun c hc =>
        mem_fixedSubfield.1 hc
      refine oddNode_of_mulEquiv e ⟨blk3Hom (fixedSubfield F 2 f) hk' w,
        blk3Hom (fixedSubfield F 2 f) hk' m, by rw [← map_pow, hw, map_one],
        fun h => hw1 (blk3Hom_injective (fixedSubfield F 2 f) hk' (by rw [h, map_one])), ?_⟩
      simpa [map_mul, map_inv] using congrArg (blk3Hom (fixedSubfield F 2 f) hk') hm

end TwistedA

open CFSG.Assembly.LowTwoRank in
theorem hasQModel_of_model_psu {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : HasQModel Y ((2 ^ f) ^ 2 - 1) := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_su hcard (by omega) ζ hζ e,
    fun i => hasInvolThree_su hcard i, fun i p hp hp2 hpd => oddNode_su_sq hcard hn i hp hp2 hpd⟩

theorem hasQModel_TA (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.p = 2) {Y : Type} [Group Y]
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    HasQModel Y (q.card ^ 2 - 1) := by
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hq] at h
  have := hasQModel_of_model_psu h
  rwa [← card_eq_two_pow hq] at this

section TwistedD

set_option linter.unusedSectionVars false


open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg.CentralExt CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.Assembly.LowTwoRank in
theorem hasQModel_of_model_pomegaMinus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : HasQModel Y ((2 ^ f) ^ 2 - 1) := by
  obtain ⟨⟨-, hf1, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  have hF2 : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  have h4 : 4 ≤ Nat.card (ShortField b c) := by
    rw [SpinMinusClosed.card_shortField]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hF2 2
  refine ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_spinMinus hirr (by omega) e,
    fun i => hasInvolThree_spinMinus hirr i, fun i p hp hp2 hpd => ?_⟩
  rw [← hcard] at hpd
  by_cases hk : i.val + 1 < n - 1
  · exact oddNode_of_hasSL2Node (hasSL2Node_spinMinus_long hirr hk) hp hp2 hpd
  · refine oddNode_of_hasSL2Node (hasSL2Node_spinMinus_short hirr h4 hk) hp hp2 ?_
    rw [SpinMinusClosed.card_shortField]
    exact hpd.trans (sub_one_dvd_sq_sub_one _)

theorem hasQModel_TD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hq : q.p = 2) {Y : Type} [Group Y]
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    HasQModel Y (q.card ^ 2 - 1) := by
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq e
  rw [hq] at h
  have := hasQModel_of_model_pomegaMinus h
  rwa [← card_eq_two_pow hq] at this

theorem hasQModel_twisted (d : TauCeti.ValidLieTypeIndex) (hd : IsRankTwoPlus d.1)
    (ht : IsTwistedIdx d.1) {Y : Type} [Group Y] (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    HasQModel Y (KFactsPair.indexQ d.1 ^ 2 - 1) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q => exact hasQModel_TA r q hv hd.1 e
  | twistedD r q => exact hasQModel_TD r q hv hd.1 e
  | _ => exact ht.elim

end TwistedD

section G2

set_option linter.unusedSectionVars false


theorem hasQModel_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Blueprint.AdjointQuotient .G2 K) : HasQModel Y (Nat.card K ^ 2 - 1) :=
  hasQModel_of_sl2 (borelQuotient_g2 e) (fun i => hasSL2Node_g2 i)

theorem hasQModel_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hq : q.p = 2) {Y : Type} [Group Y] (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    HasQModel Y (q.card ^ 2 - 1) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq
    (GaloisField q.p q.exponent) hK
  have := hasQModel_g2 (e.trans b.symm)
  rwa [hK] at this

theorem hasQModel_untwisted (d : TauCeti.ValidLieTypeIndex) (hd : IsRankTwoPlus d.1)
    (hu : IsUntwistedIdx d.1) {Y : Type} [Group Y] (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    HasQModel Y (KFactsPair.indexQ d.1 ^ 2 - 1) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact hasQModel_A r q hv hd.1 e
  | B r q => exact hasQModel_B r q hv hd.1 hd.2 e
  | D r q => exact hasQModel_D r q hv hd.1 e
  | G2 q => exact hasQModel_G2 q hv hd e
  | _ => exact hu.elim

end G2

end CFSG.LocalAnalysis.RankThreeUC.S15.K517ChevGenQ

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open K517ChevGenQ

section Twisted

set_option linter.unusedSectionVars false


theorem kFactChevGenQOn_twisted : KFactChevGenQOn IsTwistedIdx :=
  kFactChevGenQOn_of_models fun d hd ht _ _ e => hasQModel_twisted d hd ht e

end Twisted

section All

set_option linter.unusedSectionVars false


theorem kFactChevGenQOn_untwisted : KFactChevGenQOn IsUntwistedIdx :=
  kFactChevGenQOn_of_models fun d hd hu _ _ e => hasQModel_untwisted d hd hu e

theorem kFactChevGenQ_proved : KFactChevGenQ :=
  kFactChevGenQ_of_cases kFactChevGenQOn_untwisted kFactChevGenQOn_twisted
    fun _ h => isUntwisted_or_isTwisted h

theorem K517_4a_holds : K517_4a :=
  k517_4a_of_genQ kFactChevGenQ_proved

end All

end CFSG.LocalAnalysis.RankThreeUC.S15
