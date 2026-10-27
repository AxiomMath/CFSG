module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInvFam
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabHub.ParabThreeInv

@[expose] def HasBorelModel (Y : Type) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* Y) (M : ℕ),
    BorelQuotient D n H π M ∧ ∀ i, HasInvolThree D i

set_option linter.unusedSectionVars false

section Models

open CFSG.LieType.Universal.Symplectic TauCeti.GLSymplecticFin
open CFSG.Assembly.LowTwoRank

theorem hasBorelModel_of_model_psp {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : HasBorelModel Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_sp e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_sp i)⟩

open CFSG.LieType.Universal.Spin in
theorem hasBorelModel_of_model_pomegaPlus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : HasBorelModel Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_spinPlus hn3 e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_spinPlus hn3 i)⟩

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted in
theorem hasBorelModel_of_model_pomegaMinus {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : HasBorelModel Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_spinMinus hirr (by omega) e,
    fun i => hasInvolThree_spinMinus hirr i⟩

theorem hasBorelModel_of_model_psu {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : HasBorelModel Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_su hcard (by omega) ζ hζ e,
    fun i => hasInvolThree_su hcard i⟩

end Models

theorem hasBorelModel_g2 {K : Type} [Field K] [Finite K] [CharP K 2] {Y : Type} [Group Y]
    (e : Y ≃* CFSG.Blueprint.AdjointQuotient .G2 K) : HasBorelModel Y :=
  ⟨_, inferInstance, inferInstance, _, _, _, _, _, borelQuotient_g2 e,
    fun i => HasSL2Node.hasInvolThree (hasSL2Node_g2 i)⟩

theorem hasBorelModel_lieIndex {Y : Type} [Group Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : HasBorelModel Y := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    exact ⟨_, inferInstance, inferInstance, _, _, _, _, _,
      borelQuotient_sl ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans
        e.symm), fun i => HasSL2Node.hasInvolThree (hasSL2Node_sl i)⟩
  | twistedA r q =>
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    change q.p = 2 at hd
    rw [hd] at h
    exact hasBorelModel_of_model_psu h
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact hasBorelModel_of_model_psp h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact hasBorelModel_of_model_psp h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact hasBorelModel_of_model_pomegaPlus h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact hasBorelModel_of_model_pomegaMinus h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact hasBorelModel_g2 (e.trans b.symm)
  | _ => exact hd.elim

theorem chevGen_of_hasBorelModel {W : Type} [Group W] [Finite W] {L S₀ : Subgroup W}
    (hL : Open.IsQuasisimple ↥L) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S₀ L)
    (h : HasBorelModel (↥L ⧸ Subgroup.center ↥L)) :
    ∃ Ps : Set (Subgroup W),
      (∀ P ∈ Ps, CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsMinOverBorel L S₀ P) ∧
      L = ⨆ P ∈ Ps, CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 2 P ∧
      ∀ P ∈ Ps, ∃ x ∈ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 2 P,
        orderOf x = 3 ∧ x ∉ (Subgroup.center ↥L).map L.subtype := by
  obtain ⟨K, _, _, D, n, H, π, M, hπ, h3⟩ := h
  obtain ⟨P, hmin, hgen, hord⟩ := chevGen_core hL hS hπ h3
  refine ⟨Set.range P, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hmin i
  · rw [hgen]
    refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun Q hQ => ?_)
    · exact le_iSup₂ (f := fun (Q : Subgroup W) (_ : Q ∈ Set.range P) =>
        CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 2 Q) (P i) ⟨i, rfl⟩
    · obtain ⟨i, rfl⟩ := hQ
      exact le_iSup (fun i => CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 2 (P i)) i
  · rintro _ ⟨i, rfl⟩
    exact hord i

theorem chevGen_lieIndex {W : Type} [Group W] [Finite W] {L S₀ : Subgroup W}
    (hL : Open.IsQuasisimple ↥L) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S₀ L)
    (d : TauCeti.ValidLieTypeIndex) (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ Ps : Set (Subgroup W),
      (∀ P ∈ Ps, CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsMinOverBorel L S₀ P) ∧
      L = ⨆ P ∈ Ps, CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 2 P ∧
      ∀ P ∈ Ps, ∃ x ∈ CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.pElementSubgroup 2 P,
        orderOf x = 3 ∧ x ∉ (Subgroup.center ↥L).map L.subtype :=
  chevGen_of_hasBorelModel hL hS (hasBorelModel_lieIndex d hd e)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
