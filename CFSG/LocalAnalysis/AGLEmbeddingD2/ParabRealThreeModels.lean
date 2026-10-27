module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabRealThree
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbeddingD2.ParabRealThree

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub

@[expose] def RealThreeIn {Y : Type*} [Group Y] (J : Subgroup Y) : Prop :=
  ∃ g ∈ J, g ^ 3 = 1 ∧ g ≠ 1 ∧ ∃ w ∈ J, w * g * w⁻¹ = g⁻¹

@[expose] def RealThreeOver (Y : Type*) [Group Y] : Prop :=
  ∀ (T : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J →
    J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y) → RealThreeIn J

section SL

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem

variable {m : ℕ} {F : Type} [Field F]

theorem realThreeOver_sl_psl [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* Y) : RealThreeOver Y :=
  fun T J hNJ hJ => BorelQuotient.exists_real_three (borelQuotient_sl e)
    (fun i => HasSL2Node.hasRealOrderThree (hasSL2Node_sl i)) T J hNJ hJ

end SL

theorem realThreeOver_sl {Y : Type} [Group Y] [Finite Y] (r : ℕ) (q : TauCeti.PrimePower)
    (hq : q.p = 2) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A r q, hv⟩) :
    RealThreeOver Y := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  exact realThreeOver_sl_psl
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans e.symm)

section Sp

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

theorem realThreeOver_sp [Finite F] [CharP F 2] {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSp n F)) : RealThreeOver Y :=
  fun T J hNJ hJ => BorelQuotient.exists_real_three (borelQuotient_sp e)
    (fun i => HasSL2Node.hasRealOrderThree (hasSL2Node_sp i)) T J hNJ hJ

end Sp

theorem realThreeOver_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) : RealThreeOver Y := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact realThreeOver_sp e

section Last

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
  {k : Fin (n / 2)}

theorem hasRealOrderThree_su_last (hk : ¬k.val + 1 < n / 2) :
    ∃ x ∈ rootGroup σ hσ n (Pi.single k 1), ∃ y ∈ rootGroup σ hσ n (-Pi.single k 1),
      x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ (x * y) ^ 3 = 1 ∧ ∃ c : SU σ n, x * y * c ≠ c * (x * y) := by
  have h11 : (1 : F) ∈ traceZero σ := by
    rw [mem_traceZero, map_one]
    exact CharTwo.add_self_eq_zero 1
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hp : lowIdx k ≠ Fin.rev (lowIdx k) := lowIdx_ne_rev k k
  have hp' := rev_ne_rev_rev hp
  obtain ⟨hxm, hym⟩ := longRootHom_mem_last hσ hk (Multiplicative.ofAdd ⟨1, h11⟩)
  set p : Fin n := lowIdx k with hpdef
  set x : SU σ n := longRootHom σ hp (Multiplicative.ofAdd ⟨1, h11⟩) with hx
  set y : SU σ n := longRootHom σ hp' (Multiplicative.ofAdd ⟨1, h11⟩) with hy
  set a : Matrix (Fin n) (Fin n) F := Matrix.single p (Fin.rev p) 1 with ha
  set b : Matrix (Fin n) (Fin n) F := Matrix.single (Fin.rev p) p 1 with hb
  have hxmat : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + a := rfl
  have hymat : ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + b := by
    change 1 + Matrix.single (Fin.rev p) (Fin.rev (Fin.rev p)) 1 = _
    rw [Fin.rev_rev]
  have hrp : Fin.rev p ≠ p := hp.symm
  have ha2 : a + a = 0 := by
    rw [ha, ← Matrix.single_add, h2, Matrix.single_zero]
  have hb2 : b + b = 0 := by
    rw [hb, ← Matrix.single_add, h2, Matrix.single_zero]
  have haa : a * a = 0 := by
    rw [ha]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hrp _
  have hbb : b * b = 0 := by
    rw [hb]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hp _
  have hab : a * b = Matrix.single p p 1 := by
    rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have hba : b * a = Matrix.single (Fin.rev p) (Fin.rev p) 1 := by
    rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have haba : a * b * a = a := by
    rw [hab, ha, Matrix.single_mul_single_same, mul_one]
  have hbab : b * a * b = b := by
    rw [hba, hb, Matrix.single_mul_single_same, mul_one]
  obtain ⟨hx2, hy2, hbraid, hxyx⟩ := braid_of_rels ha2 hb2 haa hbb haba hbab
  have hx2' : x * x = 1 :=
    Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul, hxmat]; exact hx2))
  have hy2' : y * y = 1 :=
    Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul, hymat]; exact hy2))
  have hbraid' : x * y * x = y * x * y :=
    Subtype.ext (Units.ext (by
      simp only [Subgroup.coe_mul, Units.val_mul, hxmat, hymat]
      exact hbraid))
  refine ⟨x, hxm, y, hym, by rw [sq]; exact hx2', by rw [sq]; exact hy2',
    cube_eq_one_of_braid hx2' hy2' hbraid', x, fun h => ?_⟩
  have h' := congrArg (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul, hxmat, hymat] at h'
  rw [hxyx, ← mul_assoc, hx2, one_mul] at h'
  have h'' := congrFun (congrFun h' p) p
  simp [ha, hb, hrp, h2] at h''

end Last

section Unitary

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem hasRealOrderThree_su (i : Fin (n / 2)) : HasRealOrderThree (rootDatum hF n) i := by
  by_cases hk : i.val + 1 < n / 2
  · exact HasSL2Node.hasRealOrderThree (hasSL2Node_su_short hF hk)
  · obtain ⟨x, hx, y, hy, hx2, hy2, h3, c, hc⟩ :=
      hasRealOrderThree_su_last (unitaryInvolution_involutive hF) hk
    exact ⟨x, hx, y, hy, hx2, hy2, h3, c, hc⟩

include hF in
theorem realThreeOver_su (hn : 2 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) : RealThreeOver Y := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  exact fun T J hNJ hJ => BorelQuotient.exists_real_three (borelQuotient_su hF hn ζ hζ e)
    (fun i => hasRealOrderThree_su hF i) T J hNJ hJ

end Unitary

theorem realThreeOver_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) : RealThreeOver Y := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact realThreeOver_su hcard (by omega) e

section Plus

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem realThreeOver_spinPlus (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) : RealThreeOver Y := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact fun T J hNJ hJ => BorelQuotient.exists_real_three (borelQuotient_spinPlus hn e)
    (fun i => HasSL2Node.hasRealOrderThree (hasSL2Node_spinPlus hn i)) T J hNJ hJ

end Plus

theorem realThreeOver_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) : RealThreeOver Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact realThreeOver_spinPlus (by omega) e

section Minus

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem hasRealOrderThree_spinMinus_short {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    HasRealOrderThree (minusDatum n hirr) k := by
  have := fact_shortField hirr
  have h2 : (1 : ShortField b c) + 1 = 0 := by
    have h := congrArg (algebraMap F (ShortField b c)) (CharTwo.add_self_eq_zero (1 : F))
    simpa using h
  obtain ⟨hx2, hy2, hbraid⟩ := braid_of_rankOneRels h2 (shortRels n hirr k)
  refine HasRealOrderThree.of_involutions (minusDatum_steinbergExtras n hirr)
    (x := (shortRels n hirr k).x 1) (y := (shortRels n hirr k).y 1)
    ((mem_minusRootGroup_single_iff hirr hk _).2 ⟨1, rfl⟩)
    ((mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨1, rfl⟩) (fun h => ?_) hx2 hy2 hbraid
  have h0 : (shortRels n hirr k).x 0 = 1 := RankOneRels.x_zero _
  exact one_ne_zero (shortRels_x_injective hirr k (h.trans h0.symm))

include hirr in
theorem hasRealOrderThree_spinMinus (i : Fin (n - 1)) :
    HasRealOrderThree (minusDatum n hirr) i := by
  by_cases hk : i.val + 1 < n - 1
  · exact HasSL2Node.hasRealOrderThree (hasSL2Node_spinMinus_long hirr hk)
  · exact hasRealOrderThree_spinMinus_short hirr hk

include hirr in
theorem realThreeOver_spinMinus (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) : RealThreeOver Y := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact fun T J hNJ hJ => BorelQuotient.exists_real_three (borelQuotient_spinMinus hirr hn e)
    (fun i => hasRealOrderThree_spinMinus hirr i) T J hNJ hJ

end Minus

theorem realThreeOver_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) : RealThreeOver Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact realThreeOver_spinMinus hirr (by omega) e

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal

variable {K : Type} [Field K] [Finite K]

theorem realThreeOver_g2 [CharP K 2] {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* AdjointQuotient .G2 K) : RealThreeOver Y :=
  fun T J hNJ hJ => BorelQuotient.exists_real_three (borelQuotient_g2 e)
    (fun i => HasSL2Node.hasRealOrderThree (hasSL2Node_g2 i)) T J hNJ hJ

end G2

section Catalog


theorem realThreeOver_lieIndex {Y : Type} [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbedding.IsClassicalOrG2Index d.1) (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    RealThreeOver Y := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact realThreeOver_sl r q hd hv e
  | twistedA r q =>
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    change q.p = 2 at hd
    rw [hd] at h
    exact realThreeOver_of_model_psu h
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact realThreeOver_of_model_psp h
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact realThreeOver_of_model_psp h
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact realThreeOver_of_model_pomegaPlus h
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact realThreeOver_of_model_pomegaMinus h
  | G2 q =>
    change q.p = 2 at hd
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd
      (GaloisField q.p q.exponent) hK
    exact realThreeOver_g2 (e.trans b.symm)
  | _ => exact hd.elim

end Catalog

end CFSG.AGLEmbeddingD2.ParabRealThree
