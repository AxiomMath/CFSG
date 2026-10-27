module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInvHub
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbedding.ParabHub.ParabThreeInv

open CFSG.Assembly.LowTwoRank

section SL

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem

theorem invThree_sl {Y : Type} [Group Y] [Finite Y] (r : ℕ) (q : TauCeti.PrimePower)
    (hq : q.p = 2) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : Y ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A r q, hv⟩) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  exact invThree_sl_psl ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans
    e.symm) T J hNJ hJ

end SL

section Sp

open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem TauCeti.GLSymplecticFin

theorem invThree_of_model_psp {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact BorelQuotient.invThree (borelQuotient_sp e)
    (fun i => HasSL2Node.hasInvolThree (hasSL2Node_sp i)) T J hNJ hJ

end Sp

section SpinPlus

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

theorem invThree_of_model_pomegaPlus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  exact BorelQuotient.invThree (borelQuotient_spinPlus hn3 e)
    (fun i => HasSL2Node.hasInvolThree (hasSL2Node_spinPlus hn3 i)) T J hNJ hJ

end SpinPlus

section SpinMinus

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem hasInvolThree_spinMinus (i : Fin (n - 1)) : HasInvolThree (minusDatum n hirr) i := by
  by_cases hk : i.val + 1 < n - 1
  · exact HasSL2Node.hasInvolThree (hasSL2Node_spinMinus_long hirr hk)
  · have := fact_shortField hirr
    have h2 : (1 : ShortField b c) + 1 = 0 := by
      have h := congrArg (algebraMap F (ShortField b c)) (CharTwo.add_self_eq_zero (1 : F))
      simpa using h
    obtain ⟨hx2, hy2, hbraid⟩ := braid_of_rankOneRels h2 (shortRels n hirr i)
    refine HasInvolThree.of_involutions (minusDatum_steinbergExtras n hirr)
      (x := (shortRels n hirr i).x 1) (y := (shortRels n hirr i).y 1)
      ((mem_minusRootGroup_single_iff hirr hk _).2 ⟨1, rfl⟩)
      ((mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨1, rfl⟩) (fun h => ?_) hx2 hy2 hbraid
    have h0 : (shortRels n hirr i).x 0 = 1 := RankOneRels.x_zero _
    exact one_ne_zero (shortRels_x_injective hirr i (h.trans h0.symm))

end SpinMinus

section SpinMinusModel

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

theorem invThree_of_model_pomegaMinus {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact BorelQuotient.invThree (borelQuotient_spinMinus hirr (by omega) e)
    (fun i => hasInvolThree_spinMinus hirr i) T J hNJ hJ

end SpinMinusModel

section SULast

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
  {k : Fin (n / 2)}

theorem hasInvolThree_su_last (hk : ¬k.val + 1 < n / 2) :
    ∃ x ∈ rootGroup σ hσ n (Pi.single k 1), ∃ y ∈ rootGroup σ hσ n (-Pi.single k 1),
      x * x = 1 ∧ y * y = 1 ∧ (x * y) ^ 3 = 1 ∧ ∃ c : SU σ n, x * y * c ≠ c * (x * y) := by
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
  refine ⟨x, hxm, y, hym, hx2', hy2', cube_eq_one_of_braid hx2' hy2' hbraid', x, fun h => ?_⟩
  have h' := congrArg (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul, hxmat, hymat] at h'
  rw [hxyx, ← mul_assoc, hx2, one_mul] at h'
  have h'' := congrFun (congrFun h' p) p
  simp [ha, hb, hrp, h2] at h''

end SULast

section SU

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

include hF in
theorem hasInvolThree_su (i : Fin (n / 2)) : HasInvolThree (rootDatum hF n) i := by
  by_cases hk : i.val + 1 < n / 2
  · exact HasSL2Node.hasInvolThree (hasSL2Node_su_short hF hk)
  · obtain ⟨x, hx, y, hy, hx2, hy2, h3, c, hc⟩ :=
      hasInvolThree_su_last (unitaryInvolution_involutive hF) hk
    exact ⟨x, hx, y, hy, hx2, hy2, h3, c, hc⟩

end SU

theorem invThree_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
  exact BorelQuotient.invThree (borelQuotient_su hcard (by omega) ζ hζ e)
    (fun i => hasInvolThree_su hcard i) T J hNJ hJ

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.RootSystem

variable {K : Type} [Field K] [Finite K]

theorem invThree_g2 [CharP K 2] {Y : Type} [Group Y] [Finite Y] (e : Y ≃* AdjointQuotient .G2 K)
    (T : Sylow 2 Y) (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : InvThree J :=
  BorelQuotient.invThree (borelQuotient_g2 e)
    (fun i => HasSL2Node.hasInvolThree (hasSL2Node_g2 i)) T J hNJ hJ

end G2

end CFSG.AGLEmbedding.ParabHub.ParabThreeInv
