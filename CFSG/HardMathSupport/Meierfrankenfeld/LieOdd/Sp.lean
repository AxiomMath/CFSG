module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpModel
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpDim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpArith
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderOrder
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator

theorem lt_of_psp {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥) (hel : IsElemAbelian2 E)
    {K : Type} [Field K] [Finite K] {p e r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (hr : 2 ≤ r) (he : 1 ≤ e) (hcenter : Subgroup.center ↥L = ⊥)
    (θ : ↥L ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r K))
    (h2 : ¬ (r = 2 ∧ p ^ e ≤ 7)) (h3 : ¬ (r = 3 ∧ p ^ e = 3)) (h4 : ¬ (r = 4 ∧ p ^ e = 3)) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have : CharP K p := charP_of_card_eq_prime_pow hKcard
  have hdim := two_pow_le_card_of_pspn hW hp2 hK (by omega) θ
  have hord := card_sup_le_of_pspn hW hp2 hK hr hirr hcenter θ hEN hel
  have harith := card_aut_pspn_lt hp2 hr he h2 h3 h4
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hord).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noIrrFFOffender_lie_C {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.C r q).Valid)
    (h3 : ¬ (r = 3 ∧ q.card = 3)) (h4 : ¬ (r = 4 ∧ q.card = 3)) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.C r q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨hr3, hp2⟩ := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨hcenter, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_psp_model_of_lie_C hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv e
  refine lt_of_psp hW hq hirr hEN hE hel hp2 hK (by omega) q.exponent_pos hcenter θ
    (by omega) (fun h => h3 ⟨h.1, by simpa [PrimePower.card_def] using h.2⟩)
    (fun h => h4 ⟨h.1, by simpa [PrimePower.card_def] using h.2⟩)

theorem noIrrFFOffender_lie_B2 {q : PrimePower} (hv : (LieTypeIndex.B 2 q).Valid)
    (hp2 : q.p ≠ 2) (hq9 : 9 ≤ q.card) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨hcenter, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_psp_model_of_lie_B2 hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv e hp2
      (by omega)
  have hq9' : 9 ≤ q.p ^ q.exponent := by simpa [PrimePower.card_def] using hq9
  exact lt_of_psp hW hq hirr hEN hE hel hp2 hK le_rfl q.exponent_pos hcenter θ
    (fun h => by omega) (fun h => by omega) (fun h => by omega)

theorem noFFModule_lie_C (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower} (hd : d.1 = .C r q)
    (h3 : ¬ (r = 3 ∧ q.card = 3)) (h4 : ¬ (r = 4 ∧ q.card = 3)) :
    NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_C hv h3 h4)

theorem noFFModule_lie_B2 (d : ValidLieTypeIndex) {q : PrimePower} (hd : d.1 = .B 2 q)
    (hp2 : q.p ≠ 2) (hq9 : 9 ≤ q.card) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_B2 hv hp2 hq9)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
