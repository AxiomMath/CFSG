module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthDim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthArith
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

theorem lt_of_pomega {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥) (hel : IsElemAbelian2 E)
    {p e n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (hn : 7 ≤ n)
    (hord : Nat.card ↥(L ⊔ E) ≤ 96 * p ^ (e * (n * (n - 1) / 2)) * e)
    (hdim : 2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) * p ^ (e * (n - 4)) / (p - 1))) ≤
      Nat.card W) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have harith := card_aut_pomega_lt hp2 he hn
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hord).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem dim_exponent_eq {K : Type} [Finite K] {p e : ℕ} (hK : Nat.card K = p ^ e) (k : ℕ) :
    (Nat.card K - 1) * Nat.card K ^ k / (p - 1) = (p ^ e - 1) * p ^ (e * k) / (p - 1) := by
  rw [hK, ← pow_mul]

theorem noIrrFFOffender_lie_B {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid)
    (hp2 : q.p ≠ 2) (hr : 3 ≤ r) (h73 : ¬ (r = 3 ∧ q.card = 3)) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hcenter, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_pomega_model_of_lie_B hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2 hr
      h73 e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card q.prime_p hp2 hK
  have hord := card_sup_le_of_pomegaOdd hW hq.1 hirr hcenter hEN hel q.prime_p hp2
    q.exponent_pos hK hr (n := 2 * r + 1) rfl θ
  have hdim := two_pow_le_card_of_pomega hW hp2 (coe_quadOdd r K)
    (nondegenerate_polarBilin_quadOdd r K h2) (commutator_orthogonalGroup_quadOdd h2 hr)
    (oddPair_orth (K := K) (i := (⟨0, by omega⟩ : Fin r)) (j := ⟨1, by omega⟩)
      (by simp [Fin.ext_iff]))
    (oddPair_orth (K := K) (i := (⟨0, by omega⟩ : Fin r)) (j := ⟨2, by omega⟩)
      (by simp [Fin.ext_iff]))
    (oddPair_orth (K := K) (i := (⟨1, by omega⟩ : Fin r)) (j := ⟨2, by omega⟩)
      (by simp [Fin.ext_iff])) θ
  rw [dim_exponent_eq hK, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit, show r + (r + 1) = 2 * r + 1 by ring] at hdim
  exact lt_of_pomega hW hq hirr hEN hE hel hp2 q.exponent_pos (by omega) hord hdim

theorem noIrrFFOffender_lie_D {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.D r q).Valid)
    (hp2 : q.p ≠ 2) : NoIrrFFOffender (CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hcenter, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_pomega_model_of_lie_D hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2 e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hord := card_sup_le_of_pomegaPlus hW hq.1 hirr hcenter hEN hel q.prime_p hp2
    q.exponent_pos hK hr (n := 2 * r) rfl θ
  have hdim := two_pow_le_card_of_pomega hW hp2 (coe_quadPlus r K)
    (nondegenerate_polarBilin_quadPlus r K) (commutator_orthogonalGroup_quadPlus (by omega))
    (plusPair_orth (K := K) (i := (⟨0, by omega⟩ : Fin r)) (j := ⟨1, by omega⟩)
      (by simp [Fin.ext_iff]))
    (plusPair_orth (K := K) (i := (⟨0, by omega⟩ : Fin r)) (j := ⟨2, by omega⟩)
      (by simp [Fin.ext_iff]))
    (plusPair_orth (K := K) (i := (⟨1, by omega⟩ : Fin r)) (j := ⟨2, by omega⟩)
      (by simp [Fin.ext_iff])) θ
  rw [dim_exponent_eq hK, Fintype.card_sum, Fintype.card_fin, show r + r = 2 * r by ring] at hdim
  exact lt_of_pomega hW hq hirr hEN hE hel hp2 q.exponent_pos (by omega) hord hdim

theorem noIrrFFOffender_lie_twistedD {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedD r q).Valid) (hp2 : q.p ≠ 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hcenter, K, _, _, b, c, hbc, hK, ⟨θ⟩⟩ :=
    exists_pomega_model_of_lie_twistedD hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv
      hp2 e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hord := card_sup_le_of_pomegaMinus hW hq.1 hirr hcenter hEN hel q.prime_p hp2
    q.exponent_pos hK hr (n := 2 * r) rfl hbc θ
  have hdim := two_pow_le_card_of_pomega hW hp2 (coe_quadMinus r K b c)
    (nondegenerate_polarBilin_quadMinus_of_finite r K hbc)
    (commutator_orthogonalGroup_quadMinus hr hbc)
    (minusPair_orth (K := K) (b := b) (c := c) (i := (⟨0, by omega⟩ : Fin (r - 1)))
      (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (minusPair_orth (K := K) (b := b) (c := c) (i := (⟨0, by omega⟩ : Fin (r - 1)))
      (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff]))
    (minusPair_orth (K := K) (b := b) (c := c) (i := (⟨1, by omega⟩ : Fin (r - 1)))
      (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff])) θ
  rw [dim_exponent_eq hK, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, show r - 1 + (r - 1 + 2) = 2 * r by omega] at hdim
  exact lt_of_pomega hW hq hirr hEN hE hel hp2 q.exponent_pos (by omega) hord hdim

theorem noFFModule_lie_B (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower} (hd : d.1 = .B r q)
    (hp2 : q.p ≠ 2) (hr : 3 ≤ r) (h73 : ¬ (r = 3 ∧ q.card = 3)) :
    NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_B hv hp2 hr h73)

theorem noFFModule_lie_D (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower} (hd : d.1 = .D r q)
    (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_D hv hp2)

theorem noFFModule_lie_twistedD (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower}
    (hd : d.1 = .twistedD r q) (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_twistedD hv hp2)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
