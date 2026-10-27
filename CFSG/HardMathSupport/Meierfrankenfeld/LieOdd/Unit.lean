module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitModel
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitDim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitArith
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_mulAut_eq_mul_card_outer {S : Type} [Group S] [Finite S]
    (hS : Subgroup.center S = ⊥) :
    Nat.card (MulAut S) = Nat.card S * Nat.card (Outer S) := by
  have : Finite (MulAut S) :=
    Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hc : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h := congrArg (fun φ : MulAut S => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc x * g = g * x * g⁻¹ * g := by rw [h]
        _ = g * x := by group
    rw [hS] at hc
    exact hc
  have h1 := Subgroup.card_mul_index (inner S)
  have h2 : Nat.card (inner S) = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← h1, h2]
  rfl

theorem card_sup_le_of_psu {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {K : Type} [Field K] [Finite K] {p e n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ e) ^ 2) (hn : 3 ≤ n)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (p ^ e) K))
    (hZn : Nat.card (Subgroup.center ↥L) ≤ n) :
    Nat.card ↥(L ⊔ E) ≤ 4 * n * e * (p ^ e) ^ (n ^ 2 - 1) := by
  set S := StatedProj (StatedSU n (p ^ e) K)
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have : Finite S := Finite.of_equiv _ θ.toEquiv
  have hS : Subgroup.center S = ⊥ := by
    have : Group.IsPerfect ↥L := hq.1
    have h0 := CFSG.AGLEmbedding.center_quotient_center_eq_bot_of_isPerfect
      (Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) :
        Group.IsPerfect (↥L ⧸ Subgroup.center ↥L))
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    have hs' : θ.symm s ∈ Subgroup.center (↥L ⧸ Subgroup.center ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply θ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hs (θ x)
    rw [h0, Subgroup.mem_bot] at hs'
    rw [← θ.apply_symm_apply s, hs', map_one]
  have hsup := FFToolkit.card_sup_le_of_outer hW hq.1 hirr hE hEel θ
    (k := Nat.card (Outer S)) (fun B _ _ => card_le_card_outer_mul_card_inf B)
  have hL : Nat.card ↥L = Nat.card (Subgroup.center ↥L) * Nat.card S := by
    rw [← Nat.card_congr θ.toEquiv, mul_comm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _)
  have hAut : Nat.card S * Nat.card (Outer S) ≤ 2 * e * (2 * (p ^ e) ^ (n ^ 2 - 1)) := by
    rw [← card_mulAut_eq_mul_card_outer hS]
    exact (card_mulAut_psu_le hp2 hK hn).trans
      (Nat.mul_le_mul_left _ (card_statedSU_le hK (by omega)))
  calc Nat.card ↥(L ⊔ E) ≤ Nat.card (Outer S) * Nat.card ↥L := hsup
    _ = Nat.card (Subgroup.center ↥L) * (Nat.card S * Nat.card (Outer S)) := by
        rw [hL]; ring
    _ ≤ n * (2 * e * (2 * (p ^ e) ^ (n ^ 2 - 1))) := Nat.mul_le_mul hZn hAut
    _ = 4 * n * e * (p ^ e) ^ (n ^ 2 - 1) := by ring

theorem noIrrFFOffender_lie_twistedA {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) (hp2 : q.p ≠ 2) (h3 : ¬ (r = 2 ∧ q.exponent = 1))
    (h4 : ¬ (r = 3 ∧ q.card = 3)) (h5 : ¬ (r = 4 ∧ q.card = 3)) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp : q.p.Prime := q.prime_p
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  obtain ⟨hZ, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_psu_model_of_lie_twistedA hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2
      h4 e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let π : ↥L →* StatedProj (StatedSU (r + 1) (q.p ^ q.exponent) K) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hZp : ¬ q.p ∣ Nat.card π.ker := by
    rw [hkerπ]
    intro hd
    have h1 : q.p ∣ q.p ^ q.exponent + 1 := hd.trans (hZ.trans (Nat.gcd_dvd_right _ _))
    have h2 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
  have hdim := two_pow_le_card_of_psun hW hp2 hK (by omega) π hπ hkerπ.le hZp
  have hZn : Nat.card (Subgroup.center ↥L) ≤ r + 1 :=
    Nat.le_of_dvd (by omega) (hZ.trans (Nat.gcd_dvd_left _ _))
  have hord := card_sup_le_of_psu hW hq hirr hEN hel hp2 hK (by omega) θ hZn
  have harith := card_aut_psun_lt hp2 q.exponent_pos (n := r + 1) (by omega)
    (fun h => h3 ⟨by omega, h.2⟩) (fun h => h4 ⟨by omega, by rw [hcard]; exact h.2⟩)
    (fun h => h5 ⟨by omega, by rw [hcard]; exact h.2⟩)
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hord).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_twistedA (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower}
    (hd : d.1 = .twistedA r q) (hp2 : q.p ≠ 2) (h3 : ¬ (r = 2 ∧ q.exponent = 1))
    (h4 : ¬ (r = 3 ∧ q.card = 3)) (h5 : ¬ (r = 4 ∧ q.card = 3)) :
    NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_twistedA hv hp2 h3 h4 h5)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
