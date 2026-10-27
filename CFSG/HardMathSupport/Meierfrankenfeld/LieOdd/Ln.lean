module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnModel
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnDim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnArith
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator

theorem noIrrFFOffender_lie_A {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    (hp : q.p ≠ 2) (hr : 2 ≤ r) (h31 : ¬ (r = 2 ∧ q.exponent = 1)) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.A r q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hperf : Group.IsPerfect ↥L := hq.1
  obtain ⟨hZdvd, K, _, _, hK, ⟨eL⟩⟩ := exists_psln_model_of_lie_A hperf hv e hp hr
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = q.p ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have : CharP K q.p := charP_of_card_eq_prime_pow hKcard
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hZodd := FFToolkit.odd_card_center_of_isIrrOn hW hirr
  have hzn : Nat.card (Subgroup.center ↥L) ∣ r + 1 := hZdvd.trans (Nat.gcd_dvd_left _ _)
  have hzp : ¬ q.p ∣ Nat.card (Subgroup.center ↥L) := by
    intro h
    have h1 : q.p ∣ q.p ^ q.exponent - 1 := h.trans (hZdvd.trans (Nat.gcd_dvd_right _ _))
    have h2 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    have h3 : 1 ≤ q.p ^ q.exponent := Nat.one_le_pow _ _ q.prime_p.pos
    have h4 : q.p ∣ q.p ^ q.exponent - (q.p ^ q.exponent - 1) := Nat.dvd_sub h2 h1
    rw [Nat.sub_sub_self h3] at h4
    exact q.prime_p.one_lt.ne' (Nat.dvd_one.mp h4)
  let π : ↥L →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (r + 1) K :=
    eL.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := eL.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := CFSG.SectionRank.OddCover.ker_comp_mk'_center eL
  have hdim := two_pow_le_card_of_psln hW hp hK (by omega) π hπ hker.le (hker ▸ hzp)
  have hord := card_sup_le_of_psln hW hK (by omega) hperf hirr eL hEN hel
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  have harith := card_aut_psln_lt hp3 (by omega : 3 ≤ r + 1) q.exponent_pos
    (fun h => h31 ⟨by omega, h.2⟩) hZodd hzn
  have h2 := succ_le_two_pow_orderOf (p := q.p) hp
  have h4 := pow_le_two_pow_mul
    (N := (q.p ^ (q.exponent * (r + 1 - 1)) - 1) / (q.p - 1)) h2
  exact absurd ((hU1.trans hord).trans_lt (harith.trans_le (h4.trans hdim))) (lt_irrefl _)

theorem noFFModule_lie_A (d : ValidLieTypeIndex) {r : ℕ} {q : PrimePower} (hd : d.1 = .A r q)
    (hp : q.p ≠ 2) (hr : 2 ≤ r) (h31 : ¬ (r = 2 ∧ q.exponent = 1)) :
    NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_A hv hp hr h31)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
