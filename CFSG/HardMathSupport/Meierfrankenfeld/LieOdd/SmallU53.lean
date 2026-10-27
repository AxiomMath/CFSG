module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Small
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitDimFull

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Assembly.LowTwoRank

theorem noIrrFFOffender_smallU53 {q : PrimePower} (hv : (LieTypeIndex.twistedA 4 q).Valid)
    (h3 : q.card = 3) : NoIrrFFOffender (CFSGIndex.lie ⟨.twistedA 4 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp : q.p.Prime := q.prime_p
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hp3 : q.p = 3 := by
    have h1 : q.p ∣ 3 := by
      rw [← h3, hcard]; exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1
  have he1 : q.exponent = 1 := by
    have h1 : 3 ^ q.exponent = 3 ^ 1 := by rw [← hp3, ← hcard, h3, hp3]; rfl
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hp2 : q.p ≠ 2 := by rw [hp3]; norm_num
  obtain ⟨hZ, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_psu_model_of_lie_twistedA hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2
      (fun h => by omega) e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let π : ↥L →* StatedProj (StatedSU (4 + 1) (q.p ^ q.exponent) K) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hZ1 : Nat.card (Subgroup.center ↥L) = 1 := by
    have : Nat.gcd (4 + 1) (q.p ^ q.exponent + 1) = 1 := by
      rw [hp3, he1]; norm_num
    rw [this] at hZ
    exact Nat.dvd_one.1 hZ
  have hZp : ¬ q.p ∣ Nat.card π.ker := by
    rw [hkerπ, hZ1]
    exact fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  have hdim := two_pow_le_card_of_psun_full hW hp2 hK (by rw [he1]; exact odd_one) (by omega) π hπ
    hkerπ.le hZp
  have hord := card_sup_le_of_psu hW hq hirr hEN hel hp2 hK (n := 4 + 1) (by omega) θ
    (by rw [hZ1]; omega)
  have hpe : q.p ^ q.exponent = 3 := by rw [← hcard, h3]
  have h31 : q.p - 1 = 2 := by omega
  have hord2 : orderOf (2 : ZMod q.p) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · have h3z : ((3 : ℕ) : ZMod q.p) = 0 := (ZMod.natCast_eq_zero_iff 3 q.p).2 (by rw [hp3])
      have : (2 : ZMod q.p) ^ 2 = ((3 : ℕ) : ZMod q.p) + 1 := by push_cast; ring
      rw [this, h3z, zero_add]
    · intro h
      have : (1 : ZMod q.p) = 0 := by linear_combination h
      exact one_ne_zero this
  rw [hord2, hpe, h31] at hdim
  rw [hpe] at hord
  norm_num at hdim hord
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  have h54 : 4 * 5 * 3 ^ 24 < 2 ^ 54 := by norm_num
  omega

theorem smallU53 : SmallU53 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_smallU53 hv hq)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
