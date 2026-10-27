module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModelG2F4
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrderG2F4
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcF4Odd
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.G2Three
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.G2Arith
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcE

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem noIrrFFOffender_lie_G2 {q : PrimePower} (hv : (LieTypeIndex.G2 q).Valid)
    (hp2 : q.p ≠ 2) (h3 : q.card ≠ 3) : NoIrrFFOffender (CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have h5 : 5 ≤ q.card := by
    rw [hcard]
    exact five_le_of_odd_prime_pow q.prime_p hp2 q.exponent_pos (by rw [← hcard]; exact h3)
  obtain ⟨hcen, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_adjoint_model_of_lie_G2 hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2 h5 e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  let π : ↥L →* AdjointQuotient .G2 K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hker1 : Nat.card π.ker = 1 := by rw [hkerπ, hcen, Subgroup.card_bot]
  have hord := card_sup_le_card_center_mul_card_mulAut hW hq hirr hEN hel
    (center_adjointQuotient_eq_bot .G2 K) θ
  have hAut := card_mulAut_adjointQuotient_G2_le K hp2 hK
  have hsup : Nat.card ↥(L ⊔ E) ≤ 24 * q.exponent * (q.p ^ q.exponent) ^ 14 := by
    rw [hK] at hAut
    calc Nat.card ↥(L ⊔ E)
        ≤ Nat.card (Subgroup.center ↥L) * Nat.card (MulAut (AdjointQuotient .G2 K)) := hord
      _ ≤ 1 * (2 * q.exponent * (q.p ^ q.exponent) ^ 14) :=
          Nat.mul_le_mul (by rw [hcen, Subgroup.card_bot]) hAut
      _ ≤ 24 * q.exponent * (q.p ^ q.exponent) ^ 14 := by
          nlinarith [Nat.zero_le (q.exponent * (q.p ^ q.exponent) ^ 14)]
  by_cases hp3 : q.p = 3
  ·
    have he2 : 2 ≤ q.exponent := by
      by_contra hlt
      have he1 : q.exponent = 1 := by have := q.exponent_pos; omega
      exact h3 (by rw [hcard, hp3, he1]; norm_num)
    have : CharP K 3 := by rw [← hp3]; infer_instance
    have hdim := two_pow_le_card_of_adjointG2_three hW π hπ hkerπ.le
      (by rw [hker1]; norm_num)
    rw [hK, hp3] at hdim
    have harith := card_aut_g2_three_lt he2
    rw [hp3] at hsup
    by_contra hcon
    push Not at hcon
    have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
    exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)
  ·
    have hdim := two_pow_le_card_of_adjointG2 hW hp2 hp3 π hπ hkerπ.le
      (by rw [hker1]; exact q.prime_p.not_dvd_one)
    rw [hK] at hdim
    have harith := card_aut_g2_lt hp2 q.exponent_pos (by rw [← hcard]; exact h3)
    by_contra hcon
    push Not at hcon
    have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
    exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_G2 (d : ValidLieTypeIndex) {q : PrimePower} (hd : d.1 = .G2 q)
    (hp2 : q.p ≠ 2) (h3 : q.card ≠ 3) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_G2 hv hp2 h3)

theorem noIrrFFOffender_lie_F4 {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid)
    (hp2 : q.p ≠ 2) : NoIrrFFOffender (CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hcen, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_adjoint_model_of_lie_F4 hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2 e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  let π : ↥L →* AdjointQuotient .F4 K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hdim := two_pow_le_card_of_adjointF4_odd hW hp2 π hπ hkerπ.le
    (by rw [hkerπ, hcen, Subgroup.card_bot]; exact q.prime_p.not_dvd_one)
  rw [hK] at hdim
  have hord := card_sup_le_card_center_mul_card_mulAut hW hq hirr hEN hel
    (center_adjointQuotient_eq_bot .F4 K) θ
  have hAut := card_mulAut_adjointQuotient_F4_le K hp2 hK
  have hsup : Nat.card ↥(L ⊔ E) ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 52 := by
    rw [hK] at hAut
    calc Nat.card ↥(L ⊔ E)
        ≤ Nat.card (Subgroup.center ↥L) * Nat.card (MulAut (AdjointQuotient .F4 K)) := hord
      _ ≤ 1 * (q.exponent * (q.p ^ q.exponent) ^ 52) :=
          Nat.mul_le_mul (by rw [hcen, Subgroup.card_bot]) hAut
      _ ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 52 := by
          nlinarith [Nat.zero_le (q.exponent * (q.p ^ q.exponent) ^ 52)]
  have harith := card_aut_exc_lt hp2 q.exponent_pos (k := 7) (D := 52) (by norm_num) (by norm_num)
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_F4 (d : ValidLieTypeIndex) {q : PrimePower} (hd : d.1 = .F4 q)
    (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_F4 hv hp2)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
