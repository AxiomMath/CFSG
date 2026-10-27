module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModelTwisted
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrderTwisted
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.TrialityDim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.TwistedArith
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcE

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedD4


theorem noIrrFFOffender_lie_trialityD4 {q : PrimePower}
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hp2 : q.p ≠ 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hcen, K, _, _, σ, hK, hσ, ⟨θ⟩⟩ :=
    exists_twistedGroup_model_of_lie_trialityD4 hq.1 hv hp2 e
  have hq2 : 2 ≤ q.p ^ q.exponent :=
    q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let π : ↥L →* ↥(twistedGroup σ) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hdim := two_pow_le_card_of_twistedGroupD4 hW hp2 hq2 hK σ hσ π hπ hkerπ.le
    (by rw [hkerπ, hcen, Subgroup.card_bot]; exact q.prime_p.not_dvd_one)
  have hord := card_sup_le_card_center_mul_card_mulAut hW hq hirr hEN hel
    (CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card hq2
      hK hσ) θ
  have hAut := card_mulAut_twistedGroup_le hp2 q.exponent_pos hK σ hσ
  have hsup : Nat.card ↥(L ⊔ E) ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 28 := by
    calc Nat.card ↥(L ⊔ E) ≤ Nat.card (Subgroup.center ↥L) *
          Nat.card (MulAut ↥(twistedGroup σ)) := hord
      _ ≤ 1 * (3 * q.exponent * (q.p ^ q.exponent) ^ 28) :=
          Nat.mul_le_mul (by rw [hcen, Subgroup.card_bot]) hAut
      _ ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 28 := by
          nlinarith [Nat.zero_le (q.exponent * (q.p ^ q.exponent) ^ 28)]
  have harith := card_aut_triality_lt hp2 q.exponent_pos
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_trialityD4 (d : ValidLieTypeIndex) {q : PrimePower}
    (hd : d.1 = .trialityD4 q) (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_trialityD4 hv hp2)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
