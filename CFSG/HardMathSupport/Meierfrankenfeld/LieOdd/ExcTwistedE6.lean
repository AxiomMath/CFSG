module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModelTwisted
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrderTwisted
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.TwistedE6Dim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.TwistedArith
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcE

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_pow_ne_self_of_card {k : Type} [Field k] [Finite k] {q : ℕ} (hq : 2 ≤ q)
    (hk : Nat.card k = q ^ 2) (σ : k →+* k) (hσ : ∀ c, σ c = c ^ q) : ∃ u, σ u ≠ u := by
  by_contra hcon
  push Not at hcon
  have h1 := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_fixedSubfield_of_card σ hk hσ
  have h2 : CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.fixedSubfield σ = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact hcon c
  rw [h2] at h1
  have h3 : Nat.card (⊤ : Subfield k) = Nat.card k :=
    Nat.card_congr Subfield.topEquiv.toEquiv
  rw [h3, hk] at h1
  have h4 : q * q = q * 1 := by rw [← sq, h1, mul_one]
  have := Nat.eq_of_mul_eq_mul_left (by omega) h4
  omega


theorem noIrrFFOffender_lie_twistedE6 {q : PrimePower} (hv : (LieTypeIndex.twistedE6 q).Valid)
    (hp2 : q.p ≠ 2) : NoIrrFFOffender (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hZp, hZ3, k, _, _, σ, hk, hσ, ⟨θ⟩⟩ :=
    exists_graphFixed_model_of_lie_twistedE6 hq.1 hv hp2 e
  have hq2 : 2 ≤ q.p ^ q.exponent :=
    q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have : Fintype k := Fintype.ofFinite k
  have : CharP k q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hk, ← pow_mul])
  have hσ2 : ∀ c, σ (σ c) = c :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.theta_theta_of_card hk hσ
  have hne := exists_pow_ne_self_of_card hq2 hk σ hσ
  let π : ↥L →* ↥(graphFixedRootGroup TwistTag.E6 k σ) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hdim := two_pow_le_card_of_graphFixedE6 hW hp2 σ hσ2 hne π hπ hkerπ.le
    (by rw [hkerπ]; exact hZp)
  rw [hk, ← pow_mul, show (2 : ℕ) * 3 = 6 from rfl] at hdim
  have hord := card_sup_le_card_center_mul_card_mulAut hW hq hirr hEN hel
    (center_graphFixedRootGroup_E6_eq_bot σ) θ
  have hAut := card_mulAut_graphFixedE6_le hp2 q.exponent_pos hk σ hσ
  have hsup : Nat.card ↥(L ⊔ E) ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 78 := by
    calc Nat.card ↥(L ⊔ E) ≤ Nat.card (Subgroup.center ↥L) *
          Nat.card (MulAut ↥(graphFixedRootGroup TwistTag.E6 k σ)) := hord
      _ ≤ 3 * (324 * q.exponent * (q.p ^ q.exponent) ^ 78) := Nat.mul_le_mul hZ3 hAut
      _ ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 78 := by
          nlinarith [Nat.zero_le (q.exponent * (q.p ^ q.exponent) ^ 78)]
  have harith := card_aut_twistedE6_lt hp2 q.exponent_pos
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_twistedE6 (d : ValidLieTypeIndex) {q : PrimePower}
    (hd : d.1 = .twistedE6 q) (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_twistedE6 hv hp2)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
