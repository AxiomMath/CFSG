module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcDim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcArith
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Unit

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SignalizerFunctorTheorem.NonLocalExc

theorem card_sup_le_card_center_mul_card_mulAut {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] [Finite S] (hS : Subgroup.center S = ⊥)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* S) :
    Nat.card ↥(L ⊔ E) ≤ Nat.card (Subgroup.center ↥L) * Nat.card (MulAut S) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hsup := FFToolkit.card_sup_le_of_outer hW hq.1 hirr hE hEel θ
    (k := Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    (fun B _ _ => card_le_card_outer_mul_card_inf B)
  have hL : Nat.card ↥L = Nat.card (Subgroup.center ↥L) * Nat.card S := by
    rw [← Nat.card_congr θ.toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_mulAut_eq_mul_card_outer hS]
  calc Nat.card ↥(L ⊔ E) ≤ _ := hsup
    _ = _ := by rw [hL]; ring

theorem noIrrFFOffender_lie_E6 {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid)
    (hp2 : q.p ≠ 2) : NoIrrFFOffender (CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hZp, hZ3, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_adjoint_model_of_lie_E6 hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2 e
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  let π : ↥L →* AdjointQuotient .E6 K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hdim := two_pow_le_card_of_adjointE (τ := .E6) (Or.inl rfl) hW hp2 π hπ hkerπ.le
    (by rw [hkerπ]; exact hZp)
  rw [card_heisS_E6, hK] at hdim
  have hord := card_sup_le_card_center_mul_card_mulAut hW hq hirr hEN hel
    (center_adjointQuotient_eq_bot .E6 K) θ
  have hAut := card_mulAut_adjointQuotient_E6_le K hK
  have hsup : Nat.card ↥(L ⊔ E) ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 78 := by
    rw [hK] at hAut
    calc Nat.card ↥(L ⊔ E) ≤ Nat.card (Subgroup.center ↥L) * Nat.card (MulAut (AdjointQuotient .E6 K)) := hord
      _ ≤ 3 * (6 * q.exponent * (q.p ^ q.exponent) ^ 78) := Nat.mul_le_mul (by omega) hAut
      _ ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 78 := by
          nlinarith [Nat.zero_le (q.exponent * (q.p ^ q.exponent) ^ 78)]
  have harith := card_aut_exc_lt hp2 q.exponent_pos (k := 10) (D := 78) (by norm_num) (by norm_num)
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_E6 (d : ValidLieTypeIndex) {q : PrimePower} (hd : d.1 = .E6 q)
    (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_E6 hv hp2)

theorem noIrrFFOffender_lie_E7 {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid)
    (hp2 : q.p ≠ 2) : NoIrrFFOffender (CFSGIndex.lie ⟨.E7 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hcen, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_adjoint_model_of_lie_E7 hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2 e
  have hZ3 : Nat.card (Subgroup.center ↥L) ≤ 1 := by rw [hcen, Subgroup.card_bot]
  have hZp : ¬ q.p ∣ Nat.card (Subgroup.center ↥L) := by
    rw [hcen, Subgroup.card_bot]
    exact q.prime_p.not_dvd_one
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  let π : ↥L →* AdjointQuotient .E7 K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hdim := two_pow_le_card_of_adjointE (τ := .E7) (Or.inr (Or.inl rfl)) hW hp2 π hπ hkerπ.le
    (by rw [hkerπ]; exact hZp)
  rw [card_heisS_E7, hK] at hdim
  have hord := card_sup_le_card_center_mul_card_mulAut hW hq hirr hEN hel
    (center_adjointQuotient_eq_bot .E7 K) θ
  have hAut := card_mulAut_adjointQuotient_E7_le K hK
  have hsup : Nat.card ↥(L ⊔ E) ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 133 := by
    rw [hK] at hAut
    calc Nat.card ↥(L ⊔ E) ≤ Nat.card (Subgroup.center ↥L) * Nat.card (MulAut (AdjointQuotient .E7 K)) := hord
      _ ≤ 3 * (2 * q.exponent * (q.p ^ q.exponent) ^ 133) := Nat.mul_le_mul (by omega) hAut
      _ ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 133 := by
          nlinarith [Nat.zero_le (q.exponent * (q.p ^ q.exponent) ^ 133)]
  have harith := card_aut_exc_lt hp2 q.exponent_pos (k := 16) (D := 133) (by norm_num) (by norm_num)
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_E7 (d : ValidLieTypeIndex) {q : PrimePower} (hd : d.1 = .E7 q)
    (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_E7 hv hp2)

theorem noIrrFFOffender_lie_E8 {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid)
    (hp2 : q.p ≠ 2) : NoIrrFFOffender (CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨hcen, K, _, _, hK, ⟨θ⟩⟩ :=
    exists_adjoint_model_of_lie_E8 hq.1 (FFToolkit.odd_card_center_of_isIrrOn hW hirr) hv hp2 e
  have hZ3 : Nat.card (Subgroup.center ↥L) ≤ 1 := by rw [hcen, Subgroup.card_bot]
  have hZp : ¬ q.p ∣ Nat.card (Subgroup.center ↥L) := by
    rw [hcen, Subgroup.card_bot]
    exact q.prime_p.not_dvd_one
  have : Fintype K := Fintype.ofFinite K
  have : CharP K q.p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  let π : ↥L →* AdjointQuotient .E8 K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerπ : π.ker = Subgroup.center ↥L := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, QuotientGroup.mk'_apply, map_eq_one_iff _ θ.injective,
      QuotientGroup.eq_one_iff]
  have hdim := two_pow_le_card_of_adjointE (τ := .E8) (Or.inr (Or.inr rfl)) hW hp2 π hπ hkerπ.le
    (by rw [hkerπ]; exact hZp)
  rw [card_heisS_E8, hK] at hdim
  have hord := card_sup_le_card_center_mul_card_mulAut hW hq hirr hEN hel
    (center_adjointQuotient_eq_bot .E8 K) θ
  have hAut := card_mulAut_adjointQuotient_E8_le K hK
  have hsup : Nat.card ↥(L ⊔ E) ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 248 := by
    rw [hK] at hAut
    calc Nat.card ↥(L ⊔ E) ≤ Nat.card (Subgroup.center ↥L) * Nat.card (MulAut (AdjointQuotient .E8 K)) := hord
      _ ≤ 3 * (1 * q.exponent * (q.p ^ q.exponent) ^ 248) :=
          Nat.mul_le_mul (by omega) (by simpa using hAut)
      _ ≤ 1024 * q.exponent * (q.p ^ q.exponent) ^ 248 := by
          nlinarith [Nat.zero_le (q.exponent * (q.p ^ q.exponent) ^ 248)]
  have harith := card_aut_exc_lt hp2 q.exponent_pos (k := 28) (D := 248) (by norm_num) (by norm_num)
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hsup).trans_lt (harith.trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_E8 (d : ValidLieTypeIndex) {q : PrimePower} (hd : d.1 = .E8 q)
    (hp2 : q.p ≠ 2) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_E8 hv hp2)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
