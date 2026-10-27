module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410
public import CFSG.ClassicalInvolution.Asc77.AscT7HS1

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

theorem exists_frame_La_neg_one_eq {F V : Type} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) {x : spinGroup Q} (hxx : x * x = 1)
    (hdim : Module.finrank F (minusSp (spinAction Q x)) = 4) :
    ∃ fr : Frame Q, fr.La (-1) = spinAction Q x := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hiO : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q x)
  have hii : spinAction Q x * spinAction Q x = 1 := by rw [← map_mul, hxx, map_one]
  have hW : PolarNondegOn Q (minusSp (spinAction Q x)) := polarNondegOn_minusSp h2 hQ hiO hii
  have hQ' : (polarBilin (Q.restrict (minusSp (spinAction Q x)))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hW
  have hQ'' : (Q.restrict (minusSp (spinAction Q x))).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp hQ'
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨l, hlen, hlorth, hlne, hlspan, hldisc⟩ :=
    exists_orthogonal_list_restrict Q (minusSp (spinAction Q x)) hQ''
  obtain ⟨c, hc, -⟩ := spinLift_sq_and_norm hQnd hiO hii rfl hlorth
    ⟨2, by rw [hlen, hdim]⟩ hlspan hlne
  have hiso : ¬ (Q.restrict (minusSp (spinAction Q x))).Anisotropic := by
    rw [QuadraticMap.not_anisotropic_iff_exists]
    obtain ⟨v, hv0, hvQ⟩ := exists_isotropic_of_finrank_ge_three hodd
      (Q.restrict (minusSp (spinAction Q x))) hQ' (by omega)
    exact ⟨v, hv0, hvQ⟩
  have hP0 : (l.map Q).prod ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact zero_ne_one hc
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hc
    exact zero_ne_one hc
  have hdisc : TauCeti.RegularFormClass.discr
      (TauCeti.formClass (Q.restrict (minusSp (spinAction Q x))) hQ'') = 0 := by
    rw [hldisc (Units.mk0 _ hP0) rfl, TauCeti.squareClass_eq_zero_iff]
    refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), Units.ext ?_⟩
    simp only [Units.val_mk0, Units.val_mul]
    field_simp
    linear_combination hc
  obtain ⟨φ⟩ := hQ''.equivalent_hyperbolicPlane_prod_self hdim hdisc hiso
  obtain ⟨fr, hfr⟩ := Frame4.exists_frame_of_isometryEquiv (minusSp (spinAction Q x)) φ
  exact ⟨fr, La_neg_one_eq_of_span_eq h2 hii hiO fr hfr⟩

section Seven

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem finrank_quadOdd_three : Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]

omit [Finite K] in
theorem finrank_perp_frame_seven (fr : Frame (quadOdd 3 K)) : Module.finrank K fr.perp = 3 := by
  have h := finrank_perp_add_four fr
  rw [finrank_quadOdd_three] at h
  omega

theorem exists_conj_tSeven_eq_negOne_mul (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (hQ : quadOdd 3 K ≠ 0) :
    ∃ g : spinGroup (quadOdd 3 K),
      g * tSeven K * g⁻¹ = spinGroup.negOne (quadOdd 3 K) hQ * tSeven K := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ' : (polarBilin (quadOdd 3 K)).Nondegenerate := nondegenerate_polarBilin_quadOdd 3 K h2
  set F := (oddFrame 3 K).toHypFrame with hF
  have hswap : F.toFrame fin3_zero_ne_one true false = (frame01 K).swap :=
    toFrame_not F fin3_zero_ne_one true true
  obtain ⟨g, hg⟩ := exists_spin_conj hodd hQ' (frame01 K) (frame01 K).swap
    (by rw [finrank_perp_frame_seven]; omega)
  have hθ' : ∀ A, spinAction (quadOdd 3 K) (F.longSL2 fin3_zero_ne_one true false A) =
      (frame01 K).swap.La A := fun A => by
    rw [spinAction_longSL2, hswap]
  have hperf : ⁅(F.longSL2 fin3_zero_ne_one true true).range,
      (F.longSL2 fin3_zero_ne_one true true).range⁆ =
        (F.longSL2 fin3_zero_ne_one true true).range :=
    Subgroup.isPerfect_iff.mp (CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4
      (MonoidHom.ofInjective (longSL2_injective F fin3_zero_ne_one true true)).symm)
  set P := (F.longSL2 fin3_zero_ne_one true true).range.map (MulAut.conj g).toMonoidHom with hP
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← map_commutator, hperf]
  have hθP : P.map (spinAction (quadOdd 3 K)) = (frame01 K).swap.La.range := by
    rw [hP, map_conj_map, map_longSL2_range]
    exact (La_range_eq_map_conj hg).symm
  have hPJ' : P ≤ (F.longSL2 fin3_zero_ne_one true false).range :=
    le_of_le_comap_map (spinAction (quadOdd 3 K)) (ker_spinAction_le_center _) hPperf (by
      rw [map_longSL2_range, hswap, ← hθP]
      exact le_comap_map _ P)
  have htP : g * tSeven K * g⁻¹ ∈ P :=
    ⟨tSeven K, MonoidHom.mem_range.mpr ⟨-1, rfl⟩, rfl⟩
  obtain ⟨A, hA⟩ := hPJ' htP
  have hA1 : A = -1 := by
    apply (frame01 K).swap.La_injective
    rw [← hθ', hA, map_mul, map_mul, map_inv, spinAction_tSeven, ← hg (-1)]
  have h1 : F.longSL2 fin3_zero_ne_one true false (-1) =
      spinGroup.negOne (quadOdd 3 K) hQ * tSeven K :=
    longSL2_neg_one_not F fin3_zero_ne_one hQ true true
  rw [hA1, h1] at hA
  exact ⟨g, hA.symm⟩

theorem spinSeven_lemma410b (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    {x : spinGroup (quadOdd 3 K)} (hx : orderOf x = 2)
    (hxZ : x ∉ center (spinGroup (quadOdd 3 K))) :
    ∃ g : spinGroup (quadOdd 3 K), g * tSeven K * g⁻¹ = x := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hQ' : (polarBilin (quadOdd 3 K)).Nondegenerate := nondegenerate_polarBilin_quadOdd 3 K h2
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have : Group.IsPerfect (spinGroup (quadOdd 3 K)) := isPerfect_spinGroup_quadOdd h2 le_rfl
  have hdet := CFSG.ClassicalInvolution.Asc77.T7H.det_spinAction_eq_one x
  have h4dvd := CFSG.ClassicalInvolution.Asc77.T7H.four_dvd_finrank_minusSp_of_sq_one h2 hQ' hxx
    hdet
  have hne : spinAction (quadOdd 3 K) x ≠ 1 := fun h =>
    hxZ (by rw [center_spinGroup_quadOdd_eq_ker h2 le_rfl]; exact h)
  have hii : spinAction (quadOdd 3 K) x * spinAction (quadOdd 3 K) x = 1 := by
    rw [← map_mul, hxx, map_one]
  have ha0 : Module.finrank K (minusSp (spinAction (quadOdd 3 K) x)) ≠ 0 := by
    intro h0
    have hbot : minusSp (spinAction (quadOdd 3 K) x) = ⊥ := Submodule.finrank_eq_zero.mp h0
    refine hne (LinearEquiv.ext fun v => ?_)
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_eq h2 hii v
    have hw0 : w = 0 := by
      have : w ∈ (⊥ : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Unit → K)) := hbot ▸ hw
      exact (Submodule.mem_bot _).mp this
    rw [hw0, add_zero]
    exact mem_plusSp.mp hu
  have hle : Module.finrank K (minusSp (spinAction (quadOdd 3 K) x)) ≤ 7 :=
    finrank_quadOdd_three (K := K) ▸ Submodule.finrank_le _
  have hdim : Module.finrank K (minusSp (spinAction (quadOdd 3 K) x)) = 4 := by
    obtain ⟨k, hk⟩ := h4dvd
    omega
  obtain ⟨fr, hfr⟩ := exists_frame_La_neg_one_eq hodd hQ' hxx hdim
  obtain ⟨g, hg⟩ := exists_spin_conj hodd hQ' (frame01 K) fr
    (by rw [finrank_perp_frame_seven]; omega)
  have hθ : spinAction (quadOdd 3 K) (g * tSeven K * g⁻¹) = spinAction (quadOdd 3 K) x := by
    rw [map_mul, map_mul, map_inv, spinAction_tSeven, ← hg (-1), hfr]
  have hk : (g * tSeven K * g⁻¹)⁻¹ * x ∈ (spinAction (quadOdd 3 K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
  rcases (mem_ker_spinAction_iff _ (nondegenerate_quadOdd 3 K) _).mp hk with h | h
  · exact ⟨g, (inv_mul_eq_one.mp h)⟩
  · obtain ⟨g', hg'⟩ := exists_conj_tSeven_eq_negOne_mul hodd h4 hQ
    have hzc : spinGroup.negOne (quadOdd 3 K) hQ ∈ center (spinGroup (quadOdd 3 K)) := by
      rw [center_spinGroup_quadOdd h2 le_rfl]
      exact mem_zpowers _
    have hcz : ∀ a, a * spinGroup.negOne (quadOdd 3 K) hQ =
        spinGroup.negOne (quadOdd 3 K) hQ * a := fun a => mem_center_iff.mp hzc a
    have hx' : x = g * tSeven K * g⁻¹ * spinGroup.negOne (quadOdd 3 K) hQ := by
      rw [← h, mul_inv_cancel_left]
    refine ⟨g * g', ?_⟩
    calc g * g' * tSeven K * (g * g')⁻¹ = g * (g' * tSeven K * g'⁻¹) * g⁻¹ := by group
      _ = g * tSeven K * (spinGroup.negOne (quadOdd 3 K) hQ * g⁻¹) := by
          rw [hg', ← hcz (tSeven K)]
          group
      _ = x := by rw [← hcz g⁻¹, ← mul_assoc, ← hx']

end Seven

end CFSG.ComponentClassification.HarrisLit.T1
