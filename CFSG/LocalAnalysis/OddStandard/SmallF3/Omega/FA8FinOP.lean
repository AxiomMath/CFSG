module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Det
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W] [FiniteDimensional (ZMod 3) W]
  {R : QuadraticForm (ZMod 3) W}

private theorem fa8fin_h_rotation (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 2) (hs : quadSign R = -1) :
    ∃ p : OGroup R, p * p = piOrth R ∧ orderOf p = 4 ∧
      (QuadraticMap.orthogonalDet R).ker = Subgroup.zpowers p := by
  haveI : Finite (OGroup R) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have h2 : 2 ≤ Module.finrank (ZMod 3) W := by rw [hdim]
  have hpos : 0 < Module.finrank (ZMod 3) W := by rw [hdim]; norm_num
  have hEven : Even (Module.finrank (ZMod 3) W) := by rw [hdim]; exact ⟨1, rfl⟩
  have hsign : quadSign R = (-1 : ℤˣ) ^ (Module.finrank (ZMod 3) W / 2) := by
    rw [hdim, hs, show (2 : ℕ) / 2 = 1 by norm_num, pow_one]
  obtain ⟨p, hp⟩ := (exists_mul_self_eq_piOrth_iff hR).mpr ⟨hEven, hsign⟩
  have hdetp : QuadraticMap.orthogonalDet R p = 1 :=
    orthogonalDet_eq_one_of_mul_self_eq_piOrth hEven hp
  have hpi_ne : piOrth R ≠ 1 := piOrth_ne_one (Q := R) hpos
  have hp2 : p ^ 2 ≠ 1 := by
    rw [pow_two, hp]
    exact hpi_ne
  have hp4 : p ^ 4 = 1 := by
    have h : p ^ 4 = (p ^ 2) * (p ^ 2) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
    rw [h, pow_two, hp, piOrth_mul_self]
  have horder : orderOf p = 4 := by
    have h := orderOf_eq_prime_pow (x := p) (n := 1) (p := 2)
      (by simpa using hp2) (by simpa using hp4)
    simpa using h
  have hzp_card : Nat.card (Subgroup.zpowers p) = 4 := by
    rw [Nat.card_zpowers, horder]
  let K : Subgroup (OGroup R) := (QuadraticMap.orthogonalDet R).ker
  have hzp_le : Subgroup.zpowers p ≤ K := by
    rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.mpr hdetp
  obtain ⟨v, hv⟩ := exists_eq_unit_of_two_le_finrank (R := R) hR h2 (1 : (ZMod 3)ˣ)
  have hRv : R v ≠ 0 := by rw [hv]; exact one_ne_zero
  let _ : Invertible (R v) := invertibleOfNonzero hRv
  have hdet_refl : QuadraticMap.orthogonalDet R
      (TauCeti.QuadraticMap.reflectionOrthogonal R v) = -1 :=
    QuadraticMap.orthogonalDet_reflectionOrthogonal R v
  have hne_one : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
  have hKne : K ≠ ⊤ := by
    intro htop
    have hmem : TauCeti.QuadraticMap.reflectionOrthogonal R v ∈ K := by
      rw [htop]; exact Subgroup.mem_top _
    exact hne_one (hdet_refl ▸ MonoidHom.mem_ker.mp hmem)
  have hKdvd8 : Nat.card K ∣ 8 := by
    rw [← natCard_oGroup_two_minus (W := W) (R := R) hR hdim hs]
    exact Subgroup.card_subgroup_dvd_card K
  have hKdvd4 : 4 ∣ Nat.card K := by
    rw [← hzp_card]
    exact Subgroup.card_dvd_of_le hzp_le
  have hKpos : 0 < Nat.card K := by
    haveI : Nonempty ↥K := ⟨1, K.one_mem⟩
    exact Finite.card_pos_iff.mpr inferInstance
  have hKle8 : Nat.card K ≤ 8 := Nat.le_of_dvd (by norm_num) hKdvd8
  have hKge4 : 4 ≤ Nat.card K := Nat.le_of_dvd hKpos hKdvd4
  have hKne8 : Nat.card K ≠ 8 := by
    intro h8
    exact hKne (Subgroup.eq_top_of_card_eq (H := K)
      (by rw [h8, natCard_oGroup_two_minus (W := W) (R := R) hR hdim hs]))
  have hKcard : Nat.card K = 4 := by
    have hcases : Nat.card K = 4 ∨ Nat.card K = 5 ∨ Nat.card K = 6 ∨ Nat.card K = 7 ∨
        Nat.card K = 8 := by omega
    rcases hcases with h | h | h | h | h
    · exact h
    · rw [h] at hKdvd4; exact absurd hKdvd4 (by decide : ¬ (4 ∣ 5))
    · rw [h] at hKdvd4; exact absurd hKdvd4 (by decide : ¬ (4 ∣ 6))
    · rw [h] at hKdvd4; exact absurd hKdvd4 (by decide : ¬ (4 ∣ 7))
    · exact absurd h hKne8
  have hK_eq : K = Subgroup.zpowers p :=
    (Subgroup.eq_of_le_of_card_ge hzp_le (le_of_eq (hKcard.trans hzp_card.symm))).symm
  exact ⟨p, hp, horder, hK_eq⟩

theorem fa8fin_oGroup_two_minus_nonabelian (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 2) (hs : quadSign R = -1) :
    ∃ a b : OGroup R, a * b ≠ b * a := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) W := by rw [hdim]
  have hEven : Even (Module.finrank (ZMod 3) W) := by rw [hdim]; exact ⟨1, rfl⟩
  have hsign : quadSign R = (-1 : ℤˣ) ^ (Module.finrank (ZMod 3) W / 2) := by
    rw [hdim, hs, show (2 : ℕ) / 2 = 1 by norm_num, pow_one]
  obtain ⟨p, hp⟩ := (exists_mul_self_eq_piOrth_iff hR).mpr ⟨hEven, hsign⟩
  obtain ⟨v, hv⟩ := exists_eq_unit_of_two_le_finrank (R := R) hR h2 (1 : (ZMod 3)ˣ)
  have hRv : R v ≠ 0 := by rw [hv]; exact one_ne_zero
  let _ : Invertible (R v) := invertibleOfNonzero hRv
  let r : OGroup R := TauCeti.QuadraticMap.reflectionOrthogonal R v
  refine ⟨r, p, ?_⟩
  intro hcomm
  have hrcoe : (r : W ≃ₗ[ZMod 3] W) = TauCeti.QuadraticMap.reflection R v := by
    show (TauCeti.QuadraticMap.reflectionOrthogonal R v : W ≃ₗ[ZMod 3] W) =
      TauCeti.QuadraticMap.reflection R v
    rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  have hrv : (r : W ≃ₗ[ZMod 3] W) v = -v := by
    rw [hrcoe, TauCeti.QuadraticMap.reflection_apply_self]
  have h1 : (r : W ≃ₗ[ZMod 3] W) ((p : W ≃ₗ[ZMod 3] W) v) =
      (p : W ≃ₗ[ZMod 3] W) ((r : W ≃ₗ[ZMod 3] W) v) := by
    have hc := congrArg (fun e : OGroup R => (e : W ≃ₗ[ZMod 3] W) v) hcomm
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using hc
  have h1' : (r : W ≃ₗ[ZMod 3] W) ((p : W ≃ₗ[ZMod 3] W) v) =
      -((p : W ≃ₗ[ZMod 3] W) v) := by
    rw [h1, hrv, map_neg]
  let y : W := (p : W ≃ₗ[ZMod 3] W) v
  have hy : (r : W ≃ₗ[ZMod 3] W) y = -y := h1'
  have hrefl : TauCeti.QuadraticMap.reflection R v y = -y := by
    rw [← hrcoe]; exact hy
  let c : ZMod 3 := ⅟(R v) * QuadraticMap.polar R v y
  have h2 : TauCeti.QuadraticMap.reflection R v y = y - c • v := by
    rw [TauCeti.QuadraticMap.reflection_apply]
  have h4 : -y = y - c • v := by rw [← hrefl]; exact h2
  have h3 : (2 : ZMod 3) • y = c • v := by
    rw [two_smul]
    have h : (y - c • v) + y = 0 := by rw [← h4, neg_add_cancel]
    have h' : y + y - c • v = 0 := by rw [← h]; abel
    calc y + y = y + y - c • v + c • v := by abel
      _ = c • v := by rw [h', zero_add]
  let lam : ZMod 3 := 2 * c
  have hylam : y = lam • v := by
    have h := congrArg (fun z => (2 : ZMod 3) • z) h3
    rw [smul_smul, smul_smul] at h
    rw [show (2 : ZMod 3) * 2 = 1 by decide, one_smul] at h
    exact h
  have hp2v : (p : W ≃ₗ[ZMod 3] W) y = -v := by
    have h : ((p * p : OGroup R) : W ≃ₗ[ZMod 3] W) v = -v := by
      rw [hp, coe_piOrth_apply]
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply] at h
    simpa [y] using h
  have hp2v' : (p : W ≃ₗ[ZMod 3] W) y = (lam * lam) • v := by
    calc (p : W ≃ₗ[ZMod 3] W) y = (p : W ≃ₗ[ZMod 3] W) (lam • v) := by rw [hylam]
      _ = lam • (p : W ≃ₗ[ZMod 3] W) v := by rw [map_smul]
      _ = lam • y := rfl
      _ = lam • (lam • v) := by rw [hylam]
      _ = (lam * lam) • v := by rw [smul_smul]
  have hlam2 : (lam * lam) • v = (-1 : ZMod 3) • v := by
    rw [← hp2v', hp2v, neg_one_smul]
  have hzero : (lam * lam + 1) • v = 0 := by
    rw [add_smul, one_smul, hlam2, neg_one_smul, neg_add_cancel]
  have hv0 : v ≠ 0 := by
    intro h0
    have hz : R v = 0 := by rw [h0]; exact QuadraticMap.map_zero R
    rw [hv] at hz
    exact one_ne_zero hz
  have hlam : lam * lam + 1 = 0 := (smul_eq_zero.mp hzero).resolve_right hv0
  exact (by decide : ∀ l : ZMod 3, l * l + 1 ≠ 0) lam hlam

theorem fa8fin_oGroup_two_minus_det_sq (hR : R.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) W = 2) (hs : quadSign R = -1) {g : OGroup R}
    (hdet : QuadraticMap.orthogonalDet R g = 1) (hgg : g * g = 1) : g = 1 ∨ g = piOrth R := by
  obtain ⟨p, hp, horder, hK_eq⟩ := fa8fin_h_rotation hR hdim hs
  have hgmem : g ∈ (QuadraticMap.orthogonalDet R).ker := MonoidHom.mem_ker.mpr hdet
  rw [hK_eq] at hgmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgmem
  have hgg' : p ^ (k + k) = 1 := by
    rw [zpow_add, hk]
    exact hgg
  have h4dvd : (4 : ℤ) ∣ (k + k) := by
    have h := (orderOf_dvd_iff_zpow_eq_one (x := p)).mpr hgg'
    simpa [horder] using h
  obtain ⟨m, hm⟩ := h4dvd
  have hk2 : k = 2 * m := by omega
  have hgpi : g = (piOrth R) ^ m := by
    have hp2z : p ^ (2 : ℤ) = piOrth R := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hp]
    rw [← hk, hk2, zpow_mul, hp2z]
  have hpi2 : (piOrth R) ^ (2 : ℕ) = 1 := by rw [pow_two, piOrth_mul_self]
  rcases Int.emod_two_eq_zero_or_one m with hm0 | hm1
  · left
    calc g = (piOrth R) ^ m := hgpi
      _ = (piOrth R) ^ (m % (2 : ℤ)) := zpow_eq_zpow_emod' (x := piOrth R) m hpi2
      _ = 1 := by rw [show m % (2 : ℤ) = 0 by simpa using hm0, zpow_zero]
  · right
    calc g = (piOrth R) ^ m := hgpi
      _ = (piOrth R) ^ (m % (2 : ℤ)) := zpow_eq_zpow_emod' (x := piOrth R) m hpi2
      _ = piOrth R := by rw [show m % (2 : ℤ) = 1 by simpa using hm1, zpow_one]

end CFSG.OddStandard.SmallF3.Omega