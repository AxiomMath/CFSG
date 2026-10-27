module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.ConnLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiveCore

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_W_out (H : GammaHyps a z) {t : G} (htz : t ∈ Gx z) (htQ : t ∉ Qz z)
    (ht : IsConj z t) : ∃ w : G, IsConj a w ∧ w ∈ Gx z ∧ w ∈ Gx t := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar H.h
  have ht2 : t ^ 2 = 1 := H.sq_z ht
  have htA : ¬ IsConj a t := fun hA => H.not_isConj_both hA ht
  have htz' : t * z = z * t := (mem_Gx.mp htz).symm
  have ht2' : (⟨t, htz⟩ : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ht2, Subgroup.coe_one]
  have hu2 : (barOf z ⟨t, htz⟩) ^ 2 = 1 := by
    change (QuotientGroup.mk (⟨t, htz⟩ : ↥(Gx z))) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, ht2', QuotientGroup.mk_one]
  have hu1 : barOf z ⟨t, htz⟩ ≠ 1 := by
    intro h1
    exact htQ ((barOf_eq_one_iff (z := z) ⟨t, htz⟩).mp h1)
  by_contra hno
  have hno' : ∀ w : G, IsConj a w → w ∈ Gx z → w ∈ Gx t → False := by
    intro w hw hwz hwt
    exact hno ⟨w, hw, hwz, hwt⟩
  have H0 : ∀ y' : G, IsConj a y' → ¬ (y' * z = z * y' ∧ y' * t = t * y') := by
    intro y' hy' hcomm
    exact hno' y' hy' (mem_Gx.mpr hcomm.1.symm) (mem_Gx.mpr hcomm.2.symm)
  have hdisj : barOf z ⟨t, htz⟩ ∉ _root_.commutator (Gbar z) ∨
      Nat.card ↥(CbarCent z ⟨t, htz⟩) = 32 := by
    rcases involution_cases_of_mulEquiv e hu2 hu1 with h1 | h2 | h3
    · exact Or.inl h1.1
    · exfalso
      exact (H.hNo.self).no_twoTwoA5
        ⟨⟨t, htz⟩, ht2, gz9_isShapeTwoTwoTimesA5_of_mulEquiv e h2.1 hu2 h2.2⟩
    · exact Or.inr h3.2
  obtain ⟨v, hv2, hv, hvnot⟩ :=
    exists_outer_involution_mul_of_mulEquiv e hu2 hu1 hdisj
  obtain ⟨y, hy, hyA, hybar⟩ := gamma_exists_lift H hv hv2
  have hyz : y * z = z * y := (mem_Gx.mp hy).symm
  obtain ⟨k, hk⟩ := exists_two_pow_orderOf_mul_of_no_two_A (x := t) (y := y)
    H.h H.hF1 H.hF2 H.hF3 ht2 htz' htA hyA hyz H0
  have hty : t * y ∈ Gx z := by
    rw [mem_Gx]
    calc z * (t * y) = (z * t) * y := (mul_assoc z t y).symm
      _ = (t * z) * y := by rw [mem_Gx.mp htz]
      _ = t * (z * y) := mul_assoc t z y
      _ = t * (y * z) := by rw [mem_Gx.mp hy]
      _ = (t * y) * z := (mul_assoc t y z).symm
  have hk' : orderOf ((⟨t, htz⟩ : ↥(Gx z)) * ⟨y, hy⟩) = 2 ^ k := by
    rw [show (⟨t, htz⟩ : ↥(Gx z)) * ⟨y, hy⟩ = ⟨t * y, hty⟩ from rfl,
      Subgroup.orderOf_mk, hk]
  have hdvd : orderOf (barOf z (⟨t, htz⟩ * ⟨y, hy⟩)) ∣ 2 ^ k := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z)))
      ((⟨t, htz⟩ : ↥(Gx z)) * ⟨y, hy⟩)
    rw [hk'] at h
    simpa only [QuotientGroup.mk'_apply] using h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have huv : barOf z (⟨t, htz⟩ * ⟨y, hy⟩) = barOf z ⟨t, htz⟩ * v := by
    calc barOf z (⟨t, htz⟩ * ⟨y, hy⟩) = barOf z ⟨t, htz⟩ * barOf z ⟨y, hy⟩ :=
          QuotientGroup.mk_mul (CFSG.pCore 2 ↥(Gx z)) ⟨t, htz⟩ ⟨y, hy⟩
      _ = barOf z ⟨t, htz⟩ * v := by rw [hybar]
  rw [huv] at hj
  exact hvnot j hj

end CFSG.EvenSporadicStandard.HNRecog.Section3
