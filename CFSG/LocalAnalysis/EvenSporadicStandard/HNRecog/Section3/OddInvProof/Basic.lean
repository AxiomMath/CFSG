module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInv_not_isConj {G : Type} [Group G] {a z : G} (hT : TableVFacts a z) :
    ¬ IsConj a z := by
  intro hac
  obtain ⟨c, hc⟩ := (hT.partition.orbit 0).nonempty
  have hc' : c ∈ orb2A a a := hc
  exact Set.disjoint_left.mp (hT.partition.disjoint 0 1 (by decide)) hc
    ⟨hc'.1, hac.symm.trans hc'.2⟩

theorem oddInv_sq_eq_one {G : Type} [Group G] {a z x : G} (h : IsF5Type a z)
    (hx : IsConj a x) : x ^ 2 = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  rw [← hc, conj_pow, ← h.orderOf_a, pow_orderOf_eq_one]
  simp

theorem oddInv_barOf_sq_eq_one {G : Type} [Group G] {z c : G} (hcz : c ∈ Gx z)
    (hc2 : c ^ 2 = 1) : (barOf z ⟨c, hcz⟩) ^ 2 = 1 := by
  have hc' : (⟨c, hcz⟩ : ↥(Gx z)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hc2
  change (QuotientGroup.mk (⟨c, hcz⟩ : ↥(Gx z))) ^ 2 = 1
  rw [← QuotientGroup.mk_pow, hc', QuotientGroup.mk_one]

theorem oddInv_orderOf_barOf {G : Type} [Group G] [Finite G] {z : G} (σ : ↥(Gx z))
    (hodd : Odd (orderOf (σ : G))) : orderOf (barOf z σ) = orderOf (σ : G) := by
  have hdvd : orderOf (barOf z σ) ∣ orderOf (σ : G) := by
    rw [Subgroup.orderOf_coe σ]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥(Gx z))) σ
  have hmemQ : (σ ^ orderOf (barOf z σ) : ↥(Gx z)) ∈ CFSG.pCore 2 ↥(Gx z) := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx z))).exists_orderOf_eq_pow
    ⟨σ ^ orderOf (barOf z σ), hmemQ⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj0 : j = 0 := by
    by_contra hjne
    have h2dvd : 2 ∣ 2 ^ j := dvd_pow_self 2 hjne
    have hdvd' : 2 ^ j ∣ orderOf (σ : G) := by
      rw [← hj, Subgroup.orderOf_coe σ]
      exact orderOf_pow_dvd _
    have h2n : 2 ∣ orderOf (σ : G) := h2dvd.trans hdvd'
    rcases hodd with ⟨k, hk⟩
    omega
  have hone : orderOf (σ ^ orderOf (barOf z σ)) = 1 := by
    rw [hj, hj0]
    norm_num
  have hpow1 : (σ ^ orderOf (barOf z σ) : ↥(Gx z)) = 1 :=
    orderOf_eq_one_iff.mp hone
  have hndvd : orderOf (σ : G) ∣ orderOf (barOf z σ) := by
    rw [Subgroup.orderOf_coe σ]
    exact orderOf_dvd_of_pow_eq_one hpow1
  exact Nat.dvd_antisymm hdvd hndvd

theorem oddInv_step_one {G : Type} [Group G] [Finite G] {a z x : G} (h : IsF5Type a z)
    (hF3 : Vert Fusion3Facts a z) (hCls : GzClassFacts a z) (hPar : ParityFacts a z)
    (hT5 : TableVFacts a z) (hx : IsConj a x) (haz : a ∈ Gx z) (hxz : x ∈ Gx z)
    (hodd : Odd (orderOf (a * x))) (hne : x ≠ a) :
    IsConj z (a * z) ∧ IsConj z (x * z) ∧ a ∉ Qz z ∧ x ∉ Qz z := by
  have ha2 : a ^ 2 = 1 := by
    rw [← h.orderOf_a]
    exact pow_orderOf_eq_one a
  have hz2 : z ^ 2 = 1 := by
    rw [← h.orderOf_z]
    exact pow_orderOf_eq_one z
  have haz_comm : a * z = z * a := (mem_Gx.mp haz).symm
  have haz2 : (a * z) ^ 2 = 1 := by
    rw [Commute.mul_pow haz_comm 2, ha2, hz2, mul_one]
  have ha_inv : a⁻¹ = a :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha2)
  have haz_ne : a * z ≠ 1 := by
    intro h1
    have h2 : a⁻¹ * (a * z) = a⁻¹ * 1 := by rw [h1]
    rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h2
    have hza : z = a := by rw [h2, ha_inv]
    exact oddInv_not_isConj hT5 (hza.symm ▸ IsConj.refl a)
  have haz_ord : orderOf (a * z) = 2 := orderOf_eq_prime haz2 haz_ne
  have hz_memGxy : z ∈ Gxy a x := by
    rw [mem_Gxy]
    exact ⟨mem_Gx.mpr haz_comm, mem_Gx.mpr ((mem_Gx.mp hxz).symm)⟩
  have hzaB : IsConj z (a * z) := by
    rcases hCls.inv_two (a * z) haz_ord with hazA | hazB
    · exfalso
      have hz_mem2AB : z ∈ orb2AB a z a := ⟨IsConj.refl z, hazA⟩
      obtain ⟨k, hk⟩ := hPar.two_power_of_2AB x z hx hz_mem2AB hz_memGxy
      have hk0 : k = 0 := by
        by_contra hkne
        have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hkne
        have h2ax : 2 ∣ orderOf (a * x) := by rw [hk]; exact h2dvd
        rcases hodd with ⟨l, hl⟩
        omega
      have hax1 : a * x = 1 := by
        apply orderOf_eq_one_iff.mp
        rw [hk, hk0]
        norm_num
      have h2 : a⁻¹ * (a * x) = a⁻¹ * 1 := by rw [hax1]
      rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h2
      have hxa : x = a := by rw [h2, ha_inv]
      exact hne hxa
    · exact hazB
  have hconj : IsConj (a * z) (x * z) := by
    by_contra hc
    have heven := hPar.even_of_not_conj x z hx h.orderOf_z hz_memGxy hc
    exact Nat.not_even_iff_odd.mpr hodd heven
  have hxzB : IsConj z (x * z) := hzaB.trans hconj
  have haQ : a ∉ Qz z :=
    (hF3.self.shape_2BB z ⟨IsConj.refl z, hzaB⟩).2
  have hxQ : x ∉ Qz z :=
    ((hF3 x z hx (IsConj.refl z)).shape_2BB z ⟨IsConj.refl z, hxzB⟩).2
  exact ⟨hzaB, hxzB, haQ, hxQ⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
