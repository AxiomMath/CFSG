module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem jbToK_mem_imJB (j : ↥(GSLit.fixedLayer h.J h.B)) : jbToK h hKa j ∈ imJB h := by
  rw [← range_jbToK h hKa]
  exact ⟨j, rfl⟩

@[expose] noncomputable def jbOnto : ↥(GSLit.fixedLayer h.J h.B) →* ↥(imJB h) :=
  (jbToK h hKa).codRestrict (imJB h) (jbToK_mem_imJB hKa)

theorem coe_jbOnto (j : ↥(GSLit.fixedLayer h.J h.B)) :
    ((jbOnto hKa j : ↥(imJB h)) : OddBar h.K) = jbToK h hKa j := rfl

theorem jbOnto_surjective : Function.Surjective (jbOnto hKa) := by
  rintro ⟨x, hx⟩
  rw [← range_jbToK h hKa] at hx
  obtain ⟨j, rfl⟩ := hx
  exact ⟨j, rfl⟩

theorem ker_jbOnto_le : (jbOnto hKa).ker ≤ pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) := by
  intro j hj
  refine ker_jbToK_le h hKa ?_
  rw [MonoidHom.mem_ker] at hj ⊢
  rw [← coe_jbOnto, hj, Subgroup.coe_one]

theorem not_two_dvd_card_ker_jbOnto : ¬ 2 ∣ Nat.card (jbOnto hKa).ker := by
  intro h2
  have hdvd : Nat.card (jbOnto hKa).ker ∣
      Nat.card (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) :=
    Subgroup.card_dvd_of_le (ker_jbOnto_le hKa)
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥(GSLit.fixedLayer h.J h.B))
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop (h2.trans hdvd)

theorem comap_jbOnto_pPrimeCore :
    (pPrimeCore 2 ↥(imJB h)).comap (jbOnto hKa) = pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (prime_complement_kernel_core_preimage (jbOnto hKa) (jbOnto_surjective hKa)
    (not_two_dvd_card_ker_jbOnto hKa)).1

include hKa in
theorem center_quotient_imJB_eq_bot (hZJ : center (OddBar h.J) = ⊥) :
    center (↥(imJB h) ⧸ pPrimeCore 2 ↥(imJB h)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨j, rfl⟩ := jbOnto_surjective hKa x
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  have hcen : (QuotientGroup.mk j : ↥(GSLit.fixedLayer h.J h.B) ⧸
      pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) ∈ center _ := by
    rw [mem_center_iff]
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    have h1 : jbOnto hKa ((w * j)⁻¹ * (j * w)) ∈ pPrimeCore 2 ↥(imJB h) := by
      have h0 := mem_center_iff.mp hc (QuotientGroup.mk (jbOnto hKa w))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h0
      simpa only [map_mul, map_inv] using h0
    have h2 : (w * j)⁻¹ * (j * w) ∈ pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) := by
      rw [← comap_jbOnto_pPrimeCore hKa]
      exact h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact h2
  have hcen' : e (QuotientGroup.mk j) ∈ center (OddBar h.J) := by
    rw [mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hcen) w']
  rw [hZJ, mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff,
    ← comap_jbOnto_pPrimeCore hKa] at hcen'
  rw [mem_bot, QuotientGroup.eq_one_iff]
  exact hcen'

include hKa in
theorem exists_involution_imJB : ∃ x : ↥(imJB h), orderOf x = 2 := by
  obtain ⟨z, hzD, hzS, hz2⟩ := h.exists_involution_D_center
  have hzJB := mem_fixedLayer_of_mem_D h hzD hzS hz2
  obtain ⟨j, hjz⟩ : ∃ j : ↥(GSLit.fixedLayer h.J h.B), (j : H) = z := ⟨⟨z, hzJB⟩, rfl⟩
  have hj2 : orderOf j = 2 := by rw [← Subgroup.orderOf_coe, hjz]; exact hz2
  refine ⟨jbOnto hKa j, ?_⟩
  have hdvd : orderOf (jbOnto hKa j) ∣ 2 := by
    have h0 := orderOf_map_dvd (jbOnto hKa) j
    rw [hj2] at h0
    exact h0
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exfalso
    have hk : j ∈ (jbOnto hKa).ker := orderOf_eq_one_iff.mp h1
    have hO := ker_jbOnto_le hKa hk
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥(GSLit.fixedLayer h.J h.B))
    have h3 := orderOf_dvd_natCard (⟨j, hO⟩ : pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))
    rw [Subgroup.orderOf_mk, hj2] at h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop h3
  · exact h1

include hKa in
theorem exists_four_imJB (hZJ : center (OddBar h.J) = ⊥) :
    ∃ x y : ↥(imJB h), orderOf x = 2 ∧ orderOf y = 2 ∧ x * y = y * x ∧ x ≠ y := by
  by_contra hcon
  have hperf : Group.IsPerfect ↥(imJB h) := by
    rw [Group.isPerfect_def, _root_.commutator_def]
    apply map_injective (imJB h).subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, imJB_commutator_eq h hKa]
  have heven : Even (Nat.card ↥(imJB h)) := by
    obtain ⟨x, hx⟩ := exists_involution_imJB hKa
    have h0 := orderOf_dvd_natCard x
    rw [hx] at h0
    exact even_iff_two_dvd.mpr h0
  exact CatFactsSp4.center_quotient_ne_bot hperf heven
    (fun x y hx hy hxy hne => (hcon ⟨x, y, hx, hy, hxy, hne⟩).elim)
    (center_quotient_imJB_eq_bot hKa hZJ)

include hKa in
theorem not_mem_center_of_imJB (hZJ : center (OddBar h.J) = ⊥) {x : ↥(imJB h)}
    (hx : orderOf x = 2) : (x : OddBar h.K) ∉ center (OddBar h.K) := by
  intro hc
  have hx2 : (x : OddBar h.K) * x = 1 := by
    have h0 := pow_orderOf_eq_one x
    rw [hx, sq] at h0
    rw [← Subgroup.coe_mul, h0, Subgroup.coe_one]
  have h1 := eq_one_of_central_sq h hKa hZJ x.2 (fun y _ => (mem_center_iff.mp hc y).symm) hx2
  have h2 : x = 1 := Subtype.ext h1
  rw [h2, orderOf_one] at hx
  exact absurd hx (by norm_num)

end CFSG.ComponentClassification.GSThmB.Cov
