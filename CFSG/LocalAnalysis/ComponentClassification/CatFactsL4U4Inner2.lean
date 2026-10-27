module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Inner

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] noncomputable def jbToK (hKa : conjugate h.K h.a = h.K) :
    ↥(GSLit.fixedLayer h.J h.B) →* OddBar h.K :=
  (QuotientGroup.mk' (pPrimeCore 2 h.K)).comp (Subgroup.inclusion (fixedLayer_le_K h hKa))

theorem jbToK_apply (hKa : conjugate h.K h.a = h.K) (j : ↥(GSLit.fixedLayer h.J h.B)) :
    jbToK h hKa j = QuotientGroup.mk ⟨(j : H), fixedLayer_le_K h hKa j.2⟩ := rfl

theorem range_jbToK (hKa : conjugate h.K h.a = h.K) : (jbToK h hKa).range = imJB h := by
  apply le_antisymm
  · rintro _ ⟨j, rfl⟩
    exact ⟨⟨j, fixedLayer_le_K h hKa j.2⟩, mem_subgroupOf.mpr j.2, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨⟨k, mem_subgroupOf.mp hk⟩, rfl⟩

theorem ker_jbToK_le (hKa : conjugate h.K h.a = h.K) :
    (jbToK h hKa).ker ≤ pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_pPrimeCore_of_normal
  set φ := jbToK h hKa
  let f : φ.ker →* pPrimeCore 2 h.K :=
    ((Subgroup.inclusion (fixedLayer_le_K h hKa)).comp φ.ker.subtype).codRestrict _ (by
      intro j
      have hj := j.2
      rw [MonoidHom.mem_ker, jbToK_apply, QuotientGroup.eq_one_iff] at hj
      exact hj)
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z : pPrimeCore 2 h.K => ((z : h.K) : H)) hxy
    exact Subtype.ext (Subtype.ext this)
  exact Nat.Coprime.coprime_dvd_right (card_dvd_of_injective f hf) pPrimeCore_coprime_card

theorem exists_oddBar_JB_equiv :
    ∃ e : ↥(GSLit.fixedLayer h.J h.B) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B) ≃* OddBar h.J,
      ∀ (t : ↥(GSLit.fixedLayer h.J h.B)) (ht : (t : H) ∈ h.J),
        e t = ((⟨(t : H), ht⟩ : h.J) : OddBar h.J) := by
  have hle : GSLit.fixedLayer h.J h.B ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore h.isQuasisimple_J h.B_le_coreActionKernel
    h.isPGroup_B).1
  exact (restriction_quotient_mulEquiv hle hsup).2

theorem card_oddBar_J_dvd (hKa : conjugate h.K h.a = h.K) :
    Nat.card (OddBar h.J) ∣ Nat.card (imJB h) := by
  obtain ⟨e, -⟩ := exists_oddBar_JB_equiv h
  rw [← Nat.card_congr e.toEquiv, ← range_jbToK h hKa,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (jbToK h hKa)).toEquiv]
  refine card_dvd_of_surjective (QuotientGroup.map _ _ (MonoidHom.id _) (ker_jbToK_le h hKa))
    fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk x, rfl⟩

theorem eq_one_of_central_sq (hKa : conjugate h.K h.a = h.K)
    (hZJ : center (OddBar h.J) = ⊥) {x : OddBar h.K} (hx : x ∈ imJB h)
    (hc : ∀ y ∈ imJB h, x * y = y * x) (h2 : x * x = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← range_jbToK h hKa] at hx hc
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨e, he⟩ := exists_oddBar_JB_equiv h
  set φ := jbToK h hKa with hφ
  have hcen : (QuotientGroup.mk j : ↥(GSLit.fixedLayer h.J h.B) ⧸
      pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) ∈ center _ := by
    rw [mem_center_iff]
    intro w
    obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective w
    have h1 : φ ((j' * j)⁻¹ * (j * j')) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hc (φ j') ⟨j', rfl⟩, inv_mul_cancel]
    have h3 := ker_jbToK_le h hKa (MonoidHom.mem_ker.mpr h1)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact h3
  have hcen' : e (QuotientGroup.mk j) ∈ center (OddBar h.J) := by
    rw [mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hcen) w']
  rw [hZJ, mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hcen'
  have hodd : Odd (orderOf j) := by
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))) :=
      pPrimeCore_coprime_card
    have h1 : orderOf j = orderOf (⟨j, hcen'⟩ : pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B)) :=
      Subgroup.orderOf_coe (⟨j, hcen'⟩ : pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))
    rw [h1]
    refine Odd.of_dvd_nat ?_ (orderOf_dvd_natCard _)
    rcases Nat.even_or_odd (Nat.card (pPrimeCore 2 ↥(GSLit.fixedLayer h.J h.B))) with he | ho
    · exact absurd (Nat.Coprime.coprime_dvd_right (even_iff_two_dvd.1 he) hcop) (by norm_num)
    · exact ho
  have hdvd : orderOf (φ j) ∣ orderOf j := orderOf_map_dvd φ j
  have h2' : orderOf (φ j) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have hodd' : Odd (orderOf (φ j)) := Odd.of_dvd_nat hodd hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 h2' with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · rw [h1] at hodd'
    exact absurd hodd' (by decide)

end CFSG.ComponentClassification.CatFactsL4U4
