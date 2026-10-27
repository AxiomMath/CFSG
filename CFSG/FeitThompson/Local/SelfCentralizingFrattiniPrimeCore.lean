module

public import CFSG.FeitThompson.Local.FrattiniQuotientAutomorphismKernelPGroup
public import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {p : ℕ}

theorem normal_map_subtype_frattini (V : Subgroup X) [V.Normal] :
    ((frattini ↥V).map V.subtype).Normal := inferInstance

theorem mem_map_subtype_frattini_iff {V : Subgroup X} {v : ↥V} :
    (v : X) ∈ (frattini ↥V).map V.subtype ↔ v ∈ frattini ↥V :=
  Subgroup.mem_map_iff_mem V.subtype_injective

theorem map_subtype_frattini_le (V : Subgroup X) : (frattini ↥V).map V.subtype ≤ V := by
  rw [Subgroup.map_le_iff_le_comap]
  intro x _
  simp

theorem mul_conj_inv_mem_map_subtype_frattini [Finite X] (hp : p.Prime) {V : Subgroup X}
    [V.Normal] (hV : IsPGroup p V) {x : X}
    (hx : x ∈ (pComplCore p (X ⧸ (frattini ↥V).map V.subtype)).comap
      (QuotientGroup.mk' ((frattini ↥V).map V.subtype)))
    {v : X} (hv : v ∈ V) : x * v * x⁻¹ * v⁻¹ ∈ (frattini ↥V).map V.subtype := by
  have : Fact p.Prime := ⟨hp⟩
  set F : Subgroup X := (frattini ↥V).map V.subtype with hF
  set π := QuotientGroup.mk' F with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective F
  have hVim : (V.map π).Normal := ‹V.Normal›.map π hsurj
  have hPG : IsPGroup p (V.map π) := hV.map π
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPG
  have hQ : ¬ p ∣ Nat.card (pComplCore p (X ⧸ F)) := not_dvd_natCard_pComplCore hp _
  have hcop : (Nat.card (pComplCore p (X ⧸ F))).Coprime (Nat.card (V.map π)) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ (hp.coprime_iff_not_dvd.2 hQ).symm
  have hcomm : Commute (π x) (π v) :=
    Subgroup.commute_of_normal_of_disjoint _ _ (pComplCore_normal p _) hVim
      (Subgroup.disjoint_of_coprime_natCard hcop) _ _ (Subgroup.mem_comap.1 hx)
      (Subgroup.mem_map_of_mem π hv)
  have h1 : π (x * v * x⁻¹ * v⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm.eq]
    group
  simpa [hπ, QuotientGroup.mk'_apply] using (QuotientGroup.eq_one_iff _).1 h1

theorem mem_of_mem_comap_pComplCore_of_coprime [Finite X] (hp : p.Prime) {V : Subgroup X}
    [V.Normal] (hV : IsPGroup p V) (hC : Subgroup.centralizer (V : Set X) ≤ V) {x : X}
    (hx : x ∈ (pComplCore p (X ⧸ (frattini ↥V).map V.subtype)).comap
      (QuotientGroup.mk' ((frattini ↥V).map V.subtype)))
    (hcop : (orderOf x).Coprime (Nat.card ↥V)) : x ∈ V := by
  have : Fact p.Prime := ⟨hp⟩
  have hnil := hV.isNilpotent
  have hsolv : Group.IsSolvable ↥V := inferInstance
  set a : MulAut ↥V := MulAut.conjNormal x with ha'
  have ha : a ∈ autKerFrattini ↥V := by
    rw [mem_autKerFrattini]
    intro v
    rw [QuotientGroup.eq, ← mem_map_subtype_frattini_iff]
    have key := mul_conj_inv_mem_map_subtype_frattini hp hV hx (V.inv_mem v.2)
    have hcoe : (((a v)⁻¹ * v : ↥V) : X) = x * (v : X)⁻¹ * x⁻¹ * ((v : X)⁻¹)⁻¹ := by
      push_cast [ha', MulAut.conjNormal_apply]
      group
    rw [hcoe]
    exact key
  have hdvd : orderOf a ∣ orderOf x := orderOf_map_dvd MulAut.conjNormal x
  have h1 : a = 1 :=
    eq_one_of_mem_autKerFrattini_of_coprime ha (hcop.coprime_dvd_left hdvd)
  refine hC (Subgroup.mem_centralizer_iff.2 fun v hv => ?_)
  have hxv := congrArg (fun (b : MulAut ↥V) => (b ⟨v, hv⟩ : X)) h1
  simp only [ha', MulAut.conjNormal_apply, MulAut.one_apply] at hxv
  exact (mul_inv_eq_iff_eq_mul.1 hxv).symm

theorem isPGroup_comap_pComplCore [Finite X] (hp : p.Prime) {V : Subgroup X}
    [V.Normal] (hV : IsPGroup p V) (hC : Subgroup.centralizer (V : Set X) ≤ V) :
    IsPGroup p ((pComplCore p (X ⧸ (frattini ↥V).map V.subtype)).comap
      (QuotientGroup.mk' ((frattini ↥V).map V.subtype))) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [isPGroup_iff_primeFactors_card_subset hp.ne_zero, hp.primeFactors]
  intro q hq
  rw [Finset.mem_singleton]
  by_contra hqp
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' q (Nat.dvd_of_mem_primeFactors hq)
  have hborder : orderOf (b : X) = q := by rw [Subgroup.orderOf_coe]; exact hb
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hV
  have hcop : (orderOf (b : X)).Coprime (Nat.card ↥V) := by
    rw [hborder, hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hqprime hp).2 hqp)
  have hbV : (b : X) ∈ V := mem_of_mem_comap_pComplCore_of_coprime hp hV hC b.2 hcop
  have hdvd : orderOf (b : X) ∣ Nat.card ↥V := by
    have h := orderOf_dvd_natCard (⟨(b : X), hbV⟩ : ↥V)
    rwa [← Subgroup.orderOf_coe (⟨(b : X), hbV⟩ : ↥V)] at h
  have hq1 := hcop.eq_one_of_dvd hdvd
  rw [hborder] at hq1
  exact hqprime.one_lt.ne' hq1

theorem pComplCore_quotient_map_subtype_frattini_eq_bot [Finite X] (hp : p.Prime) {V : Subgroup X}
    [V.Normal] (hV : IsPGroup p V) (hC : Subgroup.centralizer (V : Set X) ≤ V) :
    pComplCore p (X ⧸ (frattini ↥V).map V.subtype) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set F : Subgroup X := (frattini ↥V).map V.subtype with hF
  set π := QuotientGroup.mk' F with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective F
  have hmap : ((pComplCore p (X ⧸ F)).comap π).map π = pComplCore p (X ⧸ F) :=
    Subgroup.map_comap_eq_self_of_surjective hsurj _
  have hPG : IsPGroup p (pComplCore p (X ⧸ F)) :=
    hmap ▸ (isPGroup_comap_pComplCore hp hV hC).map π
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hPG
  have hnd : ¬ p ∣ Nat.card (pComplCore p (X ⧸ F)) := not_dvd_natCard_pComplCore hp _
  rw [← Subgroup.card_eq_one, hm]
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [h, pow_zero]
  · exact absurd (hm ▸ dvd_pow_self p h.ne') hnd

end

end CFSG.FeitThompson
