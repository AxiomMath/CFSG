module

public import CFSG.Foundations.Basic
public import CFSG.CharacterTheory.Semidihedral.CentralHall
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual

public section

namespace CFSG.GroupTheory

open CFSG.ComponentClassification.CatalogueBPrimeJoin

variable {Q : Type*} [Group Q]

theorem le_pPrimeCore_of_normal {p : ℕ} {N : Subgroup Q} (hN : N.Normal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ CFSG.pPrimeCore p Q :=
  le_sSup ⟨hN, hcop⟩

theorem normal_of_le_center {N : Subgroup Q} (hN : N ≤ Subgroup.center Q) : N.Normal :=
  ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hN hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩

theorem commutator_mul_central_left {x y z : Q} (hz : z ∈ Subgroup.center Q) :
    x * z * y * (x * z)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have h : z * y * z⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.1 hz y, mul_inv_cancel_right]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem commutator_mul_central_right {x y z : Q} (hz : z ∈ Subgroup.center Q) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have h : z * x⁻¹ * z⁻¹ = x⁻¹ := by
    rw [← Subgroup.mem_center_iff.1 hz x⁻¹, mul_inv_cancel_right]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹ * z⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem prime_corefree_quasisimple_prime_generation [Finite Q] (hQ : IsQuasisimple Q) {p : ℕ}
    (hp : p.Prime) (hcore : CFSG.pPrimeCore p Q = ⊥) :
    p ∣ Nat.card (Q ⧸ Subgroup.center Q) ∧
      Subgroup.closure {x : Q | ∃ k : ℕ, orderOf x = p ^ k} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperf, hsimple, hnonab⟩ := hQ
  set Z := Subgroup.center Q with hZ
  have hZp : ∃ k : ℕ, Nat.card Z = p ^ k := by
    refine ⟨(Nat.card Z).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd
      Nat.card_pos.ne' fun {q} hq hqZ => ?_⟩
    by_contra hqp
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) q hqZ
    have hzle : Subgroup.zpowers (z : Q) ≤ Z := Subgroup.zpowers_le.2 z.2
    have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z : Q))) := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
      exact (Nat.coprime_primes hp hq).2 fun h => hqp h.symm
    have hle := le_pPrimeCore_of_normal (normal_of_le_center hzle) hcop
    rw [hcore, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    have h1 : orderOf z = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hle
    rw [hz] at h1
    exact hq.one_lt.ne' h1
  obtain ⟨k, hk⟩ := hZp
  have hdvd : p ∣ Nat.card (Q ⧸ Z) := by
    by_contra hndvd
    have hcop : (Nat.card Z).Coprime Z.index := by
      rw [hk]
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
    obtain ⟨K, hKchar, hKcard, -, hsup, -⟩ :=
      CFSG.Semidihedral.central_hall_subgroup_direct_complement Z le_rfl hcop
    have hKn : K.Normal := by
      have := hKchar
      infer_instance
    have hKle := le_pPrimeCore_of_normal (p := p) hKn (by
      rw [hKcard]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
    rw [hcore, le_bot_iff] at hKle
    rw [hKle, sup_bot_eq] at hsup
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ Z := hsup ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx y]
  refine ⟨hdvd, ?_⟩
  rw [← primeResidual_eq_closure]
  set R := primeResidual p Q with hR
  have hRZ : R.map (QuotientGroup.mk' Z) = ⊤ := by
    rw [primeResidual_map_surjective p _ (QuotientGroup.mk'_surjective Z)]
    have hnorm : (primeResidual p (Q ⧸ Z)).Normal := by
      have := primeResidual_characteristic p (Q ⧸ Z)
      infer_instance
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hnorm with h | h
    · exfalso
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Q ⧸ Z) p hdvd
      have hgmem : g ∈ primeResidual p (Q ⧸ Z) := by
        rw [primeResidual_eq_closure]
        exact Subgroup.subset_closure ⟨1, by rw [hg, pow_one]⟩
      rw [h, Subgroup.mem_bot] at hgmem
      rw [hgmem, orderOf_one] at hg
      exact hp.one_lt.ne hg
    · exact h
  have hcomm : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ R := by
    have hcover : ∀ x : Q, ∃ r ∈ R, ∃ z ∈ Z, x = r * z := by
      intro x
      have hx : QuotientGroup.mk' Z x ∈ R.map (QuotientGroup.mk' Z) := by
        rw [hRZ]
        exact Subgroup.mem_top _
      obtain ⟨r, hr, hrx⟩ := hx
      refine ⟨r, hr, r⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, hrx, inv_mul_cancel]
    intro x y
    obtain ⟨r, hr, z, hz, rfl⟩ := hcover x
    obtain ⟨r', hr', z', hz', rfl⟩ := hcover y
    rw [commutator_mul_central_left hz, commutator_mul_central_right hz']
    exact mul_mem (mul_mem (mul_mem hr hr') (inv_mem hr)) (inv_mem hr')
  rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_def,
    Subgroup.closure_le]
  rintro _ ⟨x, -, y, -, rfl⟩
  exact hcomm x y

end CFSG.GroupTheory
