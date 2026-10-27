module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.RankThree.PartTwo.KFacts

section Shell

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem t6psuh_noTorsion (h : UnitaryFieldData ℓ f K) (hdiv : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1)) :
    ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ 3 = 1 → c = 1 := by
  intro c hN hn h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : c ^ (ℓ ^ f + 1) = 1 := (pow_succ_eq_one_iff_norm h c).mpr hN
  by_contra hne
  have hord : orderOf c = 3 := orderOf_eq_prime h3 hne
  apply hdiv
  rw [← hord]
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hq)

theorem t6psuh_hZ3 (h : UnitaryFieldData ℓ f K) (hn : 1 ≤ n)
    (hdiv : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1)) :
    ∀ z ∈ (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)).ker, z ^ 3 = 1 →
      z = 1 := by
  intro z hz hz3
  rw [QuotientGroup.ker_mk'] at hz
  obtain ⟨c, hcN, hcn, hzc⟩ := hz
  have hc3 : c ^ 3 = 1 := by
    have h1 : ((z ^ 3 : gramSU h (idGram K n)) : GL (Fin n) K) = 1 := by
      rw [hz3]; rfl
    rw [Subgroup.coe_pow, hzc, ← map_pow] at h1
    exact (scalar_eq_one_iff hn).mp h1
  have hc1 : c = 1 := t6psuh_noTorsion h hdiv c hcN hcn hc3
  apply Subtype.ext
  rw [hzc, hc1, map_one]
  rfl

theorem s1431_false_psu_of_key (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hnq : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hℓ3 : ℓ ≠ 3) (hdiv : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1))
    {A : Subgroup (MulAut (primeFormP h (idGram K n)))} {ψ : MulAut (primeFormP h (idGram K n))}
    {J : Subgroup (primeFormP h (idGram K n))} {q : ℕ}
    (c : S1431Cfg (primeFormP h (idGram K n)) A ψ J q) (hA : ∀ a ∈ A, IsInnerAut a)
    (key : ∀ a : ↥(gramSU h (idGram K n)), a ^ 3 = 1 → ∀ i : PsuIdx h n a,
      IsTypeL2 q ↥(psuBlock h n a i) → ∀ b ∈ Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n))),
        b ^ 3 = 1 → ∃ s ∈ psuBlock h n a i, ∀ m ∈ psuBlock h n a i, b * m * b⁻¹ = s * m * s⁻¹) :
    False := by
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  haveI : Finite ↥(gramSU h (idGram K n)) := inferInstance
  haveI : Finite (primeFormP h (idGram K n)) := inferInstance
  refine s1431_false_of_lift_blocks (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    (QuotientGroup.mk'_surjective _) ?_ (t6psuh_hZ3 h (by omega) hdiv) ?_ c hA ?_
  · rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  · exact CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h
      (isPrimeFormGram_idGram (K := K) (n := n)) hn hnq
  · intro a ha3 _
    exact ⟨PsuIdx h n a, inferInstance, psuBlock h n a, psuBlock_le_centralizer a,
      psuBlock_normal a, isQuasisimple_psuBlock hℓ3 a ha3, t6psuh_derived hℓ3 a ha3,
      key a ha3⟩

end Shell

end CFSG.HardMathSupport.Dickson.Sec6.I1431
