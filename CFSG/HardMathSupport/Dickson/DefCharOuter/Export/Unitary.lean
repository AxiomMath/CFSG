module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.UnitaryModel
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_conj_primeFormFieldHom_of_outer (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n)
    (hp2 : p ≠ 2) {β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hβ : orderOf β = p)
    (hout : β ∉ innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∃ (σ : K ≃+* K) (g : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      orderOf σ = p ∧ β = g * primeFormFieldHom h
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := n)) σ *
          g⁻¹ := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hf1 := h.one_le
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one
  have hq : ¬(n = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : p ∣ 2 := h2 ▸ dvd_pow_self p (by omega)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hg : ¬ p ∣ Nat.gcd n (p ^ f + 1) := by
    intro hd
    have h2 : p ∣ p ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ p ^ f := dvd_pow_self p (by omega)
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h3).1 h2))
  have hβp : β ^ p = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβ] at this
  obtain ⟨-, -, -, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  by_cases hσ : primeFormFieldFactor h hC hn hq β = 1
  · exfalso
    have hβD : β ∈ (primeFormFieldFactor h hC hn hq).ker := hσ
    rw [hkerD] at hβD
    obtain ⟨g, hg'⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn hq hp hg hβD hβp
    exact hout ⟨g, hg'⟩
  · have hσp : orderOf (primeFormFieldFactor h hC hn hq β) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβp, map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hq hp hp2
        β hβ _ rfl hσp
    refine ⟨primeFormFieldFactor h hC hn hq β, primeFormConjHom h _ M, hσp, ?_⟩
    rw [← hM]
    group

theorem outerCentData_primeFormP (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n) (hp2 : p ≠ 2)
    {β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hβ : orderOf β = p)
    (hout : β ∉ innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    OuterCentData p β := by
  haveI := h.finite
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv _ (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h n).toEquiv
  obtain ⟨σ, g, hσ, rfl⟩ := exists_conj_primeFormFieldHom_of_outer h hn hp2 hβ hout
  refine OuterCentData.of_conj h.prime g⁻¹ _ ?_
  have hf' : g⁻¹ * (g * primeFormFieldHom h
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := n)) σ * g⁻¹) *
        g⁻¹⁻¹ = primeFormFieldHom h
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := n)) σ := by
    group
  rw [hf']
  refine outerCentData_primeFormFieldHom h hn hp2 hσ ?_
  rintro ⟨a, ha⟩
  apply hout
  refine ⟨g a, ?_⟩
  rw [← CFSG.HardMathSupport.Dickson.I271.mulAut_mul_conj_mul_inv, ha]

end Unitary

theorem outerCentData_twistedA (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p = q.p) {β : MulAut S} (hβ : orderOf β = p) (hout : β ∉ innerAut S) :
    OuterCentData p β := by
  subst hpq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (n := r + 1) (K := K))
  let e' : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  refine OuterCentData.of_congr hp e' ?_
  refine outerCentData_primeFormP h hn3 hp2 ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact hβ
  · rintro ⟨g, hg⟩
    apply hout
    refine ⟨e'.symm g, ?_⟩
    apply (MulAut.congr e').injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e'.apply_symm_apply]
    exact hg

theorem carrier_twistedA (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) :
    Finite (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group ∧
      IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group ∧
      ∃ a b : (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group, a * b ≠ b * a := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  haveI := h.finite
  let e' : (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group ≃*
      primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h (r + 1))
  haveI : Finite (primeFormP h ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K)) :=
    Finite.of_equiv _ (CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h (r + 1)).toEquiv
  haveI := isSimpleGroup_primeFormP_one h hn3 hq'
  refine ⟨Finite.of_equiv _ e'.symm.toEquiv, e'.isSimpleGroup, ?_⟩
  have hnc := not_commute_primeFormP_one h hn3 hq'
  push Not at hnc
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e'.symm a, e'.symm b, fun hc => hab (by simpa using congrArg e' hc)⟩


end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
