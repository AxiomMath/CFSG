module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryAut
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

private theorem mulAut_congr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.conj_apply]

private theorem perfectInLayer_primeFormP_outer {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (β : MulAut (primeFormP h (idGram K n))) (hβ : β ^ p = 1)
    (hout : ∀ a : primeFormP h (idGram K n), MulAut.conj a ≠ β) : PerfectInLayer β := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  obtain ⟨-, -, -, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  by_cases hσ : primeFormFieldFactor h hC hn hq β = 1
  ·
    have hβD : β ∈ (primeFormFieldFactor h hC hn hq).ker := hσ
    rw [hkerD] at hβD
    obtain ⟨g, hg'⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_primeFormD h hn hq hp hg hβD hβ
    exact (hout g hg').elim
  ·
    have : Fact p.Prime := ⟨hp⟩
    have hne : β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have hord : orderOf β = p := orderOf_eq_prime hβ hne
    have hσp : orderOf (primeFormFieldFactor h hC hn hq β) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ, map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hq hp hp2
        β hord _ rfl hσp
    have hβeq : β = primeFormConjHom h _ M *
        primeFormFieldHom h hC (primeFormFieldFactor h hC hn hq β) *
        (primeFormConjHom h _ M)⁻¹ := by
      rw [← hM]
      group
    rw [hβeq]
    exact LieSemisimple.perfectInLayer_conj _ _
      (LieSemisimple.perfectInLayer_primeFormFieldHom h hn hp hp2 _ hσp)

theorem perfectInLayer_twistedA_outer (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  subst hpc
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hf0 : q.exponent ≠ 0 := by omega
  have hg : ¬ q.p ∣ Nat.gcd (r + 1) (q.p ^ q.exponent + 1) := by
    intro hd
    have h1 : q.p ∣ q.p ^ q.exponent + 1 := hd.trans (Nat.gcd_dvd_right _ _)
    have h2 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ hf0
    have h3 : q.p ∣ 1 := (Nat.dvd_add_right h2).mp h1
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
  refine LieSemisimple.perfectInLayer_of_congr e' β ?_
  have hβ' : MulAut.congr e' β ^ q.p = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : ∀ a : primeFormP h (idGram K (r + 1)), MulAut.conj a ≠ MulAut.congr e' β := by
    intro a ha
    apply hout (e'.symm a)
    apply (MulAut.congr e').injective
    rw [mulAut_congr_conj, e'.apply_symm_apply]
    exact ha
  exact perfectInLayer_primeFormP_outer h hn3 hq' hp hp2 hg _ hβ' hout'

end CFSG.HardMathSupport.Dickson.DefCharOuter
