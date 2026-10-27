module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator

theorem card_fixed_PSU {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSU n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ f₀ : ℕ, f = p * f₀ ∧
      lieOrderNumerator .PSU n (ℓ ^ f₀) =
        Nat.gcd n (ℓ ^ f₀ + 1) * Nat.card (fixedSubgroup α) := by
  classical
  obtain ⟨⟨hℓ, hf, hn, hne⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hne' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    ⟨(e.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  rw [← card_fixedSubgroup_congr θ α]
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  set σ := primeFormFieldFactor h hC1 hn hne' β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hD : β ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← ker_primeFormFieldFactor h hC1 hn hne']
      exact hσ1
    exact hβout (mem_inner_of_mem_primeFormD h hn hne' hp hdiv hD hβp)
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne' hp hp2 β hβord σ hσdef.symm hσord
  set u := primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup fσ) :=
    (card_fixedSubgroup_eq_of_intertwine (u : _ ≃* _) fσ β fun x => by
      exact congrArg (fun g : MulAut _ => g x) hβu).symm
  have hZ' : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hdiv
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -, -, -, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσord n hn hne' hZ'
  have hcard2 : Nat.card (fixedSubgroup fσ) =
      Nat.card (primeFormP (fixSubfield_unitaryFieldData h hp hp2 hσord)
        ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ))) := by
    rw [show fixedSubgroup fσ = fieldFixedPSU h n σ from rfl, ← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hcard1, hcard2, mul_comm]
  exact (card_primeFormP_one_mul_gcd (fixSubfield_unitaryFieldData h hp hp2 hσord)
    (by omega)).symm

theorem fixedLowerBoundAt_PSU : FixedLowerBoundAt .PSU := by
  intro K _ _ n ℓ f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf α hαp hαin
  have hcl : StatedClassicalModel K .PSU n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hp2 : p ≠ 2 := by omega
  have hdiv' : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := hdiv
  have hpos : 0 < p := hp.pos
  obtain ⟨f₁, hf₁, heq⟩ := card_fixed_PSU hcl hp hp2 hdiv' α hαp hαin
  have : f₁ = f₀ := by
    have := hf.symm.trans hf₁
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  subst this
  exact dvd_of_eq heq

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
