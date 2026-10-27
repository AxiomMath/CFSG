module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5aSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenInvolutionLifts

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.OuterAutomorphisms

variable {f : ℕ} {K : Type} [Field K]

theorem exists_fieldFactor_hom (hf : 2 ≤ f) (h : UnitaryFieldData 2 f K) :
    ∃ Ψ : MulAut (unitaryPSU h 3) →* (K ≃+* K), ∀ β : MulAut (unitaryPSU h 3),
      Ψ β = 1 → β * β = 1 → β ∈ inner (unitaryPSU h 3) := by
  have hq : ¬((3 : ℕ) = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one'
  obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv h hC
  refine ⟨(primeFormFieldFactor h hC (by norm_num) hq).comp (MulAut.congr e).symm.toMonoidHom, ?_⟩
  intro β hΨ hβ2
  set β' : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    (MulAut.congr e).symm β with hβ'
  have hββ' : MulAut.congr e β' = β := (MulAut.congr e).apply_symm_apply β
  have hker : β' ∈ (primeFormFieldFactor h hC (by norm_num) hq).ker := hΨ
  rw [ker_primeFormFieldFactor] at hker
  have hβ'2 : β' * β' = 1 := by
    have : (MulAut.congr e).symm (β * β) = 1 := by rw [hβ2, map_one]
    rw [map_mul] at this
    exact this
  by_cases hβ1 : β' = 1
  · rw [← hββ', hβ1, map_one]; exact one_mem _
  · have hord : orderOf β' = 2 := orderOf_eq_prime (by rw [sq]; exact hβ'2) hβ1
    obtain ⟨-, -, -, hinn⟩ := even_unitary_involution_matrix_lifts h hC (by norm_num) hq β' hord
    obtain ⟨x, hx⟩ := hinn β' hker hord
    refine ⟨e x, ?_⟩
    rw [← hββ', ← hx, congr_conj]

theorem isCyclic_ringEquiv [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] : IsCyclic (K ≃+* K) := by
  have : Algebra (ZMod p) K := ZMod.algebra K p
  have : IsCyclic (K ≃ₐ[ZMod p] K) := FiniteField.instIsCyclicAlgEquivOfFinite (ZMod p) K
  let ψ : (K ≃ₐ[ZMod p] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine isCyclic_of_surjective ψ fun σ => ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => ?_, rfl⟩
  have := RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K)
  exact congrArg (fun g : ZMod p →+* K => g x) this

theorem card_le_two_of_sq_eq_one [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (E : Subgroup (K ≃+* K)) (hE : ∀ a ∈ E, a ^ 2 = 1) : Nat.card E ≤ 2 := by
  classical
  have : IsCyclic (K ≃+* K) := isCyclic_ringEquiv (p := p)
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  have : Fintype (K ≃+* K) := Fintype.ofFinite _
  have h1 := IsCyclic.card_pow_eq_one_le (α := K ≃+* K) (n := 2) (by norm_num)
  calc Nat.card E = (Finset.univ.filter fun x : E => (x : K ≃+* K) ^ 2 = 1).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card, Finset.filter_true_of_mem]
        intro x _
        exact hE x x.2
    _ ≤ (Finset.univ.filter fun x : K ≃+* K => x ^ 2 = 1).card := by
        refine Finset.card_le_card_of_injOn (fun x => (x : K ≃+* K)) ?_ Subtype.val_injective.injOn
        intro x hx
        simpa using hx
    _ ≤ 2 := h1

end CFSG.QuasithinUnique.Setup.X5
