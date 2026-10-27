module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.Coordinator

private theorem exists_fixed_embedding_primeForm {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) {n p : ℕ} (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    (β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))
    (hβord : orderOf β = p) (σ : F ≃+* F) (hσord : orderOf σ = p)
    (hβσ : primeFormFieldFactor h isPrimeFormGram_one hn hne β = σ) :
    p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ℓ),
      Nat.card k = (ℓ ^ (f / p)) ^ 2 ∧
      ∃ ι : StatedProj (StatedSU n (ℓ ^ (f / p)) k) →* primeFormP h 1,
        Function.Injective ι ∧ ∀ y, β (ι y) = ι y := by
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hdiv
  obtain ⟨hpf, hcardfix, -, -, -, hinj, hrange, -, -, -, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσord n hn hne hZ
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne hp hp2 β hβord σ hβσ hσord
  set u := primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  have hβup : ∀ x, β (u x) = u (fσ x) := fun x => by
    have := congrArg (fun g : MulAut (primeFormP h
      ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) => g x) hβu
    simpa using this
  let h₀ : UnitaryFieldData ℓ (f / p) (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h hp hp2 hσord
  let θ₀ : StatedProj (StatedSU n (ℓ ^ (f / p)) (fixSubfield σ)) ≃* primeFormP h₀ 1 :=
    (unitaryPSUEquiv h₀ (by omega)).symm.trans
      (Classical.choice (nonempty_primeFormP_mulEquiv h₀ (isPrimeFormGram_one))).symm
  let j : primeFormP h₀ 1 →* primeFormP h 1 := primeSubfieldPSU h hp hp2 hσord n
  refine ⟨hpf, fixSubfield σ, inferInstance, h₀.finite, h₀.charP, hcardfix, ?_⟩
  refine ⟨u.toMonoidHom.comp (j.comp θ₀.toMonoidHom), ?_, ?_⟩
  · intro x y hxy
    exact θ₀.injective (hinj (u.injective hxy))
  · intro y
    have hmem : j (θ₀ y) ∈ fieldFixedPSU h n σ := by
      rw [← hrange]
      exact ⟨θ₀ y, rfl⟩
    have hfixj : fσ (j (θ₀ y)) = j (θ₀ y) := hmem
    have hfixu : β (u (j (θ₀ y))) = u (j (θ₀ y)) := by rw [hβup, hfixj]
    change β (u (j (θ₀ y))) = u (j (θ₀ y))
    exact hfixu

theorem psu_prime_outer_fixed_subfield_embedding {K : Type} [Group K] {n ℓ f : ℕ}
    (hcl : StatedClassicalModel K .PSU n ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) (α : MulAut K) (hαp : α ^ p = 1)
    (hαin : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ℓ),
      Nat.card k = (ℓ ^ (f / p)) ^ 2 ∧
      ∃ ι : StatedProj (StatedSU n (ℓ ^ (f / p)) k) →* K, Function.Injective ι ∧
        ∀ y, α (ι y) = ι y := by
  obtain ⟨⟨hℓ, hf, hn, hne⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hne' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) F) := isPrimeFormGram_one
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    ⟨(e.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  set β := MulAut.congr θ α with hβdef
  have hβθ : ∀ x : K, β (θ x) = θ (α x) := fun x => by
    simp [hβdef, MulAut.congr_apply]
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ inner (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
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
  obtain ⟨hpf, k, hkField, hkFin, hkChar, hkcard, ι, hinjι, hfixι⟩ :=
    exists_fixed_embedding_primeForm h hn hne' hp hp2 hdiv β hβord σ hσord hσdef.symm
  refine ⟨hpf, k, hkField, hkFin, hkChar, hkcard, ?_⟩
  refine ⟨θ.symm.toMonoidHom.comp ι, ?_, ?_⟩
  · intro x y hxy
    exact hinjι (θ.symm.injective hxy)
  · intro y
    have hfix : β (ι y) = ι y := hfixι y
    change α (θ.symm (ι y)) = θ.symm (ι y)
    apply θ.injective
    rw [MulEquiv.apply_symm_apply, ← hβθ (θ.symm (ι y)), MulEquiv.apply_symm_apply]
    exact hfix

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
