module

public import CFSG.HardMathSupport.Dickson.Bal207.UniOuter
import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Type

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

variable {f n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 f F}

theorem uni_outer_shape (hf : f = 1 ∨ f = 3) (hn : 4 ≤ n) (h3 : ¬ 3 ∣ n)
    (D : primeFormUnitary h (oneGram F n))
    (hD : ((D : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) (hD3 : D ^ 3 = 1)
    {τ : F ≃+* F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {L : Subgroup (primeFormP h (oneGram F n))}
    (hL : CFSG.Open.IsComponentOf L (fixSubgroup (primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl D * SemidirectProduct.inr τ)))) :
    L = fixSubgroup (primeFormPsi h uni_isPrimeFormGram_one
        (SemidirectProduct.inl D * SemidirectProduct.inr τ)) ∧
      Subgroup.center ↥L = ⊥ ∧
      ∃ (F₀ : Type) (_ : Field F₀) (k : ℕ) (h₀ : UnitaryFieldData 2 k F₀), k = 1 ∧
        Nonempty (↥L ≃* primeFormP h₀ (oneGram F₀ n)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hτo : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
  have hZ : ¬ 3 ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) n) := by
    rw [uni_normOneScalars_eq_bot h hf h3 (by omega), Subgroup.card_bot]
    norm_num
  obtain ⟨hpf, -, -, -, -, hinj, hrange, -, -, hsimp, -⟩ :=
    prime_subfield_fixed_group_package h Nat.prime_three (by norm_num) hτo n (by omega)
      (fun h' => absurd h'.1 (by omega)) hZ
  have hf3 : f = 3 := by
    rcases hf with rfl | rfl
    · norm_num at hpf
    · rfl
  obtain ⟨hS, -⟩ := hsimp (fun h' => absurd h'.1 (by omega))
  obtain ⟨M, hM⟩ := uni_exists_conj_inr D hD hD3 hτ3 hτo
  have hΨ : primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl D * SemidirectProduct.inr τ) =
        primeFormConjHom h (oneGram F n) M * primeFormFieldHom h uni_isPrimeFormGram_one τ *
          (primeFormConjHom h (oneGram F n) M)⁻¹ := by
    rw [hM, map_mul, map_mul, map_inv, uni_psi_inl, uni_psi_inr]
  have hC : fixSubgroup (primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl D * SemidirectProduct.inr τ)) =
        (fieldFixedPSU h n τ).map (primeFormConjHom h (oneGram F n) M).toMonoidHom := by
    rw [hΨ]
    exact uni_fixSubgroup_conj _ _
  rw [hC] at hL
  have hβi : Function.Injective (primeFormConjHom h (oneGram F n) M).toMonoidHom :=
    (primeFormConjHom h (oneGram F n) M).injective
  have hCs : IsSimpleGroup
      ↥((fieldFixedPSU h n τ).map (primeFormConjHom h (oneGram F n) M).toMonoidHom) :=
    (Subgroup.equivMapOfInjective (fieldFixedPSU h n τ) _ hβi).symm.isSimpleGroup
  have hLC : L = (fieldFixedPSU h n τ).map (primeFormConjHom h (oneGram F n) M).toMonoidHom := by
    rcases hL.2.1.eq_bot_or_eq_of_isSimpleGroup hCs with hb | he
    · haveI := excU62_nontrivial_of_isQuasisimple hL.2.2
      exact absurd hb ((Subgroup.nontrivial_iff_ne_bot L).1 inferInstance)
    · exact he
  have h₀ : UnitaryFieldData 2 (f / 3) (CFSG.LieType.Chevalley.fixSubfield τ) :=
    fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hτo
  let eL : ↥L ≃* primeFormP h₀ (oneGram (CFSG.LieType.Chevalley.fixSubfield τ) n) :=
    (MulEquiv.subgroupCongr hLC).trans
      ((Subgroup.equivMapOfInjective (fieldFixedPSU h n τ) _ hβi).symm.trans
        ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm)
  have hZL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have h1 : eL z ∈ Subgroup.center
        (primeFormP h₀ (oneGram (CFSG.LieType.Chevalley.fixSubfield τ) n)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := eL.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g']
    rw [uni_center_eq_bot h₀ (by omega) h3, Subgroup.mem_bot] at h1
    exact eL.injective (h1.trans (map_one eL).symm)
  refine ⟨hLC.trans hC.symm, hZL, CFSG.LieType.Chevalley.fixSubfield τ, inferInstance, f / 3, h₀,
    ?_, ⟨eL⟩⟩
  rw [hf3]

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
